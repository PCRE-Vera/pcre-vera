import Pcrevera.Ref.Bytecode

/-!
# Bound arithmetic (BOUNDS.md sections 2, 3 and 5)

`engine/bounds.py`, restated: the part of the resource analysis the analyzer
and the checker are meant to have in common, and nothing more. A bound is
`base^n` times a polynomial in `n + 1`, held in a `Poly`, which is closed
under everything the composition rules do. Evaluation is counter arithmetic
with every step pre-checked, so saturation comes back as an explicit flag or
an ExceedsBudget `Bound` instead of being passed off as a maximum — a
coefficient that quietly stopped at the cap would be a requirement the
checker goes on to find satisfied.

Also here, because both halves read the tree the same way rather than as a
rule either states: the child lists of `region_kids`, built in one backwards
pass over the parent array.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- `sat_add`: one saturating counter step, the overflow flag threaded
through instead of being decided per step. -/
def satAdd (a b : Nat) (over : Bool) : Nat × Bool :=
  if a > counterMax - b then (counterMax, true) else (a + b, over)

/-- `sat_mul`, with the same pre-tested saturation point. -/
def satMul (a b : Nat) (over : Bool) : Nat × Bool :=
  if a = 0 ∨ b = 0 then (0, over)
  else if a > counterMax / b then (counterMax, true)
  else (a * b, over)

/-- The largest power of (n + 1) a bound may carry (spec.py's MAX_DEGREE). -/
def maxDegree : Nat := 4

/-- One bound: `base^n` times a polynomial in `n + 1`. -/
structure Poly where
  base : Nat
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
deriving DecidableEq, Repr, Inhabited

/-- The bound that is nothing at every length. -/
def Poly.zero : Poly := ⟨1, 0, 0, 0, 0, 0⟩

def Poly.const (c : Nat) : Poly := ⟨1, c, 0, 0, 0, 0⟩

/-- n + 1, which is what one more starting position costs. -/
def Poly.step : Poly := ⟨1, 0, 1, 0, 0, 0⟩

/-- All five coefficients zero. The base is deliberately not asked about,
which is what `polyNorm` relies on. -/
def Poly.nothing (p : Poly) : Bool :=
  p.c0 == 0 && p.c1 == 0 && p.c2 == 0 && p.c3 == 0 && p.c4 == 0

/-- This bound is one number, whatever the subject length. -/
def Poly.flat (p : Poly) : Bool :=
  p.base == 1 && p.c1 == 0 && p.c2 == 0 && p.c3 == 0 && p.c4 == 0

/-- This bound is at most c * (n + 1), which is BOUNDS.md section 6. -/
def Poly.linear (p : Poly) : Bool :=
  p.base == 1 && p.c2 == 0 && p.c3 == 0 && p.c4 == 0

/-- The coefficient at one degree; nothing ever asks past four. -/
def Poly.coef (p : Poly) : Nat → Nat
  | 0 => p.c0
  | 1 => p.c1
  | 2 => p.c2
  | 3 => p.c3
  | _ => p.c4

def Poly.setCoef (p : Poly) (degree value : Nat) : Poly :=
  match degree with
  | 0 => { p with c0 := value }
  | 1 => { p with c1 := value }
  | 2 => { p with c2 := value }
  | 3 => { p with c3 := value }
  | _ => { p with c4 := value }

/-- `poly_norm`: a bound worth nothing carries no growth either, so a claim
of one is not refused for naming a smaller base than a requirement that is
zero. -/
def polyNorm (p : Poly) : Poly :=
  if p.nothing then Poly.zero else p

/-- `poly_add`: coefficients added, the larger base kept. -/
def polyAdd (a b : Poly) (over : Bool) : Poly × Bool :=
  let base := if b.base > a.base then b.base else a.base
  let (c0, over) := satAdd a.c0 b.c0 over
  let (c1, over) := satAdd a.c1 b.c1 over
  let (c2, over) := satAdd a.c2 b.c2 over
  let (c3, over) := satAdd a.c3 b.c3 over
  let (c4, over) := satAdd a.c4 b.c4 over
  (polyNorm ⟨base, c0, c1, c2, c3, c4⟩, over)

/-- `poly_mul`: bases multiplied, coefficients convolved. A pair with a zero
on either side contributes nothing; a product above degree four has no field
to land in, and dropping it would be the one rounding that goes the wrong
way, so it raises the flag instead. -/
def polyMul (a b : Poly) (over : Bool) : Poly × Bool :=
  let (base, over) := satMul a.base b.base over
  let degrees := List.range (maxDegree + 1)
  let pairs := degrees.flatMap fun left => degrees.map fun right => (left, right)
  let (out, over) := pairs.foldl
    (fun st pair =>
      let (out, over) := st
      let (left, right) := pair
      if a.coef left ≠ 0 ∧ b.coef right ≠ 0 then
        if left + right > maxDegree then (out, true)
        else
          let (one, over) := satMul (a.coef left) (b.coef right) over
          let (running, over) := satAdd (out.coef (left + right)) one over
          (out.setCoef (left + right) running, over)
      else st)
    ({ Poly.zero with base := base }, over)
  (polyNorm out, over)

/-- `poly_ge`: domination coefficient by coefficient, base included. It is
sufficient rather than necessary — n^2 is above n and this says otherwise —
and that is the right way round for a checker. -/
def polyGe (a b : Poly) : Bool :=
  if a.base < b.base then false
  else if a.c0 < b.c0 then false
  else if a.c1 < b.c1 then false
  else if a.c2 < b.c2 then false
  else if a.c3 < b.c3 then false
  else if a.c4 < b.c4 then false
  else true

/-- `poly_eq`: structural equality, base and coefficient for coefficient.
Both sides only ever arrive normalized — the arithmetic runs `polyNorm` and
the decoders canonize — which is what lets the checker read it as value
equality; `polyEq_eq` in the proofs pins the structural reading down. -/
def polyEq (a b : Poly) : Bool :=
  if a.base ≠ b.base then false
  else if a.c0 ≠ b.c0 then false
  else if a.c1 ≠ b.c1 then false
  else if a.c2 ≠ b.c2 then false
  else if a.c3 ≠ b.c3 then false
  else if a.c4 ≠ b.c4 then false
  else true

/-- One evaluated bound. `ok = false` is ExceedsBudget, and the value then
says nothing. -/
structure Bound where
  ok : Bool
  value : Nat
deriving DecidableEq, Repr, Inhabited

def Bound.exceeds : Bound := ⟨false, 0⟩

def Bound.finite (value : Nat) : Bound := ⟨true, value⟩

/-- `bound_add`: saturation becomes ExceedsBudget rather than a maximum. -/
def boundAdd (a b : Bound) : Bound :=
  if !a.ok || !b.ok then Bound.exceeds
  else
    let (total, over) := satAdd a.value b.value false
    if over then Bound.exceeds else Bound.finite total

def boundMul (a b : Bound) : Bound :=
  if !a.ok || !b.ok then Bound.exceeds
  else
    let (total, over) := satMul a.value b.value false
    if over then Bound.exceeds else Bound.finite total

/-- The multiplication loop of `bound_pow`. Past the two degenerate bases the
running product at least doubles every time round, so `ok` goes false within
the 53 doublings a counter has room for; 55 units of fuel put the exhausted
branch, which hands back the accumulator as it stands, out of reach. -/
def boundPowGo (base exp : Nat) : Nat → Nat → Bound → Bound
  | 0, _, out => out
  | fuel + 1, i, out =>
      if i < exp ∧ out.ok then
        boundPowGo base exp fuel (i + 1) (boundMul out (Bound.finite base))
      else out

/-- `bound_pow`: `base^exp`, the degenerate bases answered before the loop
that they would otherwise keep from stopping. -/
def boundPow (base exp : Nat) : Bound :=
  if base = 1 then Bound.finite 1
  else if base = 0 then
    if exp = 0 then Bound.finite 1 else Bound.finite 0
  else boundPowGo base exp 55 0 (Bound.finite 1)

/-- `poly_value`: evaluate at one subject length. The powers are built up one
at a time and only spent where there is a coefficient to spend them on, so a
term that was never in the bound is not what refuses it. -/
def polyValue (p : Poly) (n : Nat) : Bound :=
  if p.nothing then Bound.finite 0
  else
    let rise := boundAdd (Bound.finite n) (Bound.finite 1)
    let raise := fun (spent : Bool) (c : Nat) (st : Bound × Bound) =>
      if spent then
        let power := boundMul st.1 rise
        let total :=
          if c ≠ 0 then boundAdd st.2 (boundMul (Bound.finite c) power)
          else st.2
        (power, total)
      else st
    let st := (Bound.finite 1, Bound.finite p.c0)
    let st := raise (p.c1 != 0 || p.c2 != 0 || p.c3 != 0 || p.c4 != 0) p.c1 st
    let st := raise (p.c2 != 0 || p.c3 != 0 || p.c4 != 0) p.c2 st
    let st := raise (p.c3 != 0 || p.c4 != 0) p.c3 st
    let st := raise (p.c4 != 0) p.c4 st
    boundMul (boundPow p.base n) st.2

/-- `growth_cap`: the growth schedule's final capacity for that many entries.
Nothing for none, else `GROW_MIN + GROW_FACTOR * entries` — what a doubling
run ends up holding, and therefore what a preallocated context reserves. -/
def growthCap (entries : Nat) (over : Bool) : Nat × Bool :=
  if entries > 0 then
    let (doubled, over) := satMul entries growFactor over
    satAdd doubled growMin over
  else (0, over)

/-- The backwards pass of `region_kids`: each child put at the front of a
sibling list that ends up in index order, which for a tree that passed the
sibling rule is code order. Every parent comes before its own child — both
callers settle that first — which is what makes one pass enough. -/
def regionKidsGo (regions : Array Region) :
    Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, kids, sibs => (kids, sibs)
  | i + 1, kids, sibs =>
      let parent := (regions[i + 1]!).parent
      let sibs := sibs.set! (i + 1) kids[parent]!
      let kids := kids.set! parent (i + 1)
      regionKidsGo regions i kids sibs

/-- `region_kids`: the children of every region, in the order their code
appears, read off the parent array. -/
def regionKids (regions : Array Region) : Array Nat × Array Nat :=
  let total := regions.size
  regionKidsGo regions (total - 1)
    (Array.replicate total none32) (Array.replicate total none32)

end Pcrevera.Ref
