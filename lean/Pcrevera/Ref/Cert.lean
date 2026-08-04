import Pcrevera.Ref.Poly
import Pcrevera.Ref.Compile

/-!
# The bound certificate: checker, analyzer, and the Pike closed form

The resource analysis of DESIGN.md section 5, transcribed whole: the checker
of `engine/certificate.py`, the analyzer of `engine/analyzer.py`, and the
Pike closed form from the end of `engine/pike.py`. The split survives the
transcription because it is the point of it. The analyzer searches for one
price per region of the compiler's tree and the checker decides whether to
believe it, and the two state the composition rules of BOUNDS.md twice on
purpose — one statement of the recurrence would make the checker's verdict a
restatement of the analyzer's own opinion. What they share is `Poly.lean`:
one arithmetic, one cost model.

Every function here mirrors its TIR original check for check and in the same
order, because these are the functions layer A proves sound and any daylight
between this file and the engine would surface as a proof about the wrong
program. Loops over the bytecode become recursion on the ground still to
cover; loops along a sibling chain become recursion on the region count that
bounds them. Everything is total, and every refusal is one named reason.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- The checker's verdicts (layout.py's `Cr`): one named reason per refusal,
because a rejection nobody can read is a rejection nobody will believe. -/
inductive Cr where
  | crNoRegions | crRootKind | crRootParent | crRootRange | crTwoRoots
  | crParentOrder | crBackwards | crNotNested | crOverlap | crNoRules
  | crConfig | crIneligible | crPrices | crBase | crOpcode | crShape
  | crChildren | crAmbiguous | crOverflow | crRegionWork | crRegionOuts
  | crRegionStack | crRegionTrail | crTotalCost | crTotalStack
  | crTotalTrail | crTotalMem | crNotLinear | crOk
deriving DecidableEq, Repr, Inhabited

/-- The analyzer's answers (`Ar`). `arAmbiguous` and `arOverflow` mean the
pattern honestly has no bound of the shape section 2 writes down; `arShape`
means the analyzer met something in the compiler's own tree it had no rule
for, which is a bug of ours and is reported as one. -/
inductive Ar where
  | arShape | arAmbiguous | arOverflow | arOk
deriving DecidableEq, Repr, Inhabited

/-- The matcher configurations a certificate can be about (`Cfg`). -/
inductive Cfg where
  | backtrack | pike | memo
deriving DecidableEq, Repr, Inhabited

/-- The complexity claim (`Cc`), the one field of a certificate that is not
a number. -/
inductive Cc where
  | notProvenLinear | linear
deriving DecidableEq, Repr, Inhabited

/-- Which of a certificate's whole-call bounds is being asked for (`Bk`). -/
inductive Bk where
  | cost | stack | mem
deriving DecidableEq, Repr, Inhabited

/-- One region's price: visits, ways out, backtrack entries and undo
entries, each per entry into the region. -/
structure Price where
  work : Poly
  outs : Poly
  stack : Poly
  trail : Poly
deriving DecidableEq, Repr, Inhabited

/-- A bound certificate: the configuration it is for, the complexity claim,
the four whole-call bounds, and one price per region of the compiler's
tree. -/
structure Cert where
  config : Cfg
  complexity : Cc
  cost : Poly
  stack : Poly
  trail : Poly
  mem : Poly
  prices : Array Price
deriving DecidableEq, Repr, Inhabited

/-- A walk's accumulator: what one entry into a region has charged so far,
and the flow leaving it going forward. Flow is the whole of the composition
— every quantity is linear in it. -/
structure Acc where
  work : Poly
  stack : Poly
  trail : Poly
  flow : Poly
deriving DecidableEq, Repr, Inhabited

/-- `fresh`: nothing charged yet, and this much flow arriving. -/
def Acc.fresh (flow : Poly) : Acc := ⟨Poly.zero, Poly.zero, Poly.zero, flow⟩

/-- `_blank`: what a price slot holds until the analyzer fills it. Written
out rather than left to the zero value, because the zero of a `Poly` names a
growth base of zero and no bound has that shape. -/
def Price.blank : Price := ⟨Poly.zero, Poly.zero, Poly.zero, Poly.zero⟩

/-- `cert_bound`: the three bounds the accessors of DESIGN.md section 2.4
ask for, each against its own ceiling — a number no valid limit could match
is no use to the caller who has to pick one. The TIR carries a `known` flag
because a printed enum is an integer anyone can invent; Lean's `Bk` is
closed, so there is no such value to guard against. -/
def certBound (cert : Cert) (kind : Bk) (n : Nat) : Bound :=
  let (which, roof) :=
    match kind with
    | .cost => (cert.cost, counterMax)
    | .stack => (cert.stack, maxStack)
    | .mem => (cert.mem, ceiling)
  let out := polyValue which n
  if out.ok ∧ out.value > roof then Bound.exceeds else out

/-- The loop of `scan_span`, on the ground the walk still has to cover: a
child jump lands past `pc` or is refused, so `hi - pc` falls either way. -/
def scanSpanGo (code : Array Inst) (regions : Array Region)
    (prices : Array Price) (sibs : Array Nat) (hi : Nat)
    (pc cursor : Nat) (acc : Acc) (over : Bool) : Cr × Acc × Bool :=
  if _h : pc < hi then
    if cursor != none32 && (regions[cursor]!).lo == pc then
      -- The one comparison here that is not arithmetic: a child covering no
      -- instruction would leave the walk where it was. `shape_span` is
      -- where that is a rule rather than a guard.
      if _hk : (regions[cursor]!).hi ≤ pc then (.crShape, acc, over)
      else
        let kid := regions[cursor]!
        let claim := prices[cursor]!
        let flow := acc.flow
        let (chargedWork, over) := polyMul flow claim.work over
        let (work, over) := polyAdd acc.work chargedWork over
        let (chargedStack, over) := polyMul flow claim.stack over
        let (stack, over) := polyAdd acc.stack chargedStack over
        let (chargedTrail, over) := polyMul flow claim.trail over
        let (trail, over) := polyAdd acc.trail chargedTrail over
        let (onward, over) := polyMul flow claim.outs over
        scanSpanGo code regions prices sibs hi kid.hi (sibs[cursor]!)
          ⟨work, stack, trail, onward⟩ over
    else
      let (visited, over) := polyAdd acc.work acc.flow over
      match (code[pc]!).op with
      | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .circ | .circM
      | .doll | .dollE | .dollM | .sod | .eod | .eodn | .wordB | .notWordB =>
          let acc := { acc with work := visited }
          scanSpanGo code regions prices sibs hi (pc + 1) cursor acc over
      | .save =>
          let (trail, over) := polyAdd acc.trail acc.flow over
          let acc := { acc with work := visited, trail := trail }
          scanSpanGo code regions prices sibs hi (pc + 1) cursor acc over
      | .accept =>
          -- A match ends the attempt, so nothing after this point is
          -- reached by way of it.
          let acc := { acc with work := visited, flow := Poly.zero }
          scanSpanGo code regions prices sibs hi (pc + 1) cursor acc over
      | _ =>
          -- `shape_span` has already refused every other opcode, so this
          -- arm keeps the dispatch total rather than stating a rule.
          (.crOpcode, acc, over)
  else (.crOk, acc, over)
termination_by hi - pc
decreasing_by all_goals omega

/-- `scan_span` (BOUNDS.md section 4.1, checker side): read the range left
to right against the claimed prices, carrying the flow. -/
def scanSpan (code : Array Inst) (regions : Array Region)
    (prices : Array Price) (sibs : Array Nat) (lo hi first : Nat)
    (acc : Acc) (over : Bool) : Cr × Acc × Bool :=
  scanSpanGo code regions prices sibs hi lo first acc over

/-- The chain walk of `scan_alt`. The fuel is the price count, which is the
region count: it only bounds the walk, and the sibling chain is what the
walk really follows. -/
def scanAltGo (prices : Array Price) (sibs : Array Nat) :
    Nat → Nat → Acc → Bool → Cr × Acc × Bool
  | 0, _, acc, over => (.crOk, acc, over)
  | fuel + 1, c, acc, over =>
      if c == none32 then (.crOk, acc, over)
      else
        let claim := prices[c]!
        let nxt := sibs[c]!
        let (acc, over) :=
          if nxt != none32 then
            -- Every branch but the last is guarded by a split and leaves by
            -- a jump: the split is visited once, and the jump once per way
            -- the branch found to succeed.
            let (extra, over) := polyAdd (Poly.const 1) claim.outs over
            let (work, over) := polyAdd acc.work extra over
            let (stack, over) := polyAdd acc.stack (Poly.const 1) over
            ({ acc with work := work, stack := stack }, over)
          else (acc, over)
        let (work, over) := polyAdd acc.work claim.work over
        let (stack, over) := polyAdd acc.stack claim.stack over
        let (trail, over) := polyAdd acc.trail claim.trail over
        let (flow, over) := polyAdd acc.flow claim.outs over
        scanAltGo prices sibs fuel nxt ⟨work, stack, trail, flow⟩ over

/-- `scan_alt` (section 4.2): backtracking works its way along the chain of
splits, so every branch is entered, once. -/
def scanAlt (prices : Array Price) (sibs : Array Nat) (first : Nat)
    (over : Bool) : Cr × Acc × Bool :=
  scanAltGo prices sibs prices.size first (Acc.fresh Poly.zero) over

/-- `scan_repeat` (sections 4.3 and 4.4): an optional item, or the counted
header around a priced body. The body's ambiguity is what one iteration
hands the next, so a body that grows more ambiguous with the subject has no
closed form here — an honest refusal rather than a bound nobody can write
down. -/
def scanRepeat (code : Array Inst) (reps : Array RepInfo)
    (regions : Array Region) (prices : Array Price) (sibs : Array Nat)
    (at_ first : Nat) (over : Bool) : Cr × Acc × Bool :=
  let here := regions[at_]!
  let lo := here.lo
  let hi := here.hi
  let acc := Acc.fresh (Poly.const 1)
  if hi ≤ lo then (.crShape, acc, over)
  else
    let head := code[lo]!
    if head.op = .split then
      -- An optional item: one split whose arms are the body and what
      -- follows. Skipping the body is a way out of the region too.
      let (verdict, acc, over) :=
        scanSpan code regions prices sibs (lo + 1) hi first acc over
      if verdict ≠ .crOk then (verdict, acc, over)
      else
        let (work, over) := polyAdd acc.work (Poly.const 1) over
        let (stack, over) := polyAdd acc.stack (Poly.const 1) over
        let (flow, over) := polyAdd acc.flow (Poly.const 1) over
        (.crOk, { acc with work := work, stack := stack, flow := flow }, over)
    else if head.op ≠ .repZero then (.crShape, acc, over)
    else if hi - lo < 4 then (.crShape, acc, over)
    else
      let which := head.arg
      if which ≥ reps.size then (.crShape, acc, over)
      else
        let rep := reps[which]!
        let (verdict, acc, over) :=
          scanSpan code regions prices sibs (lo + 3) (hi - 1) first acc over
        if verdict ≠ .crOk then (verdict, acc, over)
        else
          let branching := acc.flow
          if !branching.flat then (.crAmbiguous, acc, over)
          else
            let ways := branching.c0
            let bounded := rep.hi != none32
            let ceil :=
              if bounded then (if rep.hi > rep.lo then rep.hi else rep.lo)
              else rep.lo
            -- Passes through the head, one more than the iteration count:
            -- the pass that finds the count spent reads the counter,
            -- decides, and leaves. Bounded above, the declared maximum
            -- stops it; unbounded, the empty-match rule does.
            let rounds :=
              if !bounded then { Poly.zero with c0 := rep.lo + 1, c1 := 1 }
              else Poly.const (ceil + 1)
            let (flow, over) :=
              if ways > 1 then
                let exponent := if !bounded then rep.lo + 2 else ceil + 1
                let raised := boundPow ways exponent
                let over := if !raised.ok then true else over
                let flow :=
                  if !bounded then
                    { Poly.zero with base := ways, c0 := raised.value }
                  else Poly.const raised.value
                (flow, over)
              else (rounds, over)
            let body := acc
            let per := Poly.const ways
            let one := Poly.const 1
            -- One pass through the head costs the head itself, the enter,
            -- the body, and one tail per way the body found to finish.
            -- Zeroing the counter happens once, which is the constant
            -- outside.
            let (withBody, over) := polyAdd body.work per over
            let (each, over) := polyAdd (Poly.const 2) withBody over
            let (passes, over) := polyMul flow each over
            let (work, over) := polyAdd one passes over
            -- The head forks at most once a pass.
            let (forks, over) := polyAdd one body.stack over
            let (stack, over) := polyMul flow forks over
            -- The enter remembers a position and every tail counts, both
            -- through the trail, and the zeroing outside is on it too.
            let (leaves, over) := polyAdd one per over
            let (writes, over) := polyAdd leaves body.trail over
            let (recorded, over) := polyMul flow writes over
            let (trail, over) := polyAdd one recorded over
            -- Leaving happens at the head, when the count is spent, and at
            -- the tail, when an empty iteration ends it.
            let (outs, over) := polyMul flow leaves over
            (.crOk, ⟨work, stack, trail, outs⟩, over)

/-- `charge_call` (BOUNDS.md section 5, checker side): what a whole call
costs on top of what the tree prices. Cost and memory are bounds a claim may
legitimately overshoot; the stack and the trail are held to the section 5
equations exactly, because a context sizes its two arrays from those claims
while the memory that pays for them was priced from the walk. -/
def chargeCall (re : Re) (cert : Cert) (whole : Price) (over : Bool) :
    Cr × Bool :=
  let novec := (re.ncap + 1) * 2
  let setup := (re.nregs + novec) * regSize
  let deliver := novec * regSize
  let reset := re.nregs * regSize
  -- The growth schedule doubles from its floor, so a run that holds at most
  -- k entries never reserves more than twice that, and one that never
  -- pushes never allocates at all.
  let grow := fun (scratch claimed : Poly) (esize : Nat) (over : Bool) =>
    let (capacity, over) :=
      if !claimed.nothing then
        let (grown, over) := polyMul claimed (Poly.const growFactor) over
        polyAdd (Poly.const growMin) grown over
      else (Poly.zero, over)
    let (weighed, over) := polyMul capacity (Poly.const esize) over
    polyAdd scratch weighed over
  let (scratch, over) := grow Poly.zero whole.stack btSize over
  let (scratch, over) := grow scratch whole.trail undoSize over
  -- An undo entry put back costs one unit per IR byte of the register, and
  -- one can only be put back if something recorded it, so the trail bound
  -- prices the replay too.
  let (replay, over) := polyMul whole.trail (Poly.const regSize) over
  let (replayed, over) := polyAdd whole.work replay over
  let (attempt, over) := polyAdd (Poly.const reset) replayed over
  -- The 3 and the 2 below come from the growth schedule rather than from
  -- the matcher: a doubling run allocates twice its final reservation, one
  -- more while copying, and holds both at once at the peak.
  let (positions, over) := polyMul attempt Poly.step over
  let (growth, over) := polyMul scratch (Poly.const 3) over
  let (running, over) := polyAdd positions growth over
  let (cost, over) := polyAdd (Poly.const (setup + deliver)) running over
  let (held, over) := polyMul scratch (Poly.const 2) over
  let (memory, over) := polyAdd (Poly.const (setup + deliver)) held over
  if over then (.crOverflow, over)
  else if !polyGe cert.cost cost then (.crTotalCost, over)
  else if !polyEq cert.stack whole.stack then (.crTotalStack, over)
  else if !polyEq cert.trail whole.trail then (.crTotalTrail, over)
  else if !polyGe cert.mem memory then (.crTotalMem, over)
  else (.crOk, over)

/-- The loop of `shape_span` (section 4.1 minus the pricing): what a
straight-line region may hold loose, and its children met in code order. -/
def shapeSpanGo (code : Array Inst) (regions : Array Region)
    (sibs : Array Nat) (hi : Nat) (pc cursor : Nat) : Cr :=
  if _h : pc < hi then
    -- Children arrive in code order, so one behind the walk is one the walk
    -- has already priced as part of its parent.
    if cursor != none32 && (regions[cursor]!).lo < pc then .crShape
    else if cursor != none32 && (regions[cursor]!).lo == pc then
      if _hk : (regions[cursor]!).hi ≤ pc then .crShape
      else if (regions[cursor]!).hi > hi then .crShape
      else shapeSpanGo code regions sibs hi (regions[cursor]!).hi (sibs[cursor]!)
    else
      match (code[pc]!).op with
      | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .circ | .circM
      | .doll | .dollE | .dollM | .sod | .eod | .eodn | .wordB | .notWordB
      | .save | .accept => shapeSpanGo code regions sibs hi (pc + 1) cursor
      | _ => .crOpcode
  -- A child the walk never reached is one covering code this span does not,
  -- which no rule prices.
  else if cursor != none32 then .crChildren
  else .crOk
termination_by hi - pc
decreasing_by all_goals omega

/-- `shape_span`: BOUNDS.md section 4.1, the structure without the price. -/
def shapeSpan (code : Array Inst) (regions : Array Region)
    (sibs : Array Nat) (lo hi first : Nat) : Cr :=
  shapeSpanGo code regions sibs hi lo first

/-- The branch walk of `shape_alt`: an alternation compiles to `split branch
jump split branch jump ... branch`, every jump patched to the end and every
split's other arm pointing at the next one, so walking the branches walks
the code. -/
def shapeAltGo (code : Array Inst) (regions : Array Region)
    (sibs : Array Nat) (hi : Nat) : Nat → Nat → Nat → Nat → Cr
  | 0, _, c, k =>
      if c ≠ none32 then .crChildren
      else if k < 2 then .crShape
      else .crOk
  | fuel + 1, p, c, k =>
      if c == none32 then
        -- One branch is not an alternation: the compiler emits no split for
        -- it, so a region claiming to be one is pricing instructions that
        -- are not there.
        if k < 2 then .crShape else .crOk
      else
        let kid := regions[c]!
        if kid.kind ≠ .branch then .crChildren
        else
          let nxt := sibs[c]!
          if nxt ≠ none32 then
            if p ≥ hi then .crShape
            else
              let fork := code[p]!
              if fork.op ≠ .split then .crShape
              else if fork.arg ≠ p + 1 then .crShape
              else if kid.lo ≠ p + 1 then .crShape
              else
                let stop := kid.hi
                if stop ≥ hi then .crShape
                else
                  let leave := code[stop]!
                  if leave.op ≠ .jump ∨ leave.arg ≠ hi then .crShape
                  else if fork.alt ≠ stop + 1 then .crShape
                  else shapeAltGo code regions sibs hi fuel (stop + 1) nxt (k + 1)
          else
            if kid.lo ≠ p ∨ kid.hi ≠ hi then .crShape
            else shapeAltGo code regions sibs hi fuel p nxt (k + 1)

/-- `shape_alt` (section 4.2): the splits, the branches and the jumps line
up. -/
def shapeAlt (code : Array Inst) (regions : Array Region)
    (sibs : Array Nat) (at_ first : Nat) : Cr :=
  let here := regions[at_]!
  shapeAltGo code regions sibs here.hi regions.size here.lo first 0

/-- `shape_repeat` (sections 4.3 and 4.4): an optional item, or the
five-part header. Between the four opcodes and the three offsets checked
here there is nothing left for a region to choose, which is why a repeat
needs no witness field beyond its range. -/
def shapeRepeat (code : Array Inst) (reps : Array RepInfo)
    (regions : Array Region) (sibs : Array Nat) (at_ first : Nat) : Cr :=
  let here := regions[at_]!
  let lo := here.lo
  let hi := here.hi
  if hi ≤ lo then .crShape
  else
    let head := code[lo]!
    if head.op = .split then
      -- An optional item: one split whose arms are the body and what
      -- follows, in whichever order the greediness asks for.
      let greedy := head.arg == lo + 1 && head.alt == hi
      let lazy := head.arg == hi && head.alt == lo + 1
      if !(greedy || lazy) then .crShape
      else shapeSpan code regions sibs (lo + 1) hi first
    else if head.op ≠ .repZero then .crShape
    else if hi - lo < 4 then .crShape
    else
      let which := head.arg
      if which ≥ reps.size then .crShape
      else
        let loops := code[lo + 1]!
        if loops.op ≠ .repLoop ∨ loops.arg ≠ which then .crShape
        else
          let enter := code[lo + 2]!
          if enter.op ≠ .repEnter ∨ enter.arg ≠ which then .crShape
          else
            let tail := code[hi - 1]!
            if tail.op ≠ .repNext ∨ tail.arg ≠ which then .crShape
            else
              -- The repetition the code names has to be the one that
              -- drives this range, or the iteration count would be read
              -- off some other quantifier.
              let rep := reps[which]!
              if rep.head ≠ lo + 1 ∨ rep.body ≠ lo + 2 ∨ rep.after ≠ hi then
                .crShape
              else shapeSpan code regions sibs (lo + 3) (hi - 1) first

/-- The nesting pass of `cert_shape`: children in index order, ranges nested
and non-overlapping, every parent before its own child — which is what makes
the tree a tree without walking it — and branches only under alternations.
`ends` holds where the last child of each region ended, so one pass settles
both halves of the sibling rule. -/
def certShapeNest (regions : Array Region) : Nat → Nat → Array Nat → Option Cr
  | _, 0, _ => none
  | i, fuel + 1, ends =>
      let here := regions[i]!
      let parent := here.parent
      if here.kind = .root then some .crTwoRoots
      else if parent ≥ i then some .crParentOrder
      else if here.lo > here.hi then some .crBackwards
      else
        let outer := regions[parent]!
        if here.lo < outer.lo ∨ here.hi > outer.hi then some .crNotNested
        else if here.lo < ends[parent]! then some .crOverlap
        else if here.kind = .branch ∧ outer.kind ≠ .alt then some .crChildren
        else certShapeNest regions (i + 1) fuel (ends.set! parent here.hi)

/-- The dispatch pass of `cert_shape`: the code under each region, outermost
first, so a badly built tree is answered with the outermost thing wrong with
it. The TIR starts the verdict at the refusal a made-up kind ordinal has
earned; `Rk` is closed, so the match needs no such backstop. -/
def certShapeWalk (re : Re) (kids sibs : Array Nat) : Nat → Nat → Cr
  | _, 0 => .crOk
  | i, fuel + 1 =>
      let one := re.regions[i]!
      let first := kids[i]!
      let verdict :=
        match one.kind with
        | .root | .group | .branch =>
            shapeSpan re.code re.regions sibs one.lo one.hi first
        | .alt => shapeAlt re.code re.regions sibs i first
        | .«repeat» => shapeRepeat re.code re.reps re.regions sibs i first
      if verdict ≠ .crOk then verdict
      else certShapeWalk re kids sibs (i + 1) fuel

/-- `cert_shape`: does this program's region tree describe this program?
Everything the checker can settle without looking at a certificate, which is
the half of it that runs whether or not the analyzer found a bound to check
— a compiler that emitted a bad tree is a bug of ours either way. -/
def certShape (re : Re) : Cr :=
  let code := re.code
  let regions := re.regions
  let total := regions.size
  if total = 0 then .crNoRegions
  else
    let root := regions[0]!
    if root.kind ≠ .root then .crRootKind
    else if root.parent ≠ none32 then .crRootParent
    else if root.lo ≠ 0 ∨ root.hi ≠ code.size then .crRootRange
    else
      -- A region starts out as its own `lo`, which makes the first child's
      -- overlap test the containment test and needs no special case.
      match certShapeNest regions 1 (total - 1) (regions.map (·.lo)) with
      | some verdict => verdict
      | none =>
          let (kids, sibs) := regionKids regions
          certShapeWalk re kids sibs 0 total

/-- The Pike scratch reservation (`Room`): the growth-schedule capacity of
each array a context materializes, and their weighted sum. -/
structure Room where
  lists : Nat
  stk : Nat
  tables : Nat
  pool : Nat
  reserved : Nat
  words : Nat
deriving DecidableEq, Repr, Inhabited

/-- `pike_room`: the capacities behind BOUNDS.md section 9's reservation.
Context creation reserves real arrays from these same counts, one function
for both, so the bound and the reservation cannot disagree. -/
def pikeRoom (re : Re) (over : Bool) : Room × Bool :=
  let big := re.code.size
  let slots := (re.ncap + 1) * 2
  let words := re.code.size / 8 + 1
  let (lists, over) := growthCap big over
  let (stkEntries, over) := satMul big 2 over
  let (stk, over) := growthCap stkEntries over
  let (blocks4, over) := satMul big 4 over
  let (blocks, over) := satAdd blocks4 2 over
  let (tables, over) := growthCap blocks over
  let (poolEntries, over) := satMul blocks slots over
  let (pool, over) := growthCap poolEntries over
  -- The reservation R: the two thread lists, the closure stack, refcounts
  -- and the free list, and the pool, each capacity times its entry size.
  let (reserved, over) := satMul lists (2 * thSize) over
  let (stkBytes, over) := satMul stk thSize over
  let (reserved, over) := satAdd reserved stkBytes over
  let (tableBytes, over) := satMul tables (2 * regSize) over
  let (reserved, over) := satAdd reserved tableBytes over
  let (poolBytes, over) := satMul pool regSize over
  let (reserved, over) := satAdd reserved poolBytes over
  (⟨lists, stk, tables, pool, reserved, words⟩, over)

/-- `pike_price`: the closed form of BOUNDS.md section 9. No region prices —
the visited set admits every instruction at most once per list build,
whatever the pattern's structure — so the whole call is a handful of counts
read straight off the program. `none` is the arithmetic running out of
counter, which for this configuration means there is honestly no
certificate. -/
def pikePrice (re : Re) : Option Cert :=
  let over := false
  let big := re.code.size
  let slots := (re.ncap + 1) * 2
  -- The TIR sizes a block with a plain counter multiply, which saturates
  -- silently; the operands sit far below the cap, so threading the flag
  -- here changes nothing and keeps the arithmetic uniform.
  let (block, over) := satMul slots regSize over
  let saves := re.code.foldl (fun n inst => if inst.op = .save then n + 1 else n) 0
  let (room, over) := pikeRoom re over
  let reserved := room.reserved
  let words := room.words
  let (setup, over) := satAdd block words over
  -- One position: the closure's marks and the steps, at most one each per
  -- instruction; a copy-on-write per Save plus the accept's own; the seed's
  -- block fill; and the visited set cleared.
  let (position, over) := satMul big 2 over
  let (writers, over) := satAdd saves 2 over
  let (writes, over) := satMul writers block over
  let (position, over) := satAdd position writes over
  let (position, over) := satAdd position words over
  -- The delivered answer is charged in both lines: copied out once as cost,
  -- resident alongside the scratch as memory, at one block.
  let (base, over) := satAdd setup block over
  let (growth, over) := satMul reserved 3 over
  let (steady, over) := satAdd base growth over
  let (held, over) := satMul reserved 2 over
  let (resident, over) := satAdd base held over
  if over then none
  else
    let cost := { Poly.zero with c0 := steady, c1 := position }
    some ⟨.pike, .linear, cost, Poly.zero, Poly.zero, Poly.const resident, #[]⟩

/-- `pike_check`: the certificate checker that lives beside the Pike
matcher. For this configuration the rule is the formula, so the checker
recomputes it and asks for domination — and, as on the backtracking side,
for equality on the stack and the trail, which here are exactly zero since
neither array exists on this path. -/
def pikeCheck (re : Re) (cert : Cert) : Cr :=
  if !pikeOk re.code re.reps then .crIneligible
  else if cert.config ≠ .pike then .crConfig
  else if cert.prices.size ≠ 0 then .crPrices
  else
    -- The TIR also refuses a complexity naming no variant; `Cc` is closed,
    -- so that arm has nothing left to match.
    match cert.complexity with
    | .notProvenLinear => .crNotLinear
    | .linear =>
        if !cert.cost.linear then .crNotLinear
        else
          match pikePrice re with
          | none => .crOverflow
          | some needed =>
              if !polyGe cert.cost needed.cost then .crTotalCost
              else if !polyEq cert.stack needed.stack then .crTotalStack
              else if !polyEq cert.trail needed.trail then .crTotalTrail
              else if !polyGe cert.mem needed.mem then .crTotalMem
              else .crOk

/-- The per-price half of `cert_check`'s base rule: a base of zero is 0^n,
which is 1 at n = 0 and 0 everywhere else, and no bound has that shape. -/
def certCheckBases (prices : Array Price) : Nat → Nat → Bool
  | _, 0 => true
  | i, fuel + 1 =>
      let claimed := prices[i]!
      if claimed.work.base = 0 ∨ claimed.outs.base = 0 ∨
          claimed.stack.base = 0 ∨ claimed.trail.base = 0 then false
      else certCheckBases prices (i + 1) fuel

/-- The induction of `cert_check`: each region recomputed from what its
children claim, so the step that makes the whole tree sound is one deep and
entirely local. Overflow is asked about before the comparison, because a
requirement that stopped at the cap is one a certificate would be found to
satisfy. -/
def certCheckRegions (re : Re) (prices : Array Price)
    (kids sibs : Array Nat) : Nat → Nat → Bool → Cr × Bool
  | _, 0, over => (.crOk, over)
  | i, fuel + 1, over =>
      let one := re.regions[i]!
      let first := kids[i]!
      let (verdict, acc, over) :=
        match one.kind with
        | .root | .group | .branch =>
            scanSpan re.code re.regions prices sibs one.lo one.hi first
              (Acc.fresh (Poly.const 1)) over
        | .alt => scanAlt prices sibs first over
        | .«repeat» =>
            scanRepeat re.code re.reps re.regions prices sibs i first over
      if verdict ≠ .crOk then (verdict, over)
      else if over then (.crOverflow, over)
      else
        let mine := prices[i]!
        if !polyGe mine.work acc.work then (.crRegionWork, over)
        else if !polyGe mine.outs acc.flow then (.crRegionOuts, over)
        else if !polyGe mine.stack acc.stack then (.crRegionStack, over)
        else if !polyGe mine.trail acc.trail then (.crRegionTrail, over)
        else certCheckRegions re prices kids sibs (i + 1) fuel over

/-- `cert_check`: does this certificate bound this program? The Pike
configuration dispatches to the checker beside its matcher, the memoized
path is refused by name until M9, and the tree is settled first and on its
own — whether it describes the program is a question about the program. -/
def certCheck (re : Re) (config : Cfg) (cert : Cert) : Cr :=
  if config = .pike then pikeCheck re cert
  else if config ≠ .backtrack then .crNoRules
  else if cert.config ≠ config then .crConfig
  else
    let shape := certShape re
    if shape ≠ .crOk then shape
    else
      let regions := re.regions
      let prices := cert.prices
      let total := regions.size
      -- One price per region, in the same order, so a claim cannot be
      -- about a region nobody emitted and no region can go unpriced.
      if prices.size ≠ total then .crPrices
      else if cert.cost.base = 0 ∨ cert.stack.base = 0 ∨
          cert.trail.base = 0 ∨ cert.mem.base = 0 then .crBase
      -- The TIR refuses a complexity naming no variant with `CrShape`;
      -- `Cc` is closed, so only the linearity half of the rule remains:
      -- linear means the cost really is at most c * (n + 1).
      else if cert.complexity = .linear ∧ !cert.cost.linear then .crNotLinear
      else if !certCheckBases prices 0 total then .crBase
      else
        let (kids, sibs) := regionKids regions
        let (verdict, over) := certCheckRegions re prices kids sibs 0 total false
        if verdict ≠ .crOk then verdict
        else
          -- What the call costs on top of what the tree prices.
          let (charged, _) := chargeCall re cert (prices[0]!) over
          if charged ≠ .crOk then charged
          else .crOk

/-- The loop of `price_span`, the analyzer's own statement of the section
4.1 walk. It reads the same as the checker's on purpose and is written out
again on purpose: sharing it would make the verdict an echo. -/
def priceSpanGo (code : Array Inst) (regions : Array Region)
    (prices : Array Price) (sibs : Array Nat) (hi : Nat)
    (pc cursor : Nat) (acc : Acc) (over : Bool) : Ar × Acc × Bool :=
  if _h : pc < hi then
    if cursor != none32 && (regions[cursor]!).lo == pc then
      -- The compiler drops a region that covers nothing rather than
      -- emitting one, so meeting one here is the tree failing to describe
      -- the program.
      if _hk : (regions[cursor]!).hi ≤ pc then (.arShape, acc, over)
      else
        let kid := regions[cursor]!
        let priced := prices[cursor]!
        let flow := acc.flow
        let (chargedWork, over) := polyMul flow priced.work over
        let (work, over) := polyAdd acc.work chargedWork over
        let (chargedStack, over) := polyMul flow priced.stack over
        let (stack, over) := polyAdd acc.stack chargedStack over
        let (chargedTrail, over) := polyMul flow priced.trail over
        let (trail, over) := polyAdd acc.trail chargedTrail over
        let (onward, over) := polyMul flow priced.outs over
        priceSpanGo code regions prices sibs hi kid.hi (sibs[cursor]!)
          ⟨work, stack, trail, onward⟩ over
    else
      let (visited, over) := polyAdd acc.work acc.flow over
      match (code[pc]!).op with
      | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .circ | .circM
      | .doll | .dollE | .dollM | .sod | .eod | .eodn | .wordB | .notWordB =>
          let acc := { acc with work := visited }
          priceSpanGo code regions prices sibs hi (pc + 1) cursor acc over
      | .save =>
          let (trail, over) := polyAdd acc.trail acc.flow over
          let acc := { acc with work := visited, trail := trail }
          priceSpanGo code regions prices sibs hi (pc + 1) cursor acc over
      | .accept =>
          -- A match ends the attempt, so nothing after this point is
          -- reached by way of it.
          let acc := { acc with work := visited, flow := Poly.zero }
          priceSpanGo code regions prices sibs hi (pc + 1) cursor acc over
      | _ => (.arShape, acc, over)
  else (.arOk, acc, over)
termination_by hi - pc
decreasing_by all_goals omega

/-- `price_span` (section 4.1, analyzer side): read the range left to right,
carrying the flow. -/
def priceSpan (code : Array Inst) (regions : Array Region)
    (prices : Array Price) (sibs : Array Nat) (lo hi first : Nat)
    (acc : Acc) (over : Bool) : Ar × Acc × Bool :=
  priceSpanGo code regions prices sibs hi lo first acc over

/-- The chain walk of `price_alt`, the price count bounding it and the
sibling chain steering it. -/
def priceAltGo (prices : Array Price) (sibs : Array Nat) :
    Nat → Nat → Acc → Bool → Ar × Acc × Bool
  | 0, _, acc, over => (.arOk, acc, over)
  | fuel + 1, c, acc, over =>
      if c == none32 then (.arOk, acc, over)
      else
        let priced := prices[c]!
        let nxt := sibs[c]!
        let (acc, over) :=
          if nxt != none32 then
            -- The split is visited once, and the jump that closes the
            -- branch once per way the branch found to succeed.
            let (extra, over) := polyAdd (Poly.const 1) priced.outs over
            let (work, over) := polyAdd acc.work extra over
            let (stack, over) := polyAdd acc.stack (Poly.const 1) over
            ({ acc with work := work, stack := stack }, over)
          else (acc, over)
        let (work, over) := polyAdd acc.work priced.work over
        let (stack, over) := polyAdd acc.stack priced.stack over
        let (trail, over) := polyAdd acc.trail priced.trail over
        let (flow, over) := polyAdd acc.flow priced.outs over
        priceAltGo prices sibs fuel nxt ⟨work, stack, trail, flow⟩ over

/-- `price_alt` (section 4.2): an alternation costs what its branches cost,
plus the fork before each of them and the jump after. The shape of the
splits and the jumps is the checker's business. -/
def priceAlt (prices : Array Price) (sibs : Array Nat) (first : Nat)
    (over : Bool) : Ar × Acc × Bool :=
  priceAltGo prices sibs prices.size first (Acc.fresh Poly.zero) over

/-- `price_repeat` (sections 4.3 and 4.4): an optional item, or a counted
repetition. Where the checker's twin folds an overflowing power into the
flag, this side answers `arOverflow` outright — the analyzer has nothing to
compare a saturated number against. -/
def priceRepeat (code : Array Inst) (reps : Array RepInfo)
    (regions : Array Region) (prices : Array Price) (sibs : Array Nat)
    (at_ first : Nat) (over : Bool) : Ar × Acc × Bool :=
  let here := regions[at_]!
  let lo := here.lo
  let hi := here.hi
  let acc := Acc.fresh (Poly.const 1)
  if hi ≤ lo then (.arShape, acc, over)
  else
    let head := code[lo]!
    if head.op = .split then
      -- Skipping the body is a way out of the region too.
      let (verdict, acc, over) :=
        priceSpan code regions prices sibs (lo + 1) hi first acc over
      if verdict ≠ .arOk then (verdict, acc, over)
      else
        let (work, over) := polyAdd acc.work (Poly.const 1) over
        let (stack, over) := polyAdd acc.stack (Poly.const 1) over
        let (flow, over) := polyAdd acc.flow (Poly.const 1) over
        (.arOk, { acc with work := work, stack := stack, flow := flow }, over)
    else if head.op ≠ .repZero then (.arShape, acc, over)
    else if hi - lo < 4 then (.arShape, acc, over)
    else
      let which := head.arg
      if which ≥ reps.size then (.arShape, acc, over)
      else
        let rep := reps[which]!
        let (verdict, acc, over) :=
          priceSpan code regions prices sibs (lo + 3) (hi - 1) first acc over
        if verdict ≠ .arOk then (verdict, acc, over)
        else
          -- What one iteration hands the next. A body that grows more
          -- ambiguous with the subject would raise a polynomial to a power
          -- of n, and no bound of section 2's shape has that form.
          let branching := acc.flow
          if !branching.flat then (.arAmbiguous, acc, over)
          else
            let ways := branching.c0
            let bounded := rep.hi != none32
            let ceil :=
              if bounded then (if rep.hi > rep.lo then rep.hi else rep.lo)
              else rep.lo
            -- Passes through the head, one more than the iteration count:
            -- the pass that finds the count spent reads the counter,
            -- decides, and leaves.
            let rounds :=
              if !bounded then { Poly.zero with c0 := rep.lo + 1, c1 := 1 }
              else Poly.const (ceil + 1)
            let raisedFlow :=
              if ways > 1 then
                let exponent := if !bounded then rep.lo + 2 else ceil + 1
                let raised := boundPow ways exponent
                if !raised.ok then none
                else if !bounded then
                  some { Poly.zero with base := ways, c0 := raised.value }
                else some (Poly.const raised.value)
              else some rounds
            match raisedFlow with
            | none => (.arOverflow, acc, over)
            | some flow =>
                let body := acc
                let per := Poly.const ways
                let one := Poly.const 1
                -- One pass through the head costs the head itself, the
                -- enter, the body, and one tail per way the body found to
                -- finish. Zeroing the counter happens once, which is the
                -- constant outside.
                let (withBody, over) := polyAdd body.work per over
                let (each, over) := polyAdd (Poly.const 2) withBody over
                let (passes, over) := polyMul flow each over
                let (work, over) := polyAdd one passes over
                -- The head forks at most once a pass.
                let (forks, over) := polyAdd one body.stack over
                let (stack, over) := polyMul flow forks over
                -- The enter remembers a position and every tail counts,
                -- both through the trail, and the zeroing outside is on it
                -- too.
                let (leaves, over) := polyAdd one per over
                let (writes, over) := polyAdd leaves body.trail over
                let (recorded, over) := polyMul flow writes over
                let (trail, over) := polyAdd one recorded over
                -- Leaving happens at the head, when the count is spent, and
                -- at the tail, when an empty iteration ends it.
                let (outs, over) := polyMul flow leaves over
                (.arOk, ⟨work, stack, trail, outs⟩, over)

/-- `price_call` (section 5, analyzer side): what a call pays on top of the
tree, written into the certificate's four whole-call bounds. -/
def priceCall (re : Re) (whole : Price) (cert : Cert) (over : Bool) :
    Cert × Bool :=
  let novec := (re.ncap + 1) * 2
  let setup := (re.nregs + novec) * regSize
  let deliver := novec * regSize
  let reset := re.nregs * regSize
  -- The growth schedule doubles from its floor, so a run that holds at most
  -- k entries never reserves more than twice that, and one that never
  -- pushes never allocates at all.
  let grow := fun (scratch held : Poly) (esize : Nat) (over : Bool) =>
    let (capacity, over) :=
      if !held.nothing then
        let (grown, over) := polyMul held (Poly.const growFactor) over
        polyAdd (Poly.const growMin) grown over
      else (Poly.zero, over)
    let (weighed, over) := polyMul capacity (Poly.const esize) over
    polyAdd scratch weighed over
  let (scratch, over) := grow Poly.zero whole.stack btSize over
  let (scratch, over) := grow scratch whole.trail undoSize over
  -- An undo entry put back costs one unit per IR byte of the register, and
  -- one can only be put back if something recorded it, so the trail bound
  -- prices the replay too.
  let (replay, over) := polyMul whole.trail (Poly.const regSize) over
  let (replayed, over) := polyAdd whole.work replay over
  let (attempt, over) := polyAdd (Poly.const reset) replayed over
  -- The 3 and the 2 below come from the growth schedule: a doubling run
  -- allocates twice its final reservation, copies out of one more, and the
  -- delivered ovector is resident alongside the scratch.
  let (positions, over) := polyMul attempt Poly.step over
  let (growth, over) := polyMul scratch (Poly.const 3) over
  let (running, over) := polyAdd positions growth over
  let (cost, over) := polyAdd (Poly.const (setup + deliver)) running over
  let (held, over) := polyMul scratch (Poly.const 2) over
  let (mem, over) := polyAdd (Poly.const (setup + deliver)) held over
  ({ cert with cost := cost, stack := whole.stack, trail := whole.trail, mem := mem }, over)

/-- The pre-validation of `cert_build`: every range inside the program, and
every parent before its child. Not the tree being validated — that is the
checker's whole job — but the one thing that has to be settled before the
walk below indexes the bytecode, because the analyzer is untrusted in both
directions: it may not be believed, and it may not read past the end of the
code on the way to being disbelieved. -/
def certBuildRanges (regions : Array Region) (stop : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | i, fuel + 1 =>
      let one := regions[i]!
      if one.lo > one.hi ∨ one.hi > stop then false
      else if i > 0 ∧ one.parent ≥ i then false
      else certBuildRanges regions stop (i + 1) fuel

/-- The reverse walk of `cert_build`: the compiler emits a region before its
children, so counting down from the end prices every region from prices that
are already there — the same induction the checker walks. -/
def certBuildWalk (re : Re) (kids sibs : Array Nat) :
    Nat → Array Price → Bool → Ar × Array Price × Bool
  | 0, prices, over => (.arOk, prices, over)
  | i + 1, prices, over =>
      let one := re.regions[i]!
      let first := kids[i]!
      let (verdict, acc, over) :=
        match one.kind with
        | .root | .group | .branch =>
            priceSpan re.code re.regions prices sibs one.lo one.hi first
              (Acc.fresh (Poly.const 1)) over
        | .alt => priceAlt prices sibs first over
        | .«repeat» =>
            priceRepeat re.code re.reps re.regions prices sibs i first over
      if verdict ≠ .arOk then (verdict, prices, over)
      else if over then (.arOverflow, prices, over)
      else
        let prices := prices.set! i ⟨acc.work, acc.flow, acc.stack, acc.trail⟩
        certBuildWalk re kids sibs i prices over

/-- `cert_build`: search for a certificate to claim. `arOk` is not a claim
that the tree was well formed — deciding that is the checker's job — only
that this walk never had to guess or read past the end of the program. -/
def certBuild (re : Re) : Ar × Option Cert :=
  let regions := re.regions
  let total := regions.size
  if total = 0 then (.arShape, none)
  else if !certBuildRanges regions re.code.size 0 total then (.arShape, none)
  else
    let prices := Array.replicate total Price.blank
    let (kids, sibs) := regionKids regions
    let (found, prices, over) := certBuildWalk re kids sibs total prices false
    if found ≠ .arOk then (found, none)
    else
      let (cert, over) := priceCall re (prices[0]!) default over
      if over then (.arOverflow, none)
      else
        -- Linear is a thing to read off the bound rather than a thing to
        -- decide about the pattern; the checker holds the claim to the
        -- same predicate.
        let complexity := if cert.cost.linear then Cc.linear else Cc.notProvenLinear
        let cert := { cert with config := Cfg.backtrack, complexity := complexity, prices := prices }
        (.arOk, some cert)

/-- `cert_install`: the whole resource analysis as compilation sees it — the
tree, then the Pike closed form on the patterns routed to it, then the
search, then the check. The answer is the verdict plus whichever
certificates were kept. `crOk` with no backtracking certificate is the
honest "no bound of a shape this arithmetic writes down"; any other verdict
means the two halves of BOUNDS.md disagree about one program, which no
pattern can cause and only a bug of ours can. A Pike certificate the checker
refused is not kept and its refusal is the verdict; one the pricer declined
to build is simply absent, and the walk goes on. -/
def certInstall (re : Re) : Cr × Option Cert × Option Cert :=
  let shape := certShape re
  if shape ≠ .crOk then (shape, none, none)
  else
    let pikeStep : Cr ⊕ Option Cert :=
      if re.pike then
        match pikePrice re with
        | some pcert =>
            let pv := certCheck re .pike pcert
            if pv ≠ .crOk then .inl pv else .inr (some pcert)
        | none => .inr none
      else .inr none
    match pikeStep with
    | .inl pv => (pv, none, none)
    | .inr pikeCert =>
        let (found, built) := certBuild re
        if found = .arShape then
          -- The analyzer met something in the compiler's own tree it had
          -- no rule for, which `cert_shape` has just said there is none of.
          (.crShape, none, pikeCert)
        else if found ≠ .arOk then (.crOk, none, pikeCert)
        else
          match built with
          -- `arOk` always carries a certificate; answering `crOk` here
          -- keeps the match total without inventing a refusal.
          | none => (.crOk, none, pikeCert)
          | some cert =>
              let verdict := certCheck re .backtrack cert
              if verdict ≠ .crOk then (verdict, none, pikeCert)
              else (.crOk, some cert, pikeCert)

end Pcrevera.Ref
