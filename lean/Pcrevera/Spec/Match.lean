import Pcrevera.Basic
import Pcrevera.Spec.Tables

/-!
# The pattern semantics (S-2, S-3, S-4)

`Matches` is the trusted definition of what a wave 1 pattern means: a
priority-ordered big-step search over the AST whose answer is Found with
captures, NotFound, or BadInput, and nothing else.

The search returns the *list* of every way a subtree can match, in exactly
the backtracking preference order: greedy tries the body before the exit,
lazy the other way round, alternation in branch order, and an unbounded
repetition obeys pcre2's empty-match rule — past the minimum count, an
iteration that consumed nothing is the last one, and it keeps its saves.
The engines then have one obligation each: enumerate this list lazily
(backtracking) or take its first survivor in one pass (Pike).

Totality is earned through fuel. Fuel is spent once per repetition round
only — the branching lives in the list, so fuel bounds recursion depth, not
the size of the search tree — which is what makes the computable sufficient
fuel of S-3 a small structural bound rather than an exponential one.
-/


namespace Pcrevera.Spec

open Pcrevera

/-- The capture registers: `novec` slots, `unset32` before a write. -/
abbrev Regs := Array UInt32

/-- One way a subtree matched: where it ended and what it captured. -/
structure Thread where
  pos : Nat
  regs : Regs
deriving Repr

/-- What the leaves need to know: the subject and the conventions. -/
structure SCtx where
  s : ByteArray
  nl : NlType
  bsr : BsrType
  notbol : Bool
  noteol : Bool

/-- One assertion, decided: the anchor semantics of `engine/vm.py`, test for
test. -/
def assertionHolds (c : SCtx) (a : Ast) (pos : Nat) : Bool :=
  let n := c.s.size
  match a with
  | .circ => pos == 0 && !c.notbol
  | .circM =>
      if pos == 0 then !c.notbol
      else pos != n && newlineBefore c.s pos c.nl != 0
  | .doll => !c.noteol && atLineEnd c.s pos c.nl
  | .dollE => !c.noteol && pos == n
  | .dollM =>
      if pos < n then newlineAt c.s pos c.nl != 0 else !c.noteol
  | .sod => pos == 0
  | .eod => pos == n
  | .eodn => atLineEnd c.s pos c.nl
  | .wordB => wordEdge c.s pos
  | .notWordB => !wordEdge c.s pos
  | _ => false

mutual

/-- Every match of `a` from `pos`, in preference order. `none` is fuel
running out, which the sufficient fuel of S-3 rules out. -/
def search (fuel : Nat) (c : SCtx) (a : Ast) (pos : Nat) (regs : Regs) :
    Option (List Thread) :=
  let n := c.s.size
  match a with
  | .nul => some [⟨pos, regs⟩]
  | .chr b =>
      some (if pos < n && byteAt c.s pos == b then [⟨pos + 1, regs⟩] else [])
  | .chrCI folded =>
      some (if pos < n && lowerByte (byteAt c.s pos) == folded
            then [⟨pos + 1, regs⟩] else [])
  | .cls bits =>
      some (if pos < n && bits.has (byteAt c.s pos) then [⟨pos + 1, regs⟩] else [])
  | .any => some (if pos < n then [⟨pos + 1, regs⟩] else [])
  | .anyNoNL =>
      some (if pos < n && newlineAt c.s pos c.nl == 0 then [⟨pos + 1, regs⟩] else [])
  | .bsr =>
      let eaten := bsrAt c.s pos c.bsr
      some (if eaten != 0 then [⟨pos + eaten, regs⟩] else [])
  | .cat kids => searchCat fuel c kids pos regs
  | .alt arms => searchAlt fuel c arms pos regs
  | .grp cap body =>
      let opened := if cap != 0 then regs.set! (2 * cap) pos.toUInt32 else regs
      (search fuel c body pos opened).map
        (List.map fun t =>
          if cap != 0 then ⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩ else t)
  | .rep lo hi greedy body =>
      match hi with
      | some 0 => some [⟨pos, regs⟩]
      | some 1 =>
          if lo == 1 then search fuel c body pos regs
          else
            -- lo = 0: the optional item, one split, arms by greediness.
            (search fuel c body pos regs).map fun taken =>
              if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken
      | _ => searchRep fuel c body lo hi greedy 0 pos regs
  | a => some (if assertionHolds c a pos then [⟨pos, regs⟩] else [])
termination_by (fuel, sizeOf a)

/-- A concatenation: each match of the head continues into the tail. -/
def searchCat (fuel : Nat) (c : SCtx) (kids : List Ast) (pos : Nat)
    (regs : Regs) : Option (List Thread) :=
  match kids with
  | [] => some [⟨pos, regs⟩]
  | k :: rest => do
      let heads ← search fuel c k pos regs
      let tails ← heads.mapM fun t => searchCat fuel c rest t.pos t.regs
      pure tails.flatten
termination_by (fuel, sizeOf kids)

/-- An alternation: the branches in order, results appended. -/
def searchAlt (fuel : Nat) (c : SCtx) (arms : List Ast) (pos : Nat)
    (regs : Regs) : Option (List Thread) :=
  match arms with
  | [] => some []
  | arm :: rest => do
      let mine ← search fuel c arm pos regs
      let theirs ← searchAlt fuel c rest pos regs
      pure (mine ++ theirs)
termination_by (fuel, sizeOf arms)

/-- One pass through a counted repetition's head, the counter at `cnt`.

Mirrors the four Rep opcodes: below the minimum the body is entered with no
exit offered; at a spent bounded count the exit is the only continuation;
otherwise greediness orders body against exit. After each body match the
tail runs: on an unbounded repetition an iteration that consumed nothing
and satisfied the minimum ends the loop there, saves kept. -/
def searchRep (fuel : Nat) (c : SCtx) (body : Ast) (lo : Nat)
    (hi : Option Nat) (greedy : Bool) (cnt : Nat) (pos : Nat) (regs : Regs) :
    Option (List Thread) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let enter : Option (List Thread) := do
        let taken ← search fuel c body pos regs
        let onward ← taken.mapM fun t =>
          if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
            pure [t]
          else
            searchRep fuel c body lo hi greedy (cnt + 1) t.pos t.regs
        pure onward.flatten
      if cnt < lo then enter
      else if hi.any (cnt ≥ ·) then some [⟨pos, regs⟩]
      else do
        let taken ← enter
        pure (if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken)
termination_by (fuel, 1 + sizeOf body)

end

/-- The fuel S-3 promises: enough for every repetition round the search can
ever recurse through. Fuel is spent once per round, a round hands the next
one a fresh budget, and a round of an unbounded repetition either raises the
count toward the minimum or consumes a byte, so the need is additive:
rounds along one chain, plus whatever the body needs on top. -/
def suffFuel (n : Nat) : Ast → Nat
  | .cat kids => kids.attach.foldl (fun acc ⟨k, _⟩ => acc + suffFuel n k) 0
  | .alt arms => arms.attach.foldl (fun acc ⟨a, _⟩ => acc + suffFuel n a) 0
  | .grp _ body => suffFuel n body
  | .rep lo hi _ body =>
      let rounds := match hi with
        | some h => max lo h + 1
        | none => lo + n + 2
      rounds + suffFuel n body + 2
  | _ => 0

/-- What a whole match call answers, before resources enter the picture. -/
inductive MatchAnswer where
  | found (ovec : Array UInt32)
  | notFound
  | badInput
deriving DecidableEq, Repr, Inhabited

/-- The conservative can-a-match-start-on-CR analysis, on the AST: the pair
is (a first consumed byte can be CR, the walk can reach the far side without
consuming). The compiled twin is `scan_first`, whose conservative answers —
dot, \R and a reachable Accept are always a yes — are reproduced here so the
spec's bumpalong skips exactly the positions the engine skips. -/
def crWalk : Ast → Bool × Bool
  | .nul => (false, true)
  | .chr b => (b == 0x0D, false)
  | .chrCI folded => (folded == 0x0D, false)
  | .cls bits => (bits.has 0x0D, false)
  | .any | .anyNoNL | .bsr => (true, false)
  | .cat kids =>
      kids.attach.foldl
        (fun (acc : Bool × Bool) ⟨k, _⟩ =>
          let (cr, trans) := crWalk k
          (acc.1 || (acc.2 && cr), acc.2 && trans))
        (false, true)
  | .alt arms =>
      arms.attach.foldl
        (fun (acc : Bool × Bool) ⟨a, _⟩ =>
          let (cr, trans) := crWalk a
          (acc.1 || cr, acc.2 || trans))
        (false, false)
  | .grp _ body => crWalk body
  | .rep lo hi _ body =>
      match hi with
      | some 0 => (false, true)
      | some 1 =>
          let (cr, trans) := crWalk body
          if lo == 1 then (cr, trans) else (cr, true)
      | _ =>
          let (cr, trans) := crWalk body
          (cr, lo == 0 || trans)
  | _ => (false, true)

/-- Can a match's first consumed byte be a CR, conservatively: what the
bumpalong rule reads. A pattern that can accept without consuming is a yes,
the same answer `scan_first` gives a reachable Accept. -/
def _root_.Pcrevera.Pat.crFirst (p : Pat) : Bool :=
  let (cr, trans) := crWalk p.root
  cr || trans

/-- pcre2's bumpalong refusal: with a CRLF-aware convention, a pattern that
never spells CR or LF, and a possible CR start, no attempt begins between
the halves of a CR LF pair. Asked of every position after the first. -/
def skipsAttempt (p : Pat) (s : ByteArray) (pos : Nat) : Bool :=
  p.nltype.crlfish && !p.hascrlf && p.crFirst &&
    byteAt s (pos - 1) == 0x0D && pos < s.size && byteAt s pos == 0x0A

/-- The empty-match refusal at Accept, per attempt. -/
def acceptable (mo : MOpts) (start attempt : Nat) (t : Thread) : Bool :=
  !(t.pos == attempt &&
    (mo.notempty || (mo.notemptyAtStart && attempt == start)))

/-- The ENDANCHORED filter: generation plants an end-of-subject assertion
before Accept, so a surviving thread must end at the subject's end. -/
def endOk (p : Pat) (s : ByteArray) (t : Thread) : Bool :=
  !p.opts.endanchored || t.pos == s.size

/-- One attempt: every survivor of the search at this starting position, in
preference order. -/
def attemptThreads (fuel : Nat) (p : Pat) (s : ByteArray) (mo : MOpts)
    (start attempt : Nat) : Option (List Thread) := do
  let c : SCtx := ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩
  let fresh : Regs := Array.replicate (2 * (p.ncap + 1)) unset32
  let threads ← search fuel c p.root attempt fresh
  pure (threads.filter fun t =>
    acceptable mo start attempt t && endOk p s t)

/-- The scan: attempts from `start`, leftmost first, the bumpalong skips
applied, stopping at the first attempt with a survivor. `steps` only bounds
the loop the way the engine's own variant does; `s.size + 1 - start` is
always enough. -/
def scan (fuel : Nat) (p : Pat) (s : ByteArray) (mo : MOpts) (start : Nat) :
    Nat → Nat → Option MatchAnswer
  | _, 0 => none
  | attempt, steps + 1 => do
      let survivors ← attemptThreads fuel p s mo start attempt
      match survivors with
      | t :: _ =>
          pure (.found ((t.regs.set! 0 attempt.toUInt32).set! 1 t.pos.toUInt32))
      | [] =>
          if p.opts.anchored || mo.anchored || attempt ≥ s.size then
            pure .notFound
          else
            let next := attempt + 1
            scan fuel p s mo start
              (if skipsAttempt p s next then next + 1 else next) steps

/-- S-2's fuel-indexed reading of the whole call: BadInput exactly for a
start offset outside the subject or a subject past the documented cap, and
otherwise the scan. -/
def matchesF (fuel : Nat) (p : Pat) (s : ByteArray) (start : Nat)
    (mo : MOpts) : Option MatchAnswer :=
  if start > s.size || s.size > ceiling then some .badInput
  else scan fuel p s mo start start (s.size + 1 - start)

end Pcrevera.Spec
