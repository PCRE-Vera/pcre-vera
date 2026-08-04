import Pcrevera.Ref.Bytecode
import Pcrevera.Spec.Match

/-!
# R.compile (R-1)

The bytecode compiler of `engine/compiler.py`, restated as a recursion over
the AST. The engine walks an explicit job stack because TIR has no
recursion; the walk visits constructs in source order and revisits each one
to patch and close, which is exactly what a recursive emitter does, so the
two produce the same instructions, the same repetition table and the same
region table in the same order — and the conformance corpora hold this
compiler to the engine's output byte for byte.

The engine's PatternTooLarge checks during generation are not restated:
every one of them is unreachable for parser output, whose node, repetition
and register counts the parse-time limits already bound (spec.py sizes
MAX_CODE and friends so that codegen cannot hit them). This compiler is
total instead, and the theorems that need parser-shaped input say so
through `Pat.Wf`.

`scan_first` and `pike_ok` close compilation the way `generate` and
`pike_ok` do in the engine: the bumpalong bit and the Pike routing are
facts about the finished bytecode.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- Codegen state: the four tables under construction. -/
structure CState where
  code : Array Inst := #[]
  classes : Array UInt8 := #[]
  reps : Array RepInfo := #[]
  regions : Array Region := #[]

private def emit (st : CState) (i : Inst) : CState × Nat :=
  ({ st with code := st.code.push i }, st.code.size)

private def openRegion (st : CState) (kind : Rk) (parent : Nat) :
    CState × Nat :=
  let opened : Region := ⟨kind, parent, st.code.size, st.code.size⟩
  ({ st with regions := st.regions.push opened }, st.regions.size)

private def closeRegion (st : CState) (at_ : Nat) : CState :=
  let done := st.regions.modify at_ (fun r => { r with hi := st.code.size })
  { st with regions := done }

/-- A construct that compiled to nothing prices nothing: its region is still
on top of the table and is taken back off, like the engine's
`drop_empty_region`. -/
private def dropEmptyRegion (st : CState) (at_ : Nat) : CState :=
  if h : at_ < st.regions.size then
    if st.regions[at_].lo == st.code.size then
      { st with regions := st.regions.pop }
    else st
  else st

private def patch (st : CState) (pc : Nat) (f : Inst → Inst) : CState :=
  { st with code := st.code.modify pc f }

mutual

/-- One node, emitted into the region `here`. -/
def compileNode (a : Ast) (here : Nat) (st : CState) : CState :=
  match a with
  | .nul => st
  | .chr b => (emit st ⟨.chr, b.toNat, 0⟩).1
  | .chrCI folded => (emit st ⟨.chrCI, folded.toNat, 0⟩).1
  | .cls bits =>
      let idx := st.classes.size / 32
      let st := { st with classes := st.classes ++ bits.toArray }
      (emit st ⟨.cls, idx, 0⟩).1
  | .any => (emit st ⟨.any, 0, 0⟩).1
  | .anyNoNL => (emit st ⟨.anyNoNL, 0, 0⟩).1
  | .bsr => (emit st ⟨.bsr, 0, 0⟩).1
  | .circ => (emit st ⟨.circ, 0, 0⟩).1
  | .circM => (emit st ⟨.circM, 0, 0⟩).1
  | .doll => (emit st ⟨.doll, 0, 0⟩).1
  | .dollE => (emit st ⟨.dollE, 0, 0⟩).1
  | .dollM => (emit st ⟨.dollM, 0, 0⟩).1
  | .sod => (emit st ⟨.sod, 0, 0⟩).1
  | .eod => (emit st ⟨.eod, 0, 0⟩).1
  | .eodn => (emit st ⟨.eodn, 0, 0⟩).1
  | .wordB => (emit st ⟨.wordB, 0, 0⟩).1
  | .notWordB => (emit st ⟨.notWordB, 0, 0⟩).1
  | .cat kids => compileCat kids here st
  | .alt arms =>
      match arms with
      | [] => st
      | [only] => compileNode only here st
      | first :: rest =>
          -- The alternation opens before its first split goes.
          let (st, inside) := openRegion st .alt here
          let st := compileAlt first rest inside #[] st
          closeRegion st inside
  | .grp cap body =>
      let (st, mine) := openRegion st .group here
      let st := if cap != 0 then (emit st ⟨.save, 2 * cap, 0⟩).1 else st
      let st := compileNode body mine st
      let st := if cap != 0 then (emit st ⟨.save, 2 * cap + 1, 0⟩).1 else st
      dropEmptyRegion (closeRegion st mine) mine
  | .rep lo hi greedy body =>
      match hi with
      | some 0 => st
      | some 1 =>
          if lo == 1 then compileNode body here st
          else
            -- The optional item: one split, arms by greediness.
            let (st, mine) := openRegion st .«repeat» here
            let (st, sp) := emit st ⟨.split, 0, 0⟩
            let st := compileNode body mine st
            let stop := st.code.size
            let st := patch st sp fun i =>
              if greedy then { i with arg := sp + 1, alt := stop }
              else { i with arg := stop, alt := sp + 1 }
            closeRegion st mine
      | _ =>
          let (st, mine) := openRegion st .«repeat» here
          let r := st.reps.size
          let hi' := match hi with | some h => h | none => none32
          let (st, _) := emit st ⟨.repZero, r, 0⟩
          let (st, head) := emit st ⟨.repLoop, r, 0⟩
          let (st, _) := emit st ⟨.repEnter, r, 0⟩
          let entry : RepInfo := ⟨lo, hi', greedy, head, head + 1, 0⟩
          let st := { st with reps := st.reps.push entry }
          let st := compileNode body mine st
          let (st, _) := emit st ⟨.repNext, r, 0⟩
          let fixed := st.reps.modify r
              (fun rr => { rr with after := st.code.size })
          let st := { st with reps := fixed }
          closeRegion st mine
termination_by (sizeOf a, 0)

def compileCat (kids : List Ast) (here : Nat) (st : CState) : CState :=
  match kids with
  | [] => st
  | k :: rest => compileCat rest here (compileNode k here st)
termination_by (sizeOf kids, 1)

/-- The split-branch-jump chain: every branch but the last is guarded by a
split whose second arm is the next link, every branch but the last leaves
by a jump patched to the end, and each branch's region excludes its own
jump, exactly as `walk_alt` lays it out. -/
def compileAlt (arm : Ast) (rest : List Ast) (inside : Nat)
    (jumps : Array Nat) (st : CState) : CState :=
  match rest with
  | [] =>
      let (st, opened) := openRegion st .branch inside
      let st := compileNode arm opened st
      let stop := st.code.size
      let st := jumps.foldl (fun st pc =>
        patch st pc fun i => { i with arg := stop }) st
      closeRegion st opened
  | next :: rest' =>
      let (st, sp) := emit st ⟨.split, 0, 0⟩
      let st := patch st sp fun i => { i with arg := sp + 1 }
      let (st, opened) := openRegion st .branch inside
      let st := compileNode arm opened st
      let st := closeRegion st opened
      let (st, jp) := emit st ⟨.jump, 0, 0⟩
      let st := patch st sp fun i => { i with alt := st.code.size }
      compileAlt next rest' inside (jumps.push jp) st
termination_by (sizeOf arm + sizeOf rest, 2)

end

/-- Mark a pc as pending if it is in range and new: `mark_seen`. -/
def markSeen (code : Array Inst) (seen : Array Bool) (pending : List Nat)
    (pc : Nat) : Array Bool × List Nat :=
  if pc ≥ code.size then (seen, pending)
  else if seen[pc]! then (seen, pending)
  else (seen.set! pc true, pc :: pending)

/-- Can a match begin by consuming a CR? `scan_first`, the worklist over the
non-consuming transitions, conservative answers included: dot, \R and a
reachable Accept are a yes, and so is running out of fuel, which marking
each pc at most once makes unreachable. -/
def scanFirst (code : Array Inst) (classes : Array UInt8)
    (reps : Array RepInfo) : Bool :=
  go (2 * code.size + 2) ((markSeen code (Array.replicate code.size false) [] 0))
where
  go (fuel : Nat) : Array Bool × List Nat → Bool
    | (_, []) => false
    | (seen, pc :: pending) =>
        match fuel with
        | 0 => true
        | fuel + 1 =>
            let inst := code[pc]!
            let mark := fun st pc' => markSeen code st.1 st.2 pc'
            match inst.op with
            | .chr | .chrCI => inst.arg == 0x0D || go fuel (seen, pending)
            | .cls =>
                (classes[inst.arg * 32 + 1]! &&& 0x20 != 0) ||
                  go fuel (seen, pending)
            | .any | .anyNoNL | .bsr | .accept => true
            | .split =>
                go fuel (mark (mark (seen, pending) inst.arg) inst.alt)
            | .jump => go fuel (mark (seen, pending) inst.arg)
            | .repLoop =>
                let rep := reps[inst.arg]!
                let st := mark (seen, pending) rep.body
                go fuel (if rep.lo == 0 then mark st rep.after else st)
            | .repNext =>
                let rep := reps[inst.arg]!
                go fuel (mark (mark (seen, pending) rep.head) rep.after)
            | _ => go fuel (mark (seen, pending) (pc + 1))

/-- Whether one repetition's body can complete an iteration without
consuming: `pike_hollow`, the worklist toward the repetition's own RepNext.
The conservative direction is a yes — a hollow verdict only costs the
pattern its Pike routing — and that is also the fuel fallback. -/
def pikeHollow (code : Array Inst) (reps : Array RepInfo) (which : Nat) :
    Bool :=
  go (2 * code.size + 2) (Array.replicate code.size false) [(reps[which]!).body]
where
  go (fuel : Nat) (seen : Array Bool) : List Nat → Bool
    | [] => false
    | pc :: pending =>
        match fuel with
        | 0 => true
        | fuel + 1 =>
            if pc ≥ code.size then true
            else if pc == (reps[which]!).after - 1 then true
            else if seen[pc]! then go fuel seen pending
            else
              let seen := seen.set! pc true
              let inst := code[pc]!
              match inst.op with
              | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .accept =>
                  go fuel seen pending
              | .split => go fuel seen (inst.alt :: inst.arg :: pending)
              | .jump => go fuel seen (inst.arg :: pending)
              | .repLoop =>
                  let inner := reps[inst.arg]!
                  go fuel seen (inner.after :: inner.body :: pending)
              | .repNext =>
                  let inner := reps[inst.arg]!
                  go fuel seen (inner.after :: inner.head :: pending)
              | _ => go fuel seen ((pc + 1) :: pending)

/-- May the Pike VM run this program? `pike_ok`: every repetition a pure
star whose body cannot complete emptily, and no \R anywhere. -/
def pikeOk (code : Array Inst) (reps : Array RepInfo) : Bool :=
  (List.range reps.size).all (fun i =>
    let r := reps[i]!
    r.lo == 0 && r.hi == none32 && !pikeHollow code reps i) &&
  code.all (fun i => i.op != .bsr)

/-- R.compile: parse output to compiled pattern, `compile`'s codegen half.
The pattern-level facts — capture count, register count, the bumpalong bit,
Pike eligibility — are computed exactly where the engine computes them. -/
def compile (p : Pat) : Re :=
  let (st, whole) := openRegion {} .root none32
  let st := compileNode p.root whole st
  let st := if p.opts.endanchored then (emit st ⟨.eod, 0, 0⟩).1 else st
  let (st, _) := emit st ⟨.accept, 0, 0⟩
  let st := closeRegion st whole
  let ncap := p.root.maxGroup
  { code := st.code
    classes := st.classes
    reps := st.reps
    regions := st.regions
    ncap := ncap
    nregs := (ncap + 1) * 2 + st.reps.size * 2
    anchored := p.opts.anchored
    endanchored := p.opts.endanchored
    nltype := p.nltype
    bsrtype := p.bsrtype
    hascrlf := p.hascrlf
    crfirst := scanFirst st.code st.classes st.reps
    pike := pikeOk st.code st.reps }

end Pcrevera.Ref
