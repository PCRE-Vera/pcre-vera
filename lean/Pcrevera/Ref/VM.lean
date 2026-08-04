import Pcrevera.Ref.Compile

/-!
# The backtracking VM (R-2, the complete engine)

`engine/vm.py`'s `bt_run`, restated: depth-first over an explicit stack of
(pc, position, undo mark), every instruction visit charged, every push
checked, growth charged before it happens, undo replay charged per register
byte. The accounting is the whole point — the conformance corpora hold this
function to the engine's recorded `Usage` to the unit — so every charge
appears here exactly where the engine makes it, and in the same order,
because a budget refusal partway through leaves the earlier charges made.

The two growing arrays carry their capacity beside their contents: TIR's
growth schedule (double from four, clamp at the declared maximum, reserve
sets exactly) is what `charge_grow` prices, and a preallocated context hands
this function pre-reserved capacities so a push under the reservation never
charges anything.

The inner loop is written on fuel of `costlimit + 1 - cost`: every
iteration either stops or charges at least one unit after checking the
budget, so cost never passes the limit and the fuel-exhausted branch is
unreachable — R-5's termination argument, made structural.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- One backtrack entry: where to resume and how much trail to replay. -/
structure BtEntry where
  pc : Nat
  pos : Nat
  mark : Nat
deriving Repr, Inhabited

/-- One undo entry: the register a failed path overwrote. -/
structure Undo where
  slot : Nat
  old : UInt32
deriving Repr, Inhabited

/-- The accounting triple the run threads everywhere. -/
structure Meter where
  cost : Nat
  mem : Nat
  peak : Nat
deriving Repr

/-- `charge_grow`: price a growth step before it happens. Answers the new
capacity, or refuses — the caller turns a refusal into ResourceExceeded.
Both buffers are charged as memory while the copy is in flight, and every
byte zeroed or copied is a cost unit. -/
def chargeGrow (oldcap len esize maxv : Nat) (m : Meter) (lim : Limits) :
    Option (Meter × Nat) :=
  if len < oldcap then some (m, oldcap)
  else if len ≥ maxv then none
  else
    let newcap := min maxv (max growMin (oldcap * growFactor))
    let taken := newcap * esize
    let held := oldcap * esize
    if taken > lim.mem - m.mem then none
    else
      let work := taken + held
      if work > lim.cost - m.cost then none
      else
        let total := m.mem + taken
        some ({ cost := m.cost + work
                mem := total - held
                peak := max m.peak total }, newcap)

/-- The mutable half of a backtracking run. -/
structure BtSt where
  regs : Array UInt32
  bt : Array BtEntry
  btCap : Nat
  trail : Array Undo
  trailCap : Nat
  m : Meter
  stackpeak : Nat

/-- `write_reg`: an undo entry while there is anything to backtrack to,
growth-checked, then the write. -/
def writeReg (st : BtSt) (lim : Limits) (slot : Nat) (value : UInt32) :
    Option BtSt :=
  if st.bt.size > 0 then
    match chargeGrow st.trailCap st.trail.size undoSize maxTrail st.m lim with
    | none => none
    | some (m, cap) =>
        some { st with
          m, trailCap := cap
          trail := st.trail.push ⟨slot, st.regs[slot]!⟩
          regs := st.regs.set! slot value }
  else some { st with regs := st.regs.set! slot value }

/-- `push_bt`: the stack limit first, then growth, then the entry. -/
def pushBt (st : BtSt) (lim : Limits) (pc pos mark : Nat) : Option BtSt :=
  if st.bt.size ≥ lim.stack then none
  else
    match chargeGrow st.btCap st.bt.size btSize maxStack st.m lim with
    | none => none
    | some (m, cap) =>
        some { st with m, btCap := cap, bt := st.bt.push ⟨pc, pos, mark⟩ }

/-- `fork`: a backtrack entry at the current trail mark, the stack peak
noted on success. -/
def fork (st : BtSt) (lim : Limits) (target pos : Nat) : Option BtSt :=
  match pushBt st lim target pos st.trail.size with
  | none => none
  | some st => some { st with stackpeak := max st.stackpeak st.bt.size }

/-- How one attempt ended. -/
inductive AttemptOut where
  | found (endPos : Nat) (st : BtSt)
  | exhausted (st : BtSt)
  | exceeded (st : BtSt)

/-- Replay the trail down to `mark`, restoring registers. -/
def replayTrail (trail : Array Undo) (regs : Array UInt32) (mark : Nat) :
    Array Undo × Array UInt32 :=
  if trail.size ≤ mark then (trail, regs)
  else
    let undo := trail.back!
    replayTrail trail.pop (regs.set! undo.slot undo.old) mark
termination_by trail.size

mutual

/-- The instruction loop of one attempt. Fuel is `costlimit + 1 - cost`:
each iteration charges at least one unit or returns, and no charge passes
the limit, so fuel cannot run dry before the budget does. -/
def btStep (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start attempt : Nat) (fuel : Nat) (pc pos : Nat) (st : BtSt) :
    AttemptOut :=
  match fuel with
  | 0 => .exceeded st
  | fuel + 1 =>
    if st.m.cost ≥ lim.cost then .exceeded st
    else
    let st := { st with m := { st.m with cost := st.m.cost + 1 } }
    let n := s.size
    let regbase := re.novec
    let inst := re.code[pc]!
    -- A consuming test, an assertion, or a failure to hand to the stack.
    let step := fun (test : Bool) (len : Nat) =>
      if pos < n && test then btStep re s mo lim start attempt fuel (pc + 1) (pos + len) st
      else btFail re s mo lim start attempt fuel st
    let holds := fun (test : Bool) =>
      if test then btStep re s mo lim start attempt fuel (pc + 1) pos st
      else btFail re s mo lim start attempt fuel st
    let save := fun (slot : Nat) (value : UInt32) =>
      match writeReg st lim slot value with
      | none => .exceeded st
      | some st => btStep re s mo lim start attempt fuel (pc + 1) pos st
    match inst.op with
    | .chr => step (byteAt s pos == UInt8.ofNat inst.arg) 1
    | .chrCI => step (lowerByte (byteAt s pos) == UInt8.ofNat inst.arg) 1
    | .cls => step (pos < n && re.classHas inst.arg (byteAt s pos)) 1
    | .any => step true 1
    | .anyNoNL => step (newlineAt s pos re.nltype == 0) 1
    | .bsr =>
        let eaten := bsrAt s pos re.bsrtype
        if eaten != 0 then
          btStep re s mo lim start attempt fuel (pc + 1) (pos + eaten) st
        else btFail re s mo lim start attempt fuel st
    | .split =>
        match fork st lim inst.alt pos with
        | none => .exceeded st
        | some st => btStep re s mo lim start attempt fuel inst.arg pos st
    | .jump => btStep re s mo lim start attempt fuel inst.arg pos st
    | .save =>
        match writeReg st lim inst.arg pos.toUInt32 with
        | none => .exceeded st
        | some st => btStep re s mo lim start attempt fuel (pc + 1) pos st
    | .circ => holds (pos == 0 && !mo.notbol)
    | .circM =>
        holds (if pos == 0 then !mo.notbol
               else pos != n && newlineBefore s pos re.nltype != 0)
    | .doll => holds (!mo.noteol && atLineEnd s pos re.nltype)
    | .dollE => holds (!mo.noteol && pos == n)
    | .dollM =>
        holds (if pos < n then newlineAt s pos re.nltype != 0 else !mo.noteol)
    | .sod => holds (pos == 0)
    | .eod => holds (pos == n)
    | .eodn => holds (atLineEnd s pos re.nltype)
    | .wordB => holds (wordEdge s pos)
    | .notWordB => holds (!wordEdge s pos)
    | .repZero => save (regbase + inst.arg * 2) 0
    | .repEnter => save (regbase + inst.arg * 2 + 1) pos.toUInt32
    | .repLoop =>
        let rep := re.reps[inst.arg]!
        let cnt := (st.regs[regbase + inst.arg * 2]!).toNat
        if cnt < rep.lo then
          btStep re s mo lim start attempt fuel rep.body pos st
        else if cnt ≥ rep.hi then
          btStep re s mo lim start attempt fuel rep.after pos st
        else
          let (first, second) :=
            if rep.greedy then (rep.body, rep.after) else (rep.after, rep.body)
          match fork st lim second pos with
          | none => .exceeded st
          | some st => btStep re s mo lim start attempt fuel first pos st
    | .repNext =>
        let rep := re.reps[inst.arg]!
        let slot := regbase + inst.arg * 2
        let cnt := st.regs[slot]! + 1
        let entered := st.regs[slot + 1]!
        match writeReg st lim slot cnt with
        | none => .exceeded st
        | some st =>
            if rep.hi == none32 && pos.toUInt32 == entered
                && cnt.toNat ≥ rep.lo then
              btStep re s mo lim start attempt fuel rep.after pos st
            else
              btStep re s mo lim start attempt fuel rep.head pos st
    | .accept =>
        let empty := pos == attempt
        let refuse := empty &&
          (mo.notempty || (mo.notemptyAtStart && attempt == start))
        if refuse then btFail re s mo lim start attempt fuel st
        else
          let st := { st with regs :=
            (st.regs.set! 0 attempt.toUInt32).set! 1 pos.toUInt32 }
          .found pos st
termination_by (fuel, 0)

/-- A failed path: backtrack if there is anywhere to go, replay charged
first, the trail let go once nothing holds a mark into it. -/
def btFail (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start attempt : Nat) (fuel : Nat) (st : BtSt) : AttemptOut :=
  if h : st.bt.size = 0 then
    .exhausted { st with trail := #[] }
  else
    let entry := st.bt.back!
    let st := { st with bt := st.bt.pop }
    let replay := (st.trail.size - entry.mark) * regSize
    if replay > lim.cost - st.m.cost then .exceeded st
    else
      let st := { st with m := { st.m with cost := st.m.cost + replay } }
      let (trail, regs) := replayTrail st.trail st.regs entry.mark
      let st := { st with trail, regs }
      let st := if st.bt.size == 0 then { st with trail := #[] } else st
      btStep re s mo lim start attempt fuel entry.pc entry.pos st
termination_by (fuel, 1)

end

/-- How the whole call ended, before delivery. -/
inductive RunEnd where
  | matched (st : BtSt)
  | noMatch (st : BtSt)
  | exceeded (st : BtSt)

/-- The bumpalong refusal, read off the compiled pattern's own fields. -/
def Re.skipsAttempt (re : Re) (s : ByteArray) (pos : Nat) : Bool :=
  re.nltype.crlfish && !re.hascrlf && re.crfirst &&
    byteAt s (pos - 1) == 0x0D && pos < s.size && byteAt s pos == 0x0A

/-- The attempt loop: registers cleared and charged per starting position,
both scratch arrays truncated capacity-in-hand, the bumpalong rule applied
on the way forward. `steps` mirrors the engine's loop variant; the subject
length always covers it. -/
def btLoop (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) : Nat → Nat → BtSt → RunEnd
  | 0, _, st => .exceeded st
  | steps + 1, attempt, st =>
      let reset := re.nregs * regSize
      if reset > lim.cost - st.m.cost then .exceeded st
      else
        let st := { st with
          m := { st.m with cost := st.m.cost + reset }
          regs := Array.replicate re.nregs unset32
          bt := #[], trail := #[] }
        match btStep re s mo lim start attempt (lim.cost + 1 - st.m.cost)
            0 attempt st with
        | .found _ st => .matched st
        | .exceeded st => .exceeded st
        | .exhausted st =>
            if re.anchored || mo.anchored || attempt ≥ s.size then .noMatch st
            else
              let next := attempt + 1
              let next := if re.skipsAttempt s next then next + 1 else next
              btLoop re s mo lim start steps next st

/-- What a run used, read off its state. -/
def BtSt.usage (st : BtSt) : Usage :=
  { cost := st.m.cost, stack := st.stackpeak, mem := st.m.peak }

/-- `bt_run`: the whole backtracking call. A preallocated context hands in
its reserved capacities; the plain path starts from nothing. Setup is
charged as cost and memory at once; a match pays for delivering its own
answer. -/
def btRun (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) (btCap trailCap : Nat) : RunResult :=
  if start > s.size then ⟨.badInput, #[], {}⟩
  else
    let novec := re.novec
    let setup := (re.nregs + novec) * regSize
    if setup > lim.mem || setup > lim.cost then ⟨.resourceExceeded, #[], {}⟩
    else
      let st : BtSt :=
        { regs := Array.replicate re.nregs unset32
          bt := #[], btCap
          trail := #[], trailCap
          m := ⟨setup, setup, setup⟩
          stackpeak := 0 }
      match btLoop re s mo lim start (s.size + 1 - start) start st with
      | .matched st =>
          let deliver := novec * regSize
          if deliver > lim.cost - st.m.cost then
            ⟨.resourceExceeded, #[], st.usage⟩
          else
            let st := { st with m := { st.m with cost := st.m.cost + deliver } }
            ⟨.matched, st.regs.extract 0 novec, st.usage⟩
      | .noMatch st => ⟨.noMatch, #[], st.usage⟩
      | .exceeded st => ⟨.resourceExceeded, #[], st.usage⟩

end Pcrevera.Ref
