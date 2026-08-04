import Pcrevera.Ref.VM

/-!
# The Pike VM (R-2, the lockstep matcher)

`engine/pike.py`'s `pike_run`: one pass over the subject, a priority-ordered
thread list per position, the epsilon closure expanded depth-first in split
order, captures in a pooled copy-on-write block store. Cost, memory and the
copy-on-write charges follow the engine to the unit, which is why the
helpers here hand back their partially-charged state when a budget refuses
them: the engine accumulates charges through inout parameters, so a closure
that dies halfway leaves what it already charged on the meter, and the
recorded `Usage` in the corpora proves it.

The closure loop runs on fuel of `2 * code.size + 2`: each iteration either
marks an unseen pc (at most `code.size` marks, two continuations each) or
pops a seen one, so the worklist drains within that bound and the fallback
is unreachable — the same argument the engine's declared loop variant makes.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- One suspended thread: a pc and a capture-block handle. -/
structure Th where
  pc : Nat
  h : Nat
deriving Repr, Inhabited

/-- The engine's declared maxima for the Pike scratch (spec.py): the growth
schedule's final capacity over each array's semantic entry bound. -/
def maxNodes : Nat := 2 * 4096 + 16
def maxCode : Nat := 4 * maxNodes + 16
def maxOvec : Nat := 2 * (255 + 1)
def liveBlocks : Nat := 4 * maxCode + 4
def maxThreads : Nat := growMin + growFactor * maxCode
def maxClosure : Nat := growMin + growFactor * (2 * maxCode)
def maxBlocks : Nat := growMin + growFactor * liveBlocks
def maxPool : Nat := growMin + growFactor * (liveBlocks * maxOvec)

/-- The mutable half of a Pike run: the two thread lists, the closure
stack, the visited set, the copy-on-write tables, and the meter. Every
grown array carries its capacity, because a context hands them over
pre-reserved and a push under the reservation charges nothing. -/
structure PikeSt where
  clist : Array Th := #[]
  clistCap : Nat := 0
  nlist : Array Th := #[]
  nlistCap : Nat := 0
  stk : Array Th := #[]
  stkCap : Nat := 0
  seen : Array Bool := #[]
  pool : Array UInt32 := #[]
  poolCap : Nat := 0
  rc : Array Nat := #[]
  rcCap : Nat := 0
  free : Array Nat := #[]
  freeCap : Nat := 0
  m : Meter := ⟨0, 0, 0⟩

/-- A step that can blow the budget keeps its partial charges: `ok` carries
the new state, `blown` the state as far as the charges got. -/
abbrev POut (α : Type) := Except PikeSt α

/-- `pike_take`: a block off the free list, or a fresh one, growth charged.
Answers the handle; a table at its declared maximum refuses. -/
def pikeTake (st : PikeSt) (novec : Nat) (lim : Limits) :
    POut (PikeSt × Nat) :=
  if st.free.size > 0 then
    let h := st.free.back!
    .ok ({ st with free := st.free.pop, rc := st.rc.set! h 1 }, h)
  else
    let h := st.rc.size
    if h ≥ maxBlocks then .error st
    else
      match chargeGrow st.rcCap st.rc.size regSize maxBlocks st.m lim with
      | none => .error st
      | some (m, rcCap) =>
          let st := { st with m, rcCap, rc := st.rc.push 1 }
          let rec fill (k : Nat) (st : PikeSt) : POut PikeSt :=
            match k with
            | 0 => .ok st
            | k + 1 =>
                match chargeGrow st.poolCap st.pool.size regSize maxPool
                    st.m lim with
                | none => .error st
                | some (m, poolCap) =>
                    fill k
                      { st with m, poolCap, pool := st.pool.push unset32 }
          match fill novec st with
          | .error st => .error st
          | .ok st => .ok (st, h)

/-- `pike_drop`: one reference down, the block freed at zero. -/
def pikeDrop (st : PikeSt) (h : Nat) (lim : Limits) : POut PikeSt :=
  if h == none32 then .ok st
  else
    let left := st.rc[h]! - 1
    let st := { st with rc := st.rc.set! h left }
    if left == 0 then
      match chargeGrow st.freeCap st.free.size regSize maxBlocks st.m lim with
      | none => .error st
      | some (m, freeCap) =>
          .ok { st with m, freeCap, free := st.free.push h }
    else .ok st

/-- `pike_write`: copy-on-write through a handle, the copy charged per
slot, then the write. Answers the possibly-fresh handle. -/
def pikeWrite (st : PikeSt) (novec h slot : Nat) (value : UInt32)
    (lim : Limits) : POut (PikeSt × Nat) :=
  if st.rc[h]! > 1 then
    let copied := novec * regSize
    if copied > lim.cost - st.m.cost then .error st
    else
      let st := { st with m := { st.m with cost := st.m.cost + copied } }
      match pikeTake st novec lim with
      | .error st => .error st
      | .ok (st, fresh) =>
          let taken := fresh * novec
          let held := h * novec
          let pool := (List.range novec).foldl
            (fun (pool : Array UInt32) k =>
              pool.set! (taken + k) pool[held + k]!) st.pool
          let st := { st with pool, rc := st.rc.set! h (st.rc[h]! - 1) }
          let pool := st.pool.set! (fresh * novec + slot) value
          .ok ({ st with pool }, fresh)
  else
    .ok ({ st with pool := st.pool.set! (h * novec + slot) value }, h)

/-- One growth-checked push onto the closure stack: `pike_defer`. -/
def pikeDefer (st : PikeSt) (pc h : Nat) (lim : Limits) : POut PikeSt :=
  match chargeGrow st.stkCap st.stk.size thSize maxClosure st.m lim with
  | none => .error st
  | some (m, stkCap) =>
      .ok { st with m, stkCap, stk := st.stk.push ⟨pc, h⟩ }

/-- And onto the next thread list: `pike_park`. -/
def pikePark (st : PikeSt) (intoNext : Bool) (pc h : Nat) (lim : Limits) :
    POut PikeSt :=
  if intoNext then
    match chargeGrow st.nlistCap st.nlist.size thSize maxThreads st.m lim with
    | none => .error st
    | some (m, nlistCap) =>
        .ok { st with m, nlistCap, nlist := st.nlist.push ⟨pc, h⟩ }
  else
    match chargeGrow st.clistCap st.clist.size thSize maxThreads st.m lim with
    | none => .error st
    | some (m, clistCap) =>
        .ok { st with m, clistCap, clist := st.clist.push ⟨pc, h⟩ }

/-- The epsilon closure, `pike_add`: expand from one thread, depth-first in
split order, parking suspensions in priority order, the visited set
admitting each pc once per list build. -/
def pikeAdd (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (intoNext : Bool) (pos : Nat) (pc0 h0 : Nat) (st : PikeSt) :
    POut PikeSt :=
  match pikeDefer st pc0 h0 lim with
  | .error st => .error st
  | .ok st => go (2 * re.code.size + 2) st
where
  go (fuel : Nat) (st : PikeSt) : POut PikeSt :=
    match fuel with
    | 0 => .error st
    | fuel + 1 =>
        if st.stk.size == 0 then .ok st
        else
          let th := st.stk.back!
          let st := { st with stk := st.stk.pop }
          let pc := th.pc
          let h := th.h
          let novec := re.novec
          let n := s.size
          if st.seen[pc]! then
            match pikeDrop st h lim with
            | .error st => .error st
            | .ok st => go fuel st
          else
            let st := { st with seen := st.seen.set! pc true }
            if 1 > lim.cost - st.m.cost then .error st
            else
              let st := { st with m := { st.m with cost := st.m.cost + 1 } }
              let inst := re.code[pc]!
              let hold := fun (test : Bool) =>
                if test then
                  match pikeDefer st (pc + 1) h lim with
                  | .error st => .error st
                  | .ok st => go fuel st
                else
                  match pikeDrop st h lim with
                  | .error st => .error st
                  | .ok st => go fuel st
              let forkTo := fun (first second : Nat) =>
                let st := { st with rc := st.rc.set! h (st.rc[h]! + 1) }
                match pikeDefer st second h lim with
                | .error st => .error st
                | .ok st =>
                    match pikeDefer st first h lim with
                    | .error st => .error st
                    | .ok st => go fuel st
              match inst.op with
              | .chr | .chrCI | .cls | .any | .anyNoNL | .accept =>
                  match pikePark st intoNext pc h lim with
                  | .error st => .error st
                  | .ok st => go fuel st
              | .bsr =>
                  match pikeDrop st h lim with
                  | .error st => .error st
                  | .ok st => go fuel st
              | .split => forkTo inst.arg inst.alt
              | .jump =>
                  match pikeDefer st inst.arg h lim with
                  | .error st => .error st
                  | .ok st => go fuel st
              | .save =>
                  match pikeWrite st novec h inst.arg pos.toUInt32 lim with
                  | .error st => .error st
                  | .ok (st, h') =>
                      match pikeDefer st (pc + 1) h' lim with
                      | .error st => .error st
                      | .ok st => go fuel st
              | .circ => hold (pos == 0 && !mo.notbol)
              | .circM =>
                  hold (if pos == 0 then !mo.notbol
                        else pos != n && newlineBefore s pos re.nltype != 0)
              | .doll => hold (!mo.noteol && atLineEnd s pos re.nltype)
              | .dollE => hold (!mo.noteol && pos == n)
              | .dollM =>
                  hold (if pos < n then newlineAt s pos re.nltype != 0
                        else !mo.noteol)
              | .sod => hold (pos == 0)
              | .eod => hold (pos == n)
              | .eodn => hold (atLineEnd s pos re.nltype)
              | .wordB => hold (wordEdge s pos)
              | .notWordB => hold (!wordEdge s pos)
              | .repZero | .repEnter =>
                  match pikeDefer st (pc + 1) h lim with
                  | .error st => .error st
                  | .ok st => go fuel st
              | .repLoop | .repNext =>
                  let rep := re.reps[inst.arg]!
                  if rep.greedy then forkTo rep.body rep.after
                  else forkTo rep.after rep.body

/-- Drop the handles of every thread a recorded match outranks. -/
def dropRest (lim : Limits) (rest : List Th) (st : PikeSt) : POut PikeSt :=
  match rest with
  | [] => .ok st
  | th :: rest =>
      match pikeDrop st th.h lim with
      | .error st => .error st
      | .ok st => dropRest lim rest st

/-- What stepping one list leaves behind: the state, the recorded match
handle, whether seeding continues, and whether a match is on record. -/
structure StepOut where
  st : PikeSt
  mh : Nat
  seeding : Bool
  matched : Bool

/-- Step the built list in priority order: consuming survivors close over
into the next list, an accepting thread records its match and kills
everything below it. -/
def stepThreads (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start pos : Nat) (threads : List Th) (st : PikeSt) (mh : Nat)
    (seeding matched : Bool) : POut StepOut :=
  match threads with
  | [] => .ok ⟨st, mh, seeding, matched⟩
  | th :: rest =>
      if 1 > lim.cost - st.m.cost then .error st
      else
        let st := { st with m := { st.m with cost := st.m.cost + 1 } }
        let n := s.size
        let novec := re.novec
        let inst := re.code[th.pc]!
        let onward := fun (test : Bool) =>
          if pos < n && test then
            match pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h st with
            | .error st => .error st
            | .ok st => stepThreads re s mo lim start pos rest st mh seeding matched
          else
            match pikeDrop st th.h lim with
            | .error st => .error st
            | .ok st => stepThreads re s mo lim start pos rest st mh seeding matched
        match inst.op with
        | .chr => onward (byteAt s pos == UInt8.ofNat inst.arg)
        | .chrCI => onward (lowerByte (byteAt s pos) == UInt8.ofNat inst.arg)
        | .cls => onward (pos < n && re.classHas inst.arg (byteAt s pos))
        | .any => onward true
        | .anyNoNL => onward (newlineAt s pos re.nltype == 0)
        | .accept =>
            let began := st.pool[th.h * novec]!
            let empty := began == pos.toUInt32
            let refuse := empty &&
              (mo.notempty || (mo.notemptyAtStart && began == start.toUInt32))
            if refuse then
              match pikeDrop st th.h lim with
              | .error st => .error st
              | .ok st => stepThreads re s mo lim start pos rest st mh seeding matched
            else
              match pikeWrite st novec th.h 1 pos.toUInt32 lim with
              | .error st => .error st
              | .ok (st, hv) =>
                  match pikeDrop st mh lim with
                  | .error st => .error st
                  | .ok st =>
                      match dropRest lim rest st with
                      | .error st => .error st
                      | .ok st => .ok ⟨st, hv, false, true⟩
        | _ =>
            match pikeDrop st th.h lim with
            | .error st => .error st
            | .ok st => stepThreads re s mo lim start pos rest st mh seeding matched

/-- Seed the current position, lowest priority, unless a match already
exists, the pattern is anchored elsewhere, or the bumpalong rule declines
to start between the halves of a CR LF. -/
def pikeSeed (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start pos : Nat) (st : PikeSt) : POut PikeSt :=
  let skip := pos > start && re.nltype.crlfish && !re.hascrlf &&
    re.crfirst && byteAt s (pos - 1) == 0x0D && pos < s.size &&
    byteAt s pos == 0x0A
  if skip then .ok st
  else
    match pikeTake st re.novec lim with
    | .error st => .error st
    | .ok (st, sh) =>
        let novec := re.novec
        let block := novec * regSize
        if block > lim.cost - st.m.cost then .error st
        else
          let st := { st with m := { st.m with cost := st.m.cost + block } }
          let base := sh * novec
          let pool := (List.range novec).foldl
            (fun (pool : Array UInt32) k => pool.set! (base + k) unset32)
            st.pool
          let st := { st with pool := pool.set! base pos.toUInt32 }
          pikeAdd re s mo lim false pos 0 sh st

/-- How the position loop ended. A budget blow overrides an earlier match:
the engine's `blown()` writes ResourceExceeded over whatever the result
held, because the threads above a recorded match were still running. -/
inductive PikeEnd where
  | matched | noMatch | exceeded
deriving DecidableEq

/-- The lockstep scan over positions. Each iteration seeds, clears the
visited set (charged), steps the list, and swaps the lists — capacities
travelling with them, since growth is charged once per call. -/
def pikeLoop (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) (anchored : Bool) (words : Nat) :
    Nat → Nat → PikeSt → Nat → Bool → Bool → (PikeSt × Nat × PikeEnd)
  | 0, _, st, mh, _, _ => (st, mh, .exceeded)
  | steps + 1, pos, st, mh, seeding, matched =>
      let settled := fun (st : PikeSt) (mh : Nat) (matched : Bool) =>
        (st, mh, if matched then PikeEnd.matched else .noMatch)
      let seeded :=
        if seeding && (!anchored || pos == start) then
          pikeSeed re s mo lim start pos st
        else .ok st
      match seeded with
      | .error st => (st, mh, .exceeded)
      | .ok st =>
          if words > lim.cost - st.m.cost then (st, mh, .exceeded)
          else
            let st := { st with
              m := { st.m with cost := st.m.cost + words }
              seen := Array.replicate re.code.size false }
            match stepThreads re s mo lim start pos st.clist.toList st
                mh seeding matched with
            | .error st => (st, mh, .exceeded)
            | .ok out =>
                let st := out.st
                let st := { st with
                  clist := st.nlist, clistCap := st.nlistCap
                  nlist := #[], nlistCap := st.clistCap }
                if pos ≥ s.size then settled st out.mh out.matched
                else if st.clist.size == 0 && (!out.seeding || anchored) then
                  settled st out.mh out.matched
                else
                  pikeLoop re s mo lim start anchored words steps (pos + 1)
                    st out.mh out.seeding out.matched

/-- `pike_run`: the whole lockstep call. The stack limit has nothing to
refuse on this path and the reported stack usage is zero. -/
def pikeRun (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) (init : PikeSt) : RunResult :=
  if !re.pike then ⟨.badInput, #[], {}⟩
  else if start > s.size then ⟨.badInput, #[], {}⟩
  else
    let novec := re.novec
    let words := re.code.size / 8 + 1
    let setup := novec * regSize + words
    if setup > lim.mem || setup > lim.cost then ⟨.resourceExceeded, #[], {}⟩
    else
      let st : PikeSt := { init with
        clist := #[], nlist := #[], stk := #[]
        pool := #[], rc := #[], free := #[]
        seen := Array.replicate re.code.size false
        m := ⟨setup, setup, setup⟩ }
      let anchored := re.anchored || mo.anchored
      let (st, mh, ended) :=
        pikeLoop re s mo lim start anchored words (s.size + 2) start st
          none32 true false
      let usage : Usage := { cost := st.m.cost, stack := 0, mem := st.m.peak }
      match ended with
      | .exceeded => ⟨.resourceExceeded, #[], usage⟩
      | .noMatch => ⟨.noMatch, #[], usage⟩
      | .matched =>
          let block := novec * regSize
          if block > lim.cost - st.m.cost then ⟨.resourceExceeded, #[], usage⟩
          else
            let ovec := (Array.range novec).map
              (fun k => st.pool[mh * novec + k]!)
            ⟨.matched, ovec, { usage with cost := st.m.cost + block }⟩

end Pcrevera.Ref
