import Pcrevera.Ref.Cert
import Pcrevera.Ref.Pike

/-!
# The compiled pattern with its certificates, the accessors, and the
preallocated context (R-3, and the S-5 surface's working parts)

`compileFull` is the whole of `compile` as the engine runs it: codegen, then
the resource analysis, the checker's verdict deciding what the pattern gets
to carry. The accessors answer off the stored certificate exactly as
`engine/accessors.py` does, refusal order included, and `ctxCreate` is
`engine/context.py`: the memory bound made physical, the reservation taken
from the very accessor a caller would ask, each scratch array reserved at
the growth schedule's final capacity for its own term of the bound, and the
ballast making the resident bytes the accessor's number to the byte.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- A compiled pattern as the engine hands one back: the program plus
whatever certificates survived the checker. When the install verdict is
`crOk` this is exactly the engine's `Re`; any other verdict is the
engine-bug channel (`E_INTERNAL`), which no pattern can cause. -/
structure CompiledPat where
  re : Re
  cert : Option Cert
  pikecert : Option Cert

/-- Compilation with the resource analysis, `program.py`'s `compile`. -/
def compileFull (p : Pat) : Cr × CompiledPat :=
  let re := compile p
  let (verdict, cert, pikecert) := certInstall re
  (verdict, ⟨re, cert, pikecert⟩)

/-- What a public accessor answers with, `layout.py`'s `Answer`: a number,
or one of the two named refusals. -/
inductive AnswerSt where
  | ok | badInput | exceedsBudget
deriving DecidableEq, Repr

def AnswerSt.toNat : AnswerSt → Nat
  | .ok => 0
  | .badInput => 3
  | .exceedsBudget => 4

structure Answer where
  status : AnswerSt
  value : Nat
deriving DecidableEq, Repr

/-- The certificate of the path that will actually run: `re_pick`. -/
def rePick (cp : CompiledPat) : Option Cert :=
  if cp.re.pike then cp.pikecert else cp.cert

/-- One certified bound as the public contract states it: `re_bound`, the
refusal order part of the contract. The match configuration only has its
default until M9; anything else is BadInput before the slot is looked at. -/
def reBound (cp : CompiledPat) (kind : Bk) (mcfg : Nat) (n : Nat) : Answer :=
  if mcfg != 0 then ⟨.badInput, 0⟩
  else if n > ceiling then ⟨.badInput, 0⟩
  else
    match rePick cp with
    | none => ⟨.exceedsBudget, 0⟩
    | some picked =>
        let out := certBound picked kind n
        if !out.ok then ⟨.exceedsBudget, 0⟩ else ⟨.ok, out.value⟩

/-- `re_class`: no configuration argument, because the class is fixed at
compilation. The ordinals are spec.py's CLASS_*. -/
def reClass (cp : CompiledPat) : Answer :=
  match rePick cp with
  | none => ⟨.exceedsBudget, 0⟩
  | some picked =>
      match picked.complexity with
      | .notProvenLinear => ⟨.ok, 0⟩
      | .linear => ⟨.ok, 1⟩

def reCost (cp : CompiledPat) (mcfg n : Nat) : Answer := reBound cp .cost mcfg n
def reStack (cp : CompiledPat) (mcfg n : Nat) : Answer := reBound cp .stack mcfg n
def reMem (cp : CompiledPat) (mcfg n : Nat) : Answer := reBound cp .mem mcfg n

/-- What context creation answers: `match`'s outcome vocabulary plus the
accessors' ExceedsBudget, the ordinals spec.py fixes. -/
inductive CreateSt where
  | ok | resourceExceeded | badInput | exceedsBudget
deriving DecidableEq, Repr

def CreateSt.toNat : CreateSt → Nat
  | .ok => 0
  | .resourceExceeded => 2
  | .badInput => 3
  | .exceedsBudget => 4

/-- A created context, as much of the engine's `Ctx` as behavior needs: the
compiled pattern, the baked ceilings, and every reserved capacity. The
array contents are re-derived by each call — the run cores truncate before
use — so capacities are the whole of what creation leaves behind. -/
structure Ctx where
  cp : CompiledPat
  maxlen : Nat
  costcap : Nat
  stackcap : Nat
  memcap : Nat
  regsCap : Nat
  btCap : Nat
  trailCap : Nat
  listsCap : Nat
  stkCap : Nat
  tablesCap : Nat
  poolCap : Nat
  words : Nat
  slack : Nat

/-- `ctx_create`: validate through the accessor, size every array from the
selected certificate, and refuse in the accessor's own order. A refusal
creates nothing. -/
def ctxCreate (cp : CompiledPat) (mcfg maxlen : Nat) (lim : Limits) :
    CreateSt × Option Ctx :=
  let answered := reMem cp mcfg maxlen
  match answered.status with
  | .badInput => (.badInput, none)
  | .exceedsBudget => (.exceedsBudget, none)
  | .ok =>
  let resident := answered.value
  match rePick cp with
  | none => (.exceedsBudget, none)
  | some picked =>
  let novec := (cp.re.ncap + 1) * 2
  let answer := novec * regSize
  let over := false
  let sized :
      Option ((Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) × Nat × Nat) :=
    if cp.re.pike then
      let (room, over) := pikeRoom cp.re over
      let setup := novec * regSize + room.words
      if over then none
      else some ((0, 0, 0, room.lists, room.stk, room.tables, room.pool,
        room.words), setup, room.reserved)
    else
      let deep := polyValue picked.stack maxlen
      let long := polyValue picked.trail maxlen
      if !deep.ok || !long.ok then none
      else
        let (cbt, over) := growthCap deep.value over
        let (ctrail, over) := growthCap long.value over
        let (scratch, over) := satMul cbt btSize over
        let (weighed, over) := satMul ctrail undoSize over
        let (ballast, over) := satAdd scratch weighed over
        let setup := (cp.re.nregs + novec) * regSize
        if over then none
        else some ((cp.re.nregs, cbt, ctrail, 0, 0, 0, 0, 0), setup, ballast)
  match sized with
  | none => (.exceedsBudget, none)
  | some ((nregs, cbt, ctrail, lists, stk, tables, pool, words),
      setup, ballast) =>
      let over := false
      let (held1, over) := satAdd setup answer over
      let (held, over) := satAdd held1 ballast over
      if over then (.exceedsBudget, none)
      else if held > resident then (.exceedsBudget, none)
      else if resident > lim.mem then (.resourceExceeded, none)
      else if resident > lim.cost then (.resourceExceeded, none)
      else
        (.ok, some
          { cp, maxlen
            costcap := lim.cost
            stackcap := lim.stack
            memcap := resident
            regsCap := nregs
            btCap := cbt
            trailCap := ctrail
            listsCap := lists
            stkCap := stk
            tablesCap := tables
            poolCap := pool
            words
            slack := resident - held })

/-- `ctx_match`: a call may spend less than creation paid for and never
more, the configuration cannot change, and the reservation is the memory
answer whatever the subject was. -/
def ctxMatch (ctx : Ctx) (s : ByteArray) (start : Nat) (mo : MOpts)
    (cost stack : Nat) : RunResult :=
  if s.size > ctx.maxlen then ⟨.badInput, #[], {}⟩
  else if cost > ctx.costcap then ⟨.badInput, #[], {}⟩
  else if stack > ctx.stackcap then ⟨.badInput, #[], {}⟩
  else
    let lim : Limits := ⟨cost, stack, ctx.memcap⟩
    let out :=
      if ctx.cp.re.pike then
        pikeRun ctx.cp.re s start mo lim
          { clistCap := ctx.listsCap, nlistCap := ctx.listsCap
            stkCap := ctx.stkCap, poolCap := ctx.poolCap
            rcCap := ctx.tablesCap, freeCap := ctx.tablesCap }
      else
        btRun ctx.cp.re s start mo lim ctx.btCap ctx.trailCap
    { out with usage := { out.usage with mem := ctx.memcap } }

/-- Every IR byte a context holds resident: the reserved arrays at their
IR entry sizes, the two result stores, and the ballast — the sum the
engine's runners weigh off the object itself, which `ctxCreate` makes equal
to the accessor's number. -/
def Ctx.resident (ctx : Ctx) : Nat :=
  let novec := (ctx.cp.re.ncap + 1) * 2
  ctx.regsCap * regSize + ctx.btCap * btSize + ctx.trailCap * undoSize +
    ctx.listsCap * (2 * thSize) + ctx.stkCap * thSize +
    ctx.tablesCap * (2 * regSize) + ctx.poolCap * regSize +
    ctx.words + ctx.slack + 2 * (novec * regSize)

end Pcrevera.Ref
