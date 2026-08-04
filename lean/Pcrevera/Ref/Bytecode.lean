import Pcrevera.Basic
import Pcrevera.Spec.Ast

/-!
# The compiled form (layer R's vocabulary)

The bytecode, the repetition table, the region table and the compiled
pattern, mirroring `engine/layout.py` field for field. Wire scalars stay
`Nat` where the engine holds a `u32` whose value never nears the width —
program counters, table indices, region bounds — and `UInt32` where wrapping
is part of the semantics: the register file.

`none32` is the engine's NONE/UNSET sentinel spelled as a number, because
the corpus records it that way and the checker compares against it.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- The u32 sentinel 0xFFFFFFFF: NONE as an index, UNSET as a register. -/
def none32 : Nat := 0xFFFFFFFF

/-- The opcode inventory of DESIGN.md section 4.2, in layout order. -/
inductive Op where
  | chr | chrCI | cls | any | anyNoNL | bsr
  | split | jump | save
  | circ | circM | doll | dollE | dollM
  | sod | eod | eodn | wordB | notWordB
  | repZero | repLoop | repEnter | repNext
  | accept
deriving DecidableEq, Repr, Inhabited

/-- One instruction: opcode, argument, and the split's second arm. -/
structure Inst where
  op : Op
  arg : Nat := 0
  alt : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- One counted repetition: bounds, greediness, and the three pcs the code
generator fixed — the deciding head, the body entry, and the exit. -/
structure RepInfo where
  lo : Nat
  hi : Nat
  greedy : Bool
  head : Nat
  body : Nat
  after : Nat
deriving DecidableEq, Repr, Inhabited

/-- The region kinds of the resource analysis (layout.py's `Rk`). -/
inductive Rk where
  | root | group | branch | alt | «repeat»
deriving DecidableEq, Repr, Inhabited

/-- One region: a source construct's instruction range and its parent. -/
structure Region where
  kind : Rk
  parent : Nat
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr, Inhabited

/-- The compiled pattern, `layout.py`'s `Re` minus the name table (names
resolve group numbers at the API surface and no matcher reads them). The
class table is the flat 32-bytes-per-class blob the matchers index. -/
structure Re where
  code : Array Inst
  classes : Array UInt8
  reps : Array RepInfo
  regions : Array Region
  ncap : Nat
  nregs : Nat
  anchored : Bool
  endanchored : Bool
  nltype : NlType
  bsrtype : BsrType
  hascrlf : Bool
  crfirst : Bool
  pike : Bool
deriving Repr, Inhabited

/-- Ovector slots of a compiled pattern. -/
def Re.novec (re : Re) : Nat := 2 * (re.ncap + 1)

/-- Class-table membership: `class_has`, the same bit test as
`ClassBits.has` against the flat blob. -/
def Re.classHas (re : Re) (idx : Nat) (b : UInt8) : Bool :=
  re.classes[idx * 32 + (b >>> 3).toNat]! &&& (1 <<< (b &&& 7)) != 0

/-- What a run reports back: the `Usage` triple, in the section 5 units. -/
structure Usage where
  cost : Nat := 0
  stack : Nat := 0
  mem : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- The run outcomes, spec.py's ordinals. -/
inductive Outcome where
  | matched | noMatch | resourceExceeded | badInput
deriving DecidableEq, Repr, Inhabited

def Outcome.toNat : Outcome → Nat
  | .matched => 0
  | .noMatch => 1
  | .resourceExceeded => 2
  | .badInput => 3

/-- One match call's full answer: outcome, ovector, and what it used. The
ovector only means anything on `matched`. -/
structure RunResult where
  outcome : Outcome
  ovec : Array UInt32 := #[]
  usage : Usage := {}
deriving Repr

/-- The caller's limits, DESIGN.md section 2.4: cost in counter units,
stack in backtrack entries, memory in IR bytes. -/
structure Limits where
  cost : Nat
  stack : Nat
  mem : Nat
deriving DecidableEq, Repr

/-- The IR entry sizes of spec.py, the units the accounting weighs with. -/
def btSize : Nat := 12
def undoSize : Nat := 8
def regSize : Nat := 4
def thSize : Nat := 8
def growMin : Nat := 4
def growFactor : Nat := 2

/-- Declared maxima the growth helpers clamp against (spec.py). -/
def maxStack : Nat := ceiling / btSize
def maxTrail : Nat := ceiling / undoSize

end Pcrevera.Ref
