/-!
# The wave 1 pattern AST (S-1)

The specification's view of a pattern: the tree the parser hands over, with
every compile option already resolved into it. Case folding picked `chrCI`
nodes and folded their byte, EXTENDED and \Q...\E vanished during the parse,
MULTILINE and DOTALL and DOLLAR_ENDONLY chose which anchor and dot each node
is. What survives to match time — ANCHORED, ENDANCHORED, the newline and \R
conventions — travels beside the tree in `Pat`.

The step from pattern text to this tree is a tested link until M10 proves the
parser: every theorem over `Pat` quantifies over trees, and the conformance
corpora pin the exported trees to the engine's parser case by case.

A character class arrives as its finished 256-bit membership bitmap, negation
and case folding already applied, because that is what a class *means*; the
compiled form's class table is layer R's business.
-/

namespace Pcrevera

/-- A 256-bit byte set, 32 bytes, low bit first — the same wire format the
engine's class table uses, so membership is the same bit test everywhere. -/
abbrev ClassBits := Vector UInt8 32

/-- Does the set hold this byte? Mirrors the engine's `class_has`. -/
def ClassBits.has (bits : ClassBits) (b : UInt8) : Bool :=
  bits[(b >>> 3).toNat]! &&& (1 <<< (b &&& 7)) != 0

/-- The newline convention (spec.py's NL_*), fixed at compile time. -/
inductive NlType where
  | lf | cr | crlf | anycrlf | any
deriving DecidableEq, Repr, Inhabited

/-- The \R convention (spec.py's BSR_*). -/
inductive BsrType where
  | unicode | anycrlf
deriving DecidableEq, Repr, Inhabited

/-- The wave 1 AST. One constructor per arena node kind of the engine's
parser, in the same order, payloads included:

* `chr` is an exact byte, `chrCI` carries the case-folded byte and matches
  through the fold table, `cls` a finished byte set;
* `any` is the DOTALL dot, `anyNoNL` the plain one;
* `grp` carries its capture number, `0` meaning a non-capturing group;
* `rep` is any quantifier: `hi = none` is unbounded, and `greedy` is after
  UNGREEDY had its say;
* the anchor family mirrors the multiline/endonly choices the parser made.
-/
inductive Ast where
  | nul
  | chr (b : UInt8)
  | chrCI (folded : UInt8)
  | cls (bits : ClassBits)
  | any
  | anyNoNL
  | bsr
  | cat (kids : List Ast)
  | alt (arms : List Ast)
  | grp (cap : Nat) (body : Ast)
  | rep (lo : Nat) (hi : Option Nat) (greedy : Bool) (body : Ast)
  | circ | circM | doll | dollE | dollM
  | sod | eod | eodn | wordB | notWordB
deriving Repr, Inhabited

/-- The compile-time options that still matter at match time. -/
structure PatOpts where
  anchored : Bool
  endanchored : Bool
deriving DecidableEq, Repr, Inhabited

/-- A compiled-from-source pattern, as the spec receives one: the tree plus
what the parse decided about the whole pattern. `hascrlf` is the parser's
record that the pattern spells CR or LF explicitly (with pcre2's `[^x]`
exception), which the bumpalong rule of the match loop reads. -/
structure Pat where
  root : Ast
  opts : PatOpts
  nltype : NlType
  bsrtype : BsrType
  hascrlf : Bool
deriving Repr, Inhabited

/-- The match-time options of DESIGN.md section 2.2. -/
structure MOpts where
  notbol : Bool := false
  noteol : Bool := false
  notempty : Bool := false
  notemptyAtStart : Bool := false
  anchored : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- The highest capture number in the tree, which is the parser's `ncap`:
group numbers are dense, assigned 1.. in parse order, and a group survives
in the tree even where the compiler emits nothing for it. -/
def Ast.maxGroup : Ast → Nat
  | .cat kids => kids.attach.foldl (fun acc ⟨k, _⟩ => max acc k.maxGroup) 0
  | .alt arms => arms.attach.foldl (fun acc ⟨a, _⟩ => max acc a.maxGroup) 0
  | .grp cap body => max cap body.maxGroup
  | .rep _ _ _ body => body.maxGroup
  | _ => 0

def Pat.ncap (p : Pat) : Nat := p.root.maxGroup

/-- Ovector slots: two per group, the whole match included. -/
def Pat.novec (p : Pat) : Nat := 2 * (p.ncap + 1)

end Pcrevera
