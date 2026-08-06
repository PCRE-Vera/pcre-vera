import Pcrevera.Spec.Total

/-!
# The quantifier lowering, as a function on trees (L-1)

DESIGN.md section 4.3 is implemented inside the engine's code generator: a
counted repetition emits its body's job several times instead of growing the
parser's arena. `lowered.py` is that rewrite restated over the exported tree,
and this file is the same rewrite once more, in Lean, so that the thing the
generator really walks is a tree the specification can talk about.

The shape is `lowered.py`'s, clause for clause. The spellings already in star
form — nothing at all, the singleton, the one-split optional, the pure star —
keep their own emission. A bounded quantifier becomes its minimum in copies
ending in a chain of nested optionals, so that the k-th copy's presence is
decided before the (k+1)-th's. An unbounded one becomes its minimum in copies
ending in a pure star.

`Nullable` is the other thing that has to be written down here, because the
unbounded splice is only sound when the body cannot match empty: at the last
copy the original repetition would apply pcre2's empty-match rule and stop,
while the star it lowers to would go round again. The engine refuses to lower
such a pattern (`LB_NULLABLE`), and this is the semantic reason why.
-/

namespace Pcrevera.Spec

open Pcrevera

/-- The copies a minimum demands, then whatever the quantifier ends in.

A concatenation, which opens no region of its own, so the region tree is the
one the copied constructs and the tail bring with them. -/
def copies (body tail : Ast) : Nat → Ast
  | 0 => tail
  | n + 1 => .cat [body, copies body tail n]

/-- The nested optionals a finite bound ends in.

They nest so that the k-th copy's presence is decided before the (k+1)-th's,
which is what makes the count preference pcre2's, and they all exit at the
same place. -/
def optionals (body : Ast) (greedy : Bool) : Nat → Ast
  | 0 => .nul
  | n + 1 => .rep 0 (some 1) greedy (.cat [body, optionals body greedy n])

/-- One quantifier in star form, its body already lowered. -/
def lowerRep (lo : Nat) (hi : Option Nat) (greedy : Bool) (body : Ast) : Ast :=
  match hi with
  | some 0 => .rep lo (some 0) greedy body
  | some 1 => .rep lo (some 1) greedy body
  | none =>
      if lo = 0 then .rep 0 none greedy body
      else copies body (.rep 0 none greedy body) lo
  | some (h + 2) => copies body (optionals body greedy (h + 2 - lo)) lo

mutual

/-- One subtree in star form, bottom up.

Recursive because a copied body that still held a counted repetition would
still hold a counter, and one retained counter makes the whole program
ineligible. -/
def lower : Ast → Ast
  | .cat kids => .cat (lowerList kids)
  | .alt arms => .alt (lowerList arms)
  | .grp cap body => .grp cap (lower body)
  | .rep lo hi greedy body => lowerRep lo hi greedy (lower body)
  | a => a

/-- The children of a concatenation or an alternation, each lowered.

Written out rather than spelled `List.map`, because a nested inductive's
recursion has to be visible to the equation compiler, and because every
induction over the lowering wants this function's equations anyway. -/
def lowerList : List Ast → List Ast
  | [] => []
  | k :: rest => lower k :: lowerList rest

end

mutual

/-- Can this subtree match without consuming a byte?

The engine's `Size.nullable`, transcribed clause for clause. It
over-approximates on purpose — an assertion is nullable, a `\R` is not — and
the one thing it must never do is call a body non-nullable that can match
empty, which `LowerNull.lean` proves it does not.

`x{m,0}` is nullable whatever its body says, which is the engine's answer too
and for the same reason: nothing under a zero repeat is reached. -/
def Nullable : Ast → Bool
  | .nul => true
  | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr => false
  | .cat kids => nullableAll kids
  | .alt arms => nullableAny arms
  | .grp _ body => Nullable body
  | .rep lo hi _ body => hi == some 0 || lo == 0 || Nullable body
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => true

/-- A concatenation matches empty only when every child can. -/
def nullableAll : List Ast → Bool
  | [] => true
  | k :: rest => Nullable k && nullableAll rest

/-- An alternation matches empty as soon as one branch can. -/
def nullableAny : List Ast → Bool
  | [] => false
  | a :: rest => Nullable a || nullableAny rest

end

mutual

/-- The condition under which the rewrite preserves the search.

This is the *proof's* sufficient condition, not the engine's acceptance test.
The engine decides with `decide`, which is a different and stricter thing: it
also refuses a pattern holding `\R`, declines when no counted repetition
needs unrolling at all, and falls back when the unrolled form would not fit
its arrays. None of those affect what the rewrite means, so none of them
belong here; L-5 is where the engine's decision has to be shown to imply
this, not the other way round.

Two clauses, and the parser settles both.

A quantifier's bounds are in order: `{m,n}` with `m > n` is a parse error,
and every reading here assumes as much — `Nullable` would call `x{2,1}`
non-nullable while the search offers the empty exit, and the engine's own dry
run computes a negative copy count for it.

And an unbounded repetition the lowering actually splices — one with a
minimum to unroll — has a body that consumes. At the last copy the original
would apply pcre2's empty-match rule and stop, where the star it lowers to
would go round again. That is what `LB_NULLABLE` is for, though the engine
draws it more widely, blocking on the pure star as well.

Neither clause is asked of a subtree under `x{m,0}`, which matches nothing
and reaches nothing: the search answers before it looks at the body, and the
engine's dry run likewise returns a fresh size for it without descending. A
dead nullable star is a tree the engine will happily lower, so refusing it
here would be a condition the proof does not need. -/
def LowerSafe : Ast → Bool
  | .cat kids => lowerSafeAll kids
  | .alt arms => lowerSafeAll arms
  | .grp _ body => LowerSafe body
  | .rep lo hi _ body =>
      hi == some 0 ||
        (hi.all (fun h => lo ≤ h) &&
          (hi.isSome || lo == 0 || !Nullable body) && LowerSafe body)
  | _ => true

def lowerSafeAll : List Ast → Bool
  | [] => true
  | k :: rest => LowerSafe k && lowerSafeAll rest

end

end Pcrevera.Spec
