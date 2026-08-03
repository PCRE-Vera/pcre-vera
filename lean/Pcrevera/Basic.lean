/-!
# pcre-vera, the Lean side

This is where the four proof layers of DESIGN.md section 6 will live, each as a
namespace under `Pcrevera`:

* `Spec`     — layer S, the pattern semantics and the per-configuration
               execution semantics that define what "correct PCRE" means here
* `Ref`      — layer R, the executable reference engine and its equivalence
               with the specification
* `Tir`      — layer I, the TIR syntax, its interpreter, the JSON decoder that
               reads `engine.tir.json`, and the refinement proof
* `Analysis` — layer A, the bound certificate checker and its soundness

Layers S and R arrive with M6, layer I with M7. What is here now is the
scaffolding: a lake project that builds, so CI has something to check from the
first commit, plus the one piece of arithmetic every later layer meters work
with.
-/

namespace Pcrevera

/-- The saturation point of TIR's `counter` type.

Deliberately 2^53 - 1 rather than a machine word: JavaScript numbers represent
every integer up to that point exactly, and BigInt is too slow for a hot loop.
Go gets a `uint64` with an explicit check, so all three languages agree on
every cost, stack, and memory number. -/
def counterMax : Nat := 2 ^ 53 - 1

/-- Saturating addition on counters.

Enforcement in the engine is pre-charge: a charge is compared against the
remaining budget before this runs, so a run can never idle at the cap doing
uncounted work (DESIGN.md section 5). Saturation is the backstop for bound
evaluation, where an overflowing result is reported as `ExceedsBudget` rather
than as a number. -/
def counterAdd (a b : Nat) : Nat :=
  if counterMax < a + b then counterMax else a + b

theorem counterAdd_le (a b : Nat) : counterAdd a b ≤ counterMax := by
  unfold counterAdd
  split
  · exact Nat.le_refl counterMax
  · next h => exact Nat.le_of_not_lt h

theorem counterAdd_exact {a b : Nat} (h : a + b ≤ counterMax) :
    counterAdd a b = a + b := by
  unfold counterAdd
  simp [Nat.not_lt_of_le h]

end Pcrevera
