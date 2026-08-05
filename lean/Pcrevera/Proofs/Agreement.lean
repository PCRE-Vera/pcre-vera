import Pcrevera.Ref.Exec
import Pcrevera.Spec.Total

/-!
# S-12, and why it is a corollary rather than an obligation

DESIGN.md section 6 makes cross-matcher agreement fall out of refinement
rather than earning it separately: on a Pike-eligible pattern the Pike
configuration and the internal plain-backtracking configuration each refine
`Matches`, so under budgets that rule ResourceExceeded out they agree with
each other. That argument is entirely about the common referent, and it is
what this file proves — once, over an abstract pair of runs.

The sufficient-budget premise is inherent, not a convenience. At equal
limits two matchers may legitimately differ on ResourceExceeded: they meter
different work. What agreement means is that where both complete, they
completed on the same answer.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- What a run refining the specification says, in the three shapes
`RunResult` can take besides ResourceExceeded. This is the conclusion the
refinement theorems deliver, named so the corollary can quantify over it
instead of over a particular matcher. -/
def RefinesMatches (r : RunResult) (p : Pat) (s : ByteArray) (start : Nat)
    (mo : MOpts) : Prop :=
  (r.outcome = .matched → Spec.Matches p s start mo = .found r.ovec) ∧
  (r.outcome = .noMatch → Spec.Matches p s start mo = .notFound) ∧
  (r.outcome = .badInput ↔ Spec.Matches p s start mo = .badInput)

/-- Two runs that refine the same specification and that both completed
answer the same thing, ovector included. Completing is the whole premise:
`ResourceExceeded` says nothing about the pattern, so a run that hit its
budget is not a party to the agreement. -/
theorem agree_of_refines {r₁ r₂ : RunResult} {p : Pat} {s : ByteArray}
    {start : Nat} {mo : MOpts}
    (h₁ : RefinesMatches r₁ p s start mo)
    (h₂ : RefinesMatches r₂ p s start mo)
    (hne₁ : r₁.outcome ≠ .resourceExceeded)
    (hne₂ : r₂.outcome ≠ .resourceExceeded) :
    r₁.outcome = r₂.outcome ∧ (r₁.outcome = .matched → r₁.ovec = r₂.ovec) := by
  obtain ⟨hm₁, hn₁, hb₁⟩ := h₁
  obtain ⟨hm₂, hn₂, hb₂⟩ := h₂
  -- Every completed outcome pins `Matches`, and `Matches` is one value, so
  -- two completed outcomes cannot disagree without the specification
  -- disagreeing with itself.
  cases ho₁ : r₁.outcome with
  | resourceExceeded => exact absurd ho₁ hne₁
  | matched =>
      cases ho₂ : r₂.outcome with
      | resourceExceeded => exact absurd ho₂ hne₂
      | matched =>
          exact ⟨rfl, fun _ =>
            Spec.MatchAnswer.found.inj ((hm₁ ho₁).symm.trans (hm₂ ho₂))⟩
      | noMatch => exact absurd ((hm₁ ho₁).symm.trans (hn₂ ho₂)) (by simp)
      | badInput => exact absurd ((hm₁ ho₁).symm.trans (hb₂.mp ho₂)) (by simp)
  | noMatch =>
      cases ho₂ : r₂.outcome with
      | resourceExceeded => exact absurd ho₂ hne₂
      | matched => exact absurd ((hn₁ ho₁).symm.trans (hm₂ ho₂)) (by simp)
      | noMatch => exact ⟨rfl, by simp⟩
      | badInput => exact absurd ((hn₁ ho₁).symm.trans (hb₂.mp ho₂)) (by simp)
  | badInput =>
      cases ho₂ : r₂.outcome with
      | resourceExceeded => exact absurd ho₂ hne₂
      | matched => exact absurd ((hb₁.mp ho₁).symm.trans (hm₂ ho₂)) (by simp)
      | noMatch => exact absurd ((hb₁.mp ho₁).symm.trans (hn₂ ho₂)) (by simp)
      | badInput => exact ⟨rfl, by simp⟩

end Pcrevera.Ref
