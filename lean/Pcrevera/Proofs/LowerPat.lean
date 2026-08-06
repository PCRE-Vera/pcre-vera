import Pcrevera.Proofs.LowerShape

/-!
# The equality everyone quotes

L-2's load-bearing statement is `lower_searchEq`: the same ordered thread
list, positions and capture registers alike. This file carries it the rest of
the way, to the answer a caller actually sees.

The distance is short but it is not nothing. `Matches` runs a scan over
starting positions, and the scan reads three things off the pattern besides
the tree: the capture count, which sizes the fresh register array; the
anchoring options, which end the scan; and the bumpalong refusal, which reads
`crWalk`. L-3 says the first and the last survive the rewrite and the middle
one is not part of the tree at all, so the scan takes the same steps and
stops in the same place.

`Matches` exposes only the final `MatchAnswer`, `scan` having already picked
the first surviving thread — which is why this is a corollary and not the
theorem.
-/

namespace Pcrevera.Spec

open Pcrevera

/-- The pattern the code generator really walks. -/
def _root_.Pcrevera.Pat.lowered (p : Pat) : Pat := { p with root := lower p.root }

@[simp] theorem lowered_root (p : Pat) : p.lowered.root = lower p.root := rfl
@[simp] theorem lowered_opts (p : Pat) : p.lowered.opts = p.opts := rfl
@[simp] theorem lowered_nltype (p : Pat) : p.lowered.nltype = p.nltype := rfl
@[simp] theorem lowered_bsrtype (p : Pat) : p.lowered.bsrtype = p.bsrtype := rfl
@[simp] theorem lowered_hascrlf (p : Pat) : p.lowered.hascrlf = p.hascrlf := rfl

@[simp] theorem lowered_ncap (p : Pat) : p.lowered.ncap = p.ncap :=
  maxGroup_lower p.root

@[simp] theorem lowered_crFirst (p : Pat) : p.lowered.crFirst = p.crFirst := by
  simp only [Pat.crFirst, lowered_root, crWalk_lower]

theorem lowered_skipsAttempt (p : Pat) (s : ByteArray) (pos : Nat) :
    skipsAttempt p.lowered s pos = skipsAttempt p s pos := by
  simp only [skipsAttempt, lowered_nltype, lowered_hascrlf, lowered_crFirst]

/-- One attempt, each side read at its own sufficient fuel. -/
theorem attemptThreads_lower {p : Pat} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} (hsafe : LowerSafe p.root = true)
    (hattempt : attempt ≤ s.size) :
    attemptThreads (suffFuel s.size p.lowered.root) p.lowered s mo start attempt
      = attemptThreads (suffFuel s.size p.root) p s mo start attempt := by
  unfold attemptThreads
  simp only [lowered_root, lowered_ncap, lowered_nltype, lowered_bsrtype,
    endOk, lowered_opts]
  rw [show search (suffFuel s.size (lower p.root))
        ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ (lower p.root) attempt
        (Array.replicate (2 * (p.ncap + 1)) unset32)
      = search (suffFuel s.size p.root)
        ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root attempt
        (Array.replicate (2 * (p.ncap + 1)) unset32) from
    ((lower_searchEq ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root hsafe
      attempt _ hattempt).symm)]

/-- The scan takes the same steps and stops in the same place. -/
theorem scan_lower {p : Pat} {s : ByteArray} {mo : MOpts} {start : Nat}
    (hsafe : LowerSafe p.root = true) :
    ∀ (steps attempt : Nat), attempt ≤ s.size →
      scan (suffFuel s.size p.lowered.root) p.lowered s mo start attempt steps
        = scan (suffFuel s.size p.root) p s mo start attempt steps := by
  intro steps
  induction steps with
  | zero => intro attempt _; rw [scan.eq_def, scan.eq_def]
  | succ steps ih =>
      intro attempt hattempt
      rw [scan.eq_def, scan.eq_def]
      simp only []
      rw [attemptThreads_lower hsafe hattempt]
      cases hsurv : attemptThreads (suffFuel s.size p.root) p s mo start attempt with
      | none => rfl
      | some survivors =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          cases survivors with
          | cons t rest => rfl
          | nil =>
              simp only [lowered_opts]
              split <;> rename_i hstop
              · rfl
              · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hstop
                have hlt : attempt < s.size := Nat.lt_of_not_le hstop.2
                rw [lowered_skipsAttempt]
                split <;> rename_i hskip
                · exact ih _ (by have := skipsAttempt_lt hskip; omega)
                · exact ih _ (by omega)

theorem matchesF_lower {p : Pat} {s : ByteArray} {start : Nat} {mo : MOpts}
    (hsafe : LowerSafe p.root = true) :
    matchesF (suffFuel s.size p.lowered.root) p.lowered s start mo
      = matchesF (suffFuel s.size p.root) p s start mo := by
  unfold matchesF
  split <;> rename_i hbad
  · rfl
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbad
    exact scan_lower hsafe _ start (by omega)

/-- L-2, as a caller sees it: lowering the tree does not change the answer.

Every pattern, every subject, every start offset, every match option — for
the trees the engine agrees to lower. -/
theorem Matches_lower (p : Pat) (s : ByteArray) (start : Nat) (mo : MOpts)
    (hsafe : LowerSafe p.root = true) :
    Matches p.lowered s start mo = Matches p s start mo := by
  have h1 := matches_stable p s start mo _ (Nat.le_refl _)
  have h2 := matches_stable p.lowered s start mo _ (Nat.le_refl _)
  rw [matchesF_lower hsafe, h1] at h2
  exact (Option.some.inj h2).symm

end Pcrevera.Spec
