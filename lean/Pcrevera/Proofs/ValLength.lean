import Pcrevera.Proofs.PolySound
import Pcrevera.Ref.Context

/-!
# A bound never shrinks as the subject grows

BOUNDS.md section 2 writes every bound as `base^n` times a polynomial in
`n + 1` with nonnegative coefficients, so raising the subject length can
only raise the number — provided the base is at least one, which is the
only base the analysis ever produces and which the checker refuses to do
without.

That is what makes a preallocated context's single question honest. A
context reserves `worstCaseMemory` at its declared maximum and admits every
subject up to it; the reservation covers the shorter subjects exactly
because the bound is nondecreasing, and the sufficiency argument for a
context call is the plain call's argument at a length the reservation has
already paid for.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- The polynomial part never falls as the length grows. -/
theorem part_mono_length (p : Poly) {m n : Nat} (h : m ≤ n) :
    p.part m ≤ p.part n := by
  have h1 : m + 1 ≤ n + 1 := Nat.succ_le_succ h
  have t1 : p.c1 * (m + 1) ≤ p.c1 * (n + 1) := Nat.mul_le_mul_left _ h1
  have t2 : p.c2 * (m + 1) ^ 2 ≤ p.c2 * (n + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
  have t3 : p.c3 * (m + 1) ^ 3 ≤ p.c3 * (n + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
  have t4 : p.c4 * (m + 1) ^ 4 ≤ p.c4 * (n + 1) ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 4)
  simp only [Poly.part]
  omega

/-- And neither does the whole bound, once the base is a real one. A base
of zero is the shape `cert_check` refuses under `CrBase`, and it is refused
exactly because `0^n` falls rather than grows. -/
theorem val_mono_length {p : Poly} (hbase : 1 ≤ p.base) {m n : Nat}
    (h : m ≤ n) : p.val m ≤ p.val n :=
  Nat.mul_le_mul (Nat.pow_le_pow_right hbase h) (part_mono_length p h)

/-- What an accessor answering a number tells you: the pattern carries a
certificate for the path that runs, and the number is that certificate's
bound. The refusals are the accessor's own — a configuration or a length
the pattern cannot be asked about, and a bound past the counter or past the
projection's ceiling — so an `ok` status leaves only this. -/
theorem reBound_ok_elim {cp : CompiledPat} {kind : Bk} {mcfg n : Nat}
    (h : (reBound cp kind mcfg n).status = .ok) :
    ∃ cert, rePick cp = some cert ∧ (certBound cert kind n).ok = true ∧
      (reBound cp kind mcfg n).value = (certBound cert kind n).value := by
  by_cases hc : (mcfg != 0) = true
  · simp only [reBound, if_pos hc] at h; simp at h
  · by_cases hn : n > ceiling
    · simp only [reBound, if_neg hc, if_pos hn] at h; simp at h
    · cases hpick : rePick cp with
      | none => simp only [reBound, hpick, if_neg hc, if_neg hn] at h; simp at h
      | some cert =>
          by_cases hok : (!(certBound cert kind n).ok) = true
          · simp only [reBound, hpick, if_neg hc, if_neg hn, if_pos hok] at h
            simp at h
          · refine ⟨cert, rfl, by simpa using hok, ?_⟩
            simp only [reBound, hpick, if_neg hc, if_neg hn, if_neg hok]

/-- The same fact read off the accessor: a memory answer at the declared
maximum covers every subject the context admits. Both lengths have to be
answerable, since a saturating bound is a refusal rather than a number. -/
theorem reMem_mono_length {cp : CompiledPat} {mcfg m n : Nat}
    (hbase : ∀ cert, rePick cp = some cert → 1 ≤ cert.mem.base)
    (h : m ≤ n)
    (hm : (reMem cp mcfg m).status = .ok)
    (hn : (reMem cp mcfg n).status = .ok) :
    (reMem cp mcfg m).value ≤ (reMem cp mcfg n).value := by
  obtain ⟨certm, hpickm, hokm, hvm⟩ := reBound_ok_elim hm
  obtain ⟨certn, hpickn, hokn, hvn⟩ := reBound_ok_elim hn
  have hsame : certm = certn := by
    rw [hpickm] at hpickn; exact Option.some.inj hpickn
  subst hsame
  have hval : ∀ k, (certBound certm .mem k).ok = true →
      (certBound certm .mem k).value = certm.mem.val k := by
    intro k hok
    by_cases hc : (polyValue certm.mem k).ok = true ∧
        (polyValue certm.mem k).value > ceiling
    · simp only [certBound, if_pos hc, Bound.exceeds] at hok; simp at hok
    · simp only [certBound, if_neg hc] at hok ⊢
      refine polyValue_ok ?_
      cases hpv : polyValue certm.mem k with
      | mk ok value =>
        rw [hpv] at hok
        cases ok
        · simp at hok
        · rfl
  simp only [reMem]
  rw [hvm, hvn, hval m hokm, hval n hokn]
  exact val_mono_length (hbase certm hpickm) h

end Pcrevera.Ref
