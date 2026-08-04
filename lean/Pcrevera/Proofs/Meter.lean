import Pcrevera.Ref.Pike

/-!
# What the charging helpers preserve

The small facts every run-level proof leans on: a charge never carries the
cost past the limit it was checked against, and never lowers the meter.
Stated once here so the termination, monotonicity and bound proofs share
one vocabulary instead of re-proving arithmetic per opcode.
-/

namespace Pcrevera.Ref

open Pcrevera

theorem chargeGrow_spec {oldcap len esize maxv : Nat} {m m' : Meter}
    {lim : Limits} {cap : Nat}
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    m.cost ≤ m'.cost ∧ (m.cost ≤ lim.cost → m'.cost ≤ lim.cost) := by
  simp only [chargeGrow] at h
  split at h
  · cases h; omega
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next hwork =>
            cases h
            simp only [Nat.not_lt] at hwork
            refine ⟨?_, fun hin => ?_⟩ <;> dsimp only <;> omega

theorem chargeGrow_cost_le {oldcap len esize maxv : Nat} {m m' : Meter}
    {lim : Limits} {cap : Nat}
    (hin : m.cost ≤ lim.cost)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    m'.cost ≤ lim.cost := (chargeGrow_spec h).2 hin

theorem chargeGrow_cost_mono {oldcap len esize maxv : Nat} {m m' : Meter}
    {lim : Limits} {cap : Nat}
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    m.cost ≤ m'.cost := (chargeGrow_spec h).1

theorem writeReg_spec {st st' : BtSt} {lim : Limits} {slot : Nat}
    {value : UInt32}
    (h : writeReg st lim slot value = some st') :
    st.m.cost ≤ st'.m.cost ∧ (st.m.cost ≤ lim.cost → st'.m.cost ≤ lim.cost) := by
  simp only [writeReg] at h
  split at h
  · cases hg : chargeGrow st.trailCap st.trail.size undoSize maxTrail st.m lim with
    | none => rw [hg] at h; cases h
    | some pair =>
        rw [hg] at h
        cases h
        exact ⟨chargeGrow_cost_mono hg, fun hin => chargeGrow_cost_le hin hg⟩
  · cases h
    exact ⟨Nat.le_refl _, id⟩

theorem pushBt_spec {st st' : BtSt} {lim : Limits} {pc pos mark : Nat}
    (h : pushBt st lim pc pos mark = some st') :
    st.m.cost ≤ st'.m.cost ∧ (st.m.cost ≤ lim.cost → st'.m.cost ≤ lim.cost) := by
  simp only [pushBt] at h
  split at h
  · cases h
  · cases hg : chargeGrow st.btCap st.bt.size btSize maxStack st.m lim with
    | none => rw [hg] at h; cases h
    | some pair =>
        rw [hg] at h
        cases h
        exact ⟨chargeGrow_cost_mono hg, fun hin => chargeGrow_cost_le hin hg⟩

theorem fork_spec {st st' : BtSt} {lim : Limits} {target pos : Nat}
    (h : fork st lim target pos = some st') :
    st.m.cost ≤ st'.m.cost ∧ (st.m.cost ≤ lim.cost → st'.m.cost ≤ lim.cost) := by
  simp only [fork] at h
  cases hp : pushBt st lim target pos st.trail.size with
  | none => rw [hp] at h; cases h
  | some mid =>
      rw [hp] at h
      cases h
      simpa using pushBt_spec hp

end Pcrevera.Ref
