import Pcrevera.Proofs.Meter

/-!
# The backtracking loops halt on the budget (R-5, bt half)

`btStep` runs on fuel, but the fuel is bookkeeping, not a bound: every
iteration either returns or charges at least one unit after checking the
budget, so the gap to the cost limit always covers the recursion. This
file proves it as congruence — two runs agree whenever both fuels cover
the gap — which is the useful form of termination for a fueled function:
the answer does not depend on the fuel expression the definition happens
to pass.

The congruence threshold is deliberately one unit weaker than the
`lim.cost + 1 - cost` the definitions use: `lim.cost - cost ≤ fuel`
suffices, because at the limit the entry check refuses on any fuel, zero
included. That weaker form is also what the induction needs — `btFail`
re-enters `btStep` on the same fuel, and when a backtrack entry replays
an empty trail slice the replay charge is zero, so only the one-unit
slack keeps the threshold satisfied across that call.

The attempt loop is the same story one level up: `btLoop` advances the
attempt by at least one per recursion (two on a bumpalong skip, whose
guard keeps the next attempt inside the subject) and stops at the
subject's end, so `s.size + 1 - attempt` steps always cover it. That
argument needs the run-level invariant proved here too: every state an
attempt hands back still satisfies `cost ≤ lim.cost`, because the engine
checks every charge before making it.

`btRun_halts` and `btStep_fuel_irrelevant` state the payoff for the
fuels `btRun` actually passes: replace either by anything at least as
large and nothing changes.
-/

namespace Pcrevera.Ref

open Pcrevera

theorem btStep_exceeded_of_le {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt fuel pc pos : Nat} {st : BtSt}
    (h : lim.cost ≤ st.m.cost) :
    btStep re s mo lim start attempt fuel pc pos st = .exceeded st := by
  cases fuel with
  | zero => rw [btStep]
  | succ f => rw [btStep]; exact if_pos h

theorem btCongr_ind (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start attempt : Nat) : ∀ fuel₁ : Nat,
    (∀ fuel₂ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
        lim.cost - st.m.cost ≤ fuel₁ → lim.cost - st.m.cost ≤ fuel₂ →
        btStep re s mo lim start attempt fuel₁ pc pos st =
          btStep re s mo lim start attempt fuel₂ pc pos st) ∧
    (∀ fuel₂ (st : BtSt), st.m.cost ≤ lim.cost →
        lim.cost - st.m.cost ≤ fuel₁ → lim.cost - st.m.cost ≤ fuel₂ →
        btFail re s mo lim start attempt fuel₁ st =
          btFail re s mo lim start attempt fuel₂ st) := by
  have hFail : ∀ fuel₁ fuel₂ : Nat,
      (∀ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
        lim.cost - st.m.cost ≤ fuel₁ → lim.cost - st.m.cost ≤ fuel₂ →
        btStep re s mo lim start attempt fuel₁ pc pos st =
          btStep re s mo lim start attempt fuel₂ pc pos st) →
      ∀ (st : BtSt), st.m.cost ≤ lim.cost →
        lim.cost - st.m.cost ≤ fuel₁ → lim.cost - st.m.cost ≤ fuel₂ →
        btFail re s mo lim start attempt fuel₁ st =
          btFail re s mo lim start attempt fuel₂ st := by
    intro fuel₁ fuel₂ hS st hst h₁ h₂
    rw [btFail, btFail]
    dsimp only
    repeat' split
    all_goals first
      | rfl
      | (apply hS <;> first | omega | (dsimp only; omega))
  intro fuel₁
  induction fuel₁ with
  | zero =>
      have hS : ∀ fuel₂ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
          lim.cost - st.m.cost ≤ 0 → lim.cost - st.m.cost ≤ fuel₂ →
          btStep re s mo lim start attempt 0 pc pos st =
            btStep re s mo lim start attempt fuel₂ pc pos st := by
        intro fuel₂ pc pos st hst h₁ _
        have hge : lim.cost ≤ st.m.cost := by omega
        rw [btStep_exceeded_of_le hge, btStep_exceeded_of_le hge]
      exact ⟨hS, fun fuel₂ st hst h₁ h₂ =>
        hFail 0 fuel₂ (hS fuel₂) st hst h₁ h₂⟩
  | succ a ih =>
      have hS : ∀ fuel₂ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
          lim.cost - st.m.cost ≤ a + 1 → lim.cost - st.m.cost ≤ fuel₂ →
          btStep re s mo lim start attempt (a + 1) pc pos st =
            btStep re s mo lim start attempt fuel₂ pc pos st := by
        intro fuel₂ pc pos st hst h₁ h₂
        by_cases hlim : st.m.cost ≥ lim.cost
        · rw [btStep_exceeded_of_le hlim, btStep_exceeded_of_le hlim]
        · obtain ⟨b, rfl⟩ : ∃ b, fuel₂ = b + 1 := ⟨fuel₂ - 1, by omega⟩
          have ihS : ∀ pc₁ pos₁ (st₁ : BtSt), st.m.cost + 1 ≤ st₁.m.cost →
              st₁.m.cost ≤ lim.cost →
              btStep re s mo lim start attempt a pc₁ pos₁ st₁ =
                btStep re s mo lim start attempt b pc₁ pos₁ st₁ :=
            fun pc₁ pos₁ st₁ hlo hhi =>
              ih.1 b pc₁ pos₁ st₁ hhi (by omega) (by omega)
          have ihF : ∀ (st₁ : BtSt), st.m.cost + 1 ≤ st₁.m.cost →
              st₁.m.cost ≤ lim.cost →
              btFail re s mo lim start attempt a st₁ =
                btFail re s mo lim start attempt b st₁ :=
            fun st₁ hlo hhi => ih.2 b st₁ hhi (by omega) (by omega)
          simp only [btStep]
          rw [if_neg hlim, if_neg hlim]
          repeat' split
          all_goals first
            | rfl
            | exact ihS _ _ _ (Nat.le_refl _)
                (show st.m.cost + 1 ≤ lim.cost by omega)
            | exact ihF _ (Nat.le_refl _)
                (show st.m.cost + 1 ≤ lim.cost by omega)
            | (obtain ⟨hmono, hcost⟩ :=
                 writeReg_spec ‹writeReg _ _ _ _ = some _›
               exact ihS _ _ _ hmono
                 (hcost (show st.m.cost + 1 ≤ lim.cost by omega)))
            | (obtain ⟨hmono, hcost⟩ := fork_spec ‹fork _ _ _ _ = some _›
               exact ihS _ _ _ hmono
                 (hcost (show st.m.cost + 1 ≤ lim.cost by omega)))
      exact ⟨hS, fun fuel₂ st hst h₁ h₂ =>
        hFail (a + 1) fuel₂ (hS fuel₂) st hst h₁ h₂⟩

theorem btStep_congr {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel₁ fuel₂ pc pos : Nat} {st : BtSt}
    (hst : st.m.cost ≤ lim.cost)
    (h₁ : lim.cost - st.m.cost ≤ fuel₁) (h₂ : lim.cost - st.m.cost ≤ fuel₂) :
    btStep re s mo lim start attempt fuel₁ pc pos st =
      btStep re s mo lim start attempt fuel₂ pc pos st :=
  (btCongr_ind re s mo lim start attempt fuel₁).1 fuel₂ pc pos st hst h₁ h₂

theorem btFail_congr {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel₁ fuel₂ : Nat} {st : BtSt}
    (hst : st.m.cost ≤ lim.cost)
    (h₁ : lim.cost - st.m.cost ≤ fuel₁) (h₂ : lim.cost - st.m.cost ≤ fuel₂) :
    btFail re s mo lim start attempt fuel₁ st =
      btFail re s mo lim start attempt fuel₂ st :=
  (btCongr_ind re s mo lim start attempt fuel₁).2 fuel₂ st hst h₁ h₂

/-- The state an attempt hands back, whichever way it ended. -/
def AttemptOut.state : AttemptOut → BtSt
  | .found _ st => st
  | .exhausted st => st
  | .exceeded st => st

theorem btCost_ind (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start attempt : Nat) : ∀ fuel : Nat,
    (∀ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
        (btStep re s mo lim start attempt fuel pc pos st).state.m.cost ≤
          lim.cost) ∧
    (∀ (st : BtSt), st.m.cost ≤ lim.cost →
        (btFail re s mo lim start attempt fuel st).state.m.cost ≤ lim.cost) := by
  have hFail : ∀ fuel : Nat,
      (∀ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
        (btStep re s mo lim start attempt fuel pc pos st).state.m.cost ≤
          lim.cost) →
      ∀ (st : BtSt), st.m.cost ≤ lim.cost →
        (btFail re s mo lim start attempt fuel st).state.m.cost ≤ lim.cost := by
    intro fuel hS st hst
    rw [btFail]
    dsimp only
    repeat' split
    all_goals first
      | exact hst
      | (apply hS; first | omega | (dsimp only; omega))
  intro fuel
  induction fuel with
  | zero =>
      have hS : ∀ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
          (btStep re s mo lim start attempt 0 pc pos st).state.m.cost ≤
            lim.cost := by
        intro pc pos st hst
        rw [btStep]
        exact hst
      exact ⟨hS, hFail 0 hS⟩
  | succ a ih =>
      have hS : ∀ pc pos (st : BtSt), st.m.cost ≤ lim.cost →
          (btStep re s mo lim start attempt (a + 1) pc pos st).state.m.cost ≤
            lim.cost := by
        intro pc pos st hst
        by_cases hlim : st.m.cost ≥ lim.cost
        · rw [btStep_exceeded_of_le hlim]; exact hst
        · simp only [btStep]
          rw [if_neg hlim]
          repeat' split
          all_goals first
            | exact (show st.m.cost + 1 ≤ lim.cost by omega)
            | exact ih.1 _ _ _ (show st.m.cost + 1 ≤ lim.cost by omega)
            | exact ih.2 _ (show st.m.cost + 1 ≤ lim.cost by omega)
            | (obtain ⟨_, hcost⟩ :=
                 writeReg_spec ‹writeReg _ _ _ _ = some _›
               exact ih.1 _ _ _
                 (hcost (show st.m.cost + 1 ≤ lim.cost by omega)))
            | (obtain ⟨_, hcost⟩ := fork_spec ‹fork _ _ _ _ = some _›
               exact ih.1 _ _ _
                 (hcost (show st.m.cost + 1 ≤ lim.cost by omega)))
      exact ⟨hS, hFail (a + 1) hS⟩

theorem btStep_cost_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hst : st.m.cost ≤ lim.cost) :
    (btStep re s mo lim start attempt fuel pc pos st).state.m.cost ≤
      lim.cost :=
  (btCost_ind re s mo lim start attempt fuel).1 pc pos st hst

theorem btFail_cost_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel : Nat} {st : BtSt}
    (hst : st.m.cost ≤ lim.cost) :
    (btFail re s mo lim start attempt fuel st).state.m.cost ≤ lim.cost :=
  (btCost_ind re s mo lim start attempt fuel).2 st hst

theorem btStep_exhausted_cost {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt fuel pc pos : Nat} {st st' : BtSt}
    (hst : st.m.cost ≤ lim.cost)
    (h : btStep re s mo lim start attempt fuel pc pos st = .exhausted st') :
    st'.m.cost ≤ lim.cost := by
  have hle := btStep_cost_le (re := re) (s := s) (mo := mo) (start := start)
    (attempt := attempt) (fuel := fuel) (pc := pc) (pos := pos) hst
  rw [h] at hle
  exact hle

theorem Re.skipsAttempt_lt {re : Re} {s : ByteArray} {pos : Nat}
    (h : re.skipsAttempt s pos = true) : pos < s.size := by
  simp only [Re.skipsAttempt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem btLoop_congr_ind (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) : ∀ steps₁ steps₂ attempt : Nat, ∀ st : BtSt,
    st.m.cost ≤ lim.cost → attempt ≤ s.size →
    s.size + 1 - attempt ≤ steps₁ → s.size + 1 - attempt ≤ steps₂ →
    btLoop re s mo lim start steps₁ attempt st =
      btLoop re s mo lim start steps₂ attempt st := by
  intro steps₁
  induction steps₁ with
  | zero =>
      intro steps₂ attempt st _ hat h₁ _
      exfalso
      omega
  | succ k ih =>
      intro steps₂ attempt st hst hat h₁ h₂
      obtain ⟨l, rfl⟩ : ∃ l, steps₂ = l + 1 := ⟨steps₂ - 1, by omega⟩
      simp only [btLoop]
      split
      · rfl
      · rename_i hreset
        split
        · rfl
        · rfl
        · rename_i stx hres
          split
          · rfl
          · rename_i hanch
            have hstx : stx.m.cost ≤ lim.cost :=
              btStep_exhausted_cost
                (show st.m.cost + re.nregs * regSize ≤ lim.cost by omega) hres
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hanch
            split
            · rename_i hskip
              have hlt := Re.skipsAttempt_lt hskip
              exact ih _ _ _ hstx (by omega) (by omega) (by omega)
            · exact ih _ _ _ hstx (by omega) (by omega) (by omega)

theorem btLoop_steps_congr {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start steps₁ steps₂ attempt : Nat} {st : BtSt}
    (hst : st.m.cost ≤ lim.cost) (hat : attempt ≤ s.size)
    (h₁ : s.size + 1 - attempt ≤ steps₁)
    (h₂ : s.size + 1 - attempt ≤ steps₂) :
    btLoop re s mo lim start steps₁ attempt st =
      btLoop re s mo lim start steps₂ attempt st :=
  btLoop_congr_ind re s mo lim start steps₁ steps₂ attempt st hst hat h₁ h₂

theorem btStep_fuel_irrelevant {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt pc pos : Nat} {st : BtSt} (extra : Nat)
    (hst : st.m.cost ≤ lim.cost) :
    btStep re s mo lim start attempt (lim.cost + 1 - st.m.cost) pc pos st =
      btStep re s mo lim start attempt (lim.cost + 1 - st.m.cost + extra)
        pc pos st :=
  btStep_congr hst (by omega) (by omega)

theorem btRun_halts {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {st : BtSt} (extra : Nat)
    (hstart : start ≤ s.size) (hst : st.m.cost ≤ lim.cost) :
    btLoop re s mo lim start (s.size + 1 - start) start st =
      btLoop re s mo lim start (s.size + 1 - start + extra) start st :=
  btLoop_steps_congr hst hstart (Nat.le_refl _) (by omega)

end Pcrevera.Ref
