import Pcrevera.Ref.Exec

/-!
# S-9: raising a limit never changes a settled answer

The VM states never record the limits: `BtSt` and `PikeSt` carry meters,
scratch arrays and capacities, and every limit only ever appears on the
left of a pre-charge comparison. So a run that completed under some limits
is replayed step for step under pointwise-higher ones — the same guards
pass a fortiori, the same helpers answer the same states, and the final
answer is the very same `RunResult`, usage included. The proofs below walk
that observation through every layer: the charging helpers, the two
instruction loops in lockstep on their fuel, the run wrappers, the context
gate, and finally `Exec`.

The one place the two runs disagree on anything at all is the backtracking
fuel, `lim.cost + 1 - cost`, which grows with the limit; the step lemma is
therefore stated for any larger fuel, which costs the induction nothing.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- Pointwise order on limit triples: raising means every component at or
above where it was. -/
def Limits.le (lim₁ lim₂ : Limits) : Prop :=
  lim₁.cost ≤ lim₂.cost ∧ lim₁.stack ≤ lim₂.stack ∧ lim₁.mem ≤ lim₂.mem

theorem Limits.le_cost {lim₁ lim₂ : Limits} (h : Limits.le lim₁ lim₂) :
    lim₁.cost ≤ lim₂.cost := And.left h

theorem Limits.le_stack {lim₁ lim₂ : Limits} (h : Limits.le lim₁ lim₂) :
    lim₁.stack ≤ lim₂.stack := And.left (And.right h)

theorem Limits.le_mem {lim₁ lim₂ : Limits} (h : Limits.le lim₁ lim₂) :
    lim₁.mem ≤ lim₂.mem := And.right (And.right h)

/-- An attempt that reached a verdict: anything but a budget refusal. -/
def AttemptOut.done : AttemptOut → Prop
  | .exceeded _ => False
  | _ => True

/-- A loop end that reached a verdict. -/
def RunEnd.done : RunEnd → Prop
  | .exceeded _ => False
  | _ => True

/-- A settled call: Found or NotFound, the two answers S-9 protects. -/
def RunResult.settled (r : RunResult) : Prop :=
  r.outcome = .matched ∨ r.outcome = .noMatch

theorem not_settled_exceeded {ovec : Array UInt32} {u : Usage} :
    ¬ (RunResult.mk .resourceExceeded ovec u).settled := by
  rintro (h | h) <;> exact Outcome.noConfusion h

theorem not_settled_badInput {ovec : Array UInt32} {u : Usage} :
    ¬ (RunResult.mk .badInput ovec u).settled := by
  rintro (h | h) <;> exact Outcome.noConfusion h

/-! ## The charging helpers

`chargeGrow` computes its new capacity and its charges from the state
alone; the limits only decide the two refusals, and both pass a fortiori
under a higher limit. The wrappers inherit that directly. -/

theorem chargeGrow_mono {oldcap len esize maxv : Nat} {m : Meter}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) {res : Meter × Nat}
    (h : chargeGrow oldcap len esize maxv m lim₁ = some res) :
    chargeGrow oldcap len esize maxv m lim₂ = some res := by
  have hc := Limits.le_cost hle
  have hm := Limits.le_mem hle
  simp only [chargeGrow] at h ⊢
  split at h
  · next hlt => rw [if_pos hlt]; exact h
  · next hlt =>
      rw [if_neg hlt]
      split at h
      · cases h
      · next hmax =>
          rw [if_neg hmax]
          split at h
          · cases h
          · next hmem =>
              split at h
              · cases h
              · next hwork =>
                  split
                  · next hmem2 => exact absurd hmem2 (by omega)
                  · split
                    · next hwork2 => exact absurd hwork2 (by omega)
                    · exact h

theorem writeReg_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st st' : BtSt} {slot : Nat} {value : UInt32}
    (h : writeReg st lim₁ slot value = some st') :
    writeReg st lim₂ slot value = some st' := by
  simp only [writeReg] at h ⊢
  split at h
  · next hbt =>
      rw [if_pos hbt]
      split at h
      · cases h
      · next m cap hg => rw [chargeGrow_mono hle hg]; exact h
  · next hbt => rw [if_neg hbt]; exact h

theorem pushBt_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st st' : BtSt} {pc pos mark : Nat}
    (h : pushBt st lim₁ pc pos mark = some st') :
    pushBt st lim₂ pc pos mark = some st' := by
  have hs := Limits.le_stack hle
  simp only [pushBt] at h ⊢
  split at h
  · cases h
  · next hcap =>
      split
      · next hcap2 => exact absurd hcap2 (by omega)
      · split at h
        · cases h
        · next m cap hg => rw [chargeGrow_mono hle hg]; exact h

theorem fork_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st st' : BtSt} {target pos : Nat}
    (h : fork st lim₁ target pos = some st') :
    fork st lim₂ target pos = some st' := by
  simp only [fork] at h ⊢
  split at h
  · cases h
  · next mid hp => rw [pushBt_mono hle hp]; exact h

/-! ## The backtracking loop, in lockstep

One attempt is reproduced instruction for instruction. The statement
allows a larger fuel on the higher-limit side because `btLoop` computes
its fuel from the limit; the induction never notices. -/

theorem btFail_mono_of {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {start attempt f₁ f₂ : Nat} {out : AttemptOut} (hd : out.done)
    (hstep : ∀ pc pos (st : BtSt),
      btStep re s mo lim₁ start attempt f₁ pc pos st = out →
      btStep re s mo lim₂ start attempt f₂ pc pos st = out)
    {st : BtSt} (h : btFail re s mo lim₁ start attempt f₁ st = out) :
    btFail re s mo lim₂ start attempt f₂ st = out := by
  have hc := Limits.le_cost hle
  simp only [btFail] at h ⊢
  split at h
  · next hz => rw [dif_pos hz]; exact h
  · next hz =>
      rw [dif_neg hz]
      split at h
      · next hrep => subst h; exact False.elim hd
      · next hrep =>
          split
          · next hrep2 => exact absurd hrep2 (by omega)
          · exact hstep _ _ _ h

theorem btStep_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) {start attempt : Nat} :
    ∀ {fuel₁ fuel₂ pc pos : Nat} {st : BtSt} {out : AttemptOut},
      fuel₁ ≤ fuel₂ →
      btStep re s mo lim₁ start attempt fuel₁ pc pos st = out → out.done →
      btStep re s mo lim₂ start attempt fuel₂ pc pos st = out := by
  have hc := Limits.le_cost hle
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ pc pos st out _ h hd
      rw [btStep] at h
      subst h
      exact False.elim hd
  | succ f ih =>
      intro fuel₂ pc pos st out hf h hd
      obtain ⟨f₂, rfl⟩ : ∃ m, fuel₂ = m + 1 := ⟨fuel₂ - 1, by omega⟩
      have hstep : ∀ pc' pos' (st' : BtSt),
          btStep re s mo lim₁ start attempt f pc' pos' st' = out →
          btStep re s mo lim₂ start attempt f₂ pc' pos' st' = out :=
        fun _ _ _ h' => ih (by omega) h' hd
      have hfail : ∀ (st' : BtSt),
          btFail re s mo lim₁ start attempt f st' = out →
          btFail re s mo lim₂ start attempt f₂ st' = out :=
        fun _ h' => btFail_mono_of hle hd hstep h'
      rw [btStep] at h ⊢
      split at h
      · next hcost => subst h; exact False.elim hd
      · next hcost =>
          split
          · next hcost2 => exact absurd hcost2 (by omega)
          · cases hop : (re.code[pc]!).op <;> simp only [hop] at h ⊢
            case chr | chrCI | cls | any | anyNoNL | bsr | circ
                | doll | dollE | sod | eod | eodn | wordB | notWordB =>
              split at h
              · next hcnd => rw [if_pos hcnd]; exact hstep _ _ _ h
              · next hcnd => rw [if_neg hcnd]; exact hfail _ h
            case circM | dollM =>
              split at h <;> rename_i hz
              · rw [if_pos hz]
                split at h
                · next hcnd => rw [if_pos hcnd]; exact hstep _ _ _ h
                · next hcnd => rw [if_neg hcnd]; exact hfail _ h
              · rw [if_neg hz]
                split at h
                · next hcnd => rw [if_pos hcnd]; exact hstep _ _ _ h
                · next hcnd => rw [if_neg hcnd]; exact hfail _ h
            case split =>
              split at h
              · next hfk => subst h; exact False.elim hd
              · next st₂ hfk => rw [fork_mono hle hfk]; exact hstep _ _ _ h
            case jump => exact hstep _ _ _ h
            case save | repZero | repEnter =>
              split at h
              · next hw => subst h; exact False.elim hd
              · next st₂ hw => rw [writeReg_mono hle hw]; exact hstep _ _ _ h
            case repLoop =>
              split at h
              · next hlo => rw [if_pos hlo]; exact hstep _ _ _ h
              · next hlo =>
                  rw [if_neg hlo]
                  split at h
                  · next hhi => rw [if_pos hhi]; exact hstep _ _ _ h
                  · next hhi =>
                      rw [if_neg hhi]
                      by_cases hg :
                          (re.reps[(re.code[pc]!).arg]!).greedy = true
                      · simp only [if_pos hg] at h ⊢
                        split at h
                        · next hfk => subst h; exact False.elim hd
                        · next st₂ hfk =>
                            rw [fork_mono hle hfk]; exact hstep _ _ _ h
                      · simp only [if_neg hg] at h ⊢
                        split at h
                        · next hfk => subst h; exact False.elim hd
                        · next st₂ hfk =>
                            rw [fork_mono hle hfk]; exact hstep _ _ _ h
            case repNext =>
              split at h
              · next hw => subst h; exact False.elim hd
              · next st₂ hw =>
                  rw [writeReg_mono hle hw]
                  simp only []
                  split at h
                  · next hcnd => rw [if_pos hcnd]; exact hstep _ _ _ h
                  · next hcnd => rw [if_neg hcnd]; exact hstep _ _ _ h
            case accept =>
              split at h
              · next href => rw [if_pos href]; exact hfail _ h
              · next href => rw [if_neg href]; exact h

theorem btLoop_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) {start : Nat} :
    ∀ {steps attempt : Nat} {st : BtSt} {out : RunEnd},
      btLoop re s mo lim₁ start steps attempt st = out → out.done →
      btLoop re s mo lim₂ start steps attempt st = out := by
  have hc := Limits.le_cost hle
  intro steps
  induction steps with
  | zero =>
      intro attempt st out h hd
      rw [btLoop] at h
      subst h
      exact False.elim hd
  | succ n ih =>
      intro attempt st out h hd
      simp only [btLoop] at h ⊢
      split at h
      · next hres => subst h; exact False.elim hd
      · next hres =>
          split
          · next hres2 => exact absurd hres2 (by omega)
          · split at h
            · next e st₂ hbt =>
                rw [btStep_mono hle (by omega) hbt trivial]
                exact h
            · next st₂ hbt => subst h; exact False.elim hd
            · next st₂ hbt =>
                rw [btStep_mono hle (by omega) hbt trivial]
                simp only []
                split at h
                · next hend => rw [if_pos hend]; exact h
                · next hend => rw [if_neg hend]; exact ih h hd

theorem btRun_mono {re : Re} {s : ByteArray} {start : Nat} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) {btCap trailCap : Nat}
    {r : RunResult} (h : btRun re s start mo lim₁ btCap trailCap = r)
    (hr : r.settled) :
    btRun re s start mo lim₂ btCap trailCap = r := by
  have hc := Limits.le_cost hle
  have hm := Limits.le_mem hle
  simp only [btRun] at h ⊢
  split at h
  · next hstart => rw [if_pos hstart]; exact h
  · next hstart =>
      rw [if_neg hstart]
      split at h
      · subst h; exact absurd hr not_settled_exceeded
      · next hsetup =>
          split
          · next hsetup2 =>
              exfalso
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
                at hsetup hsetup2
              omega
          · split at h
            · next st₂ hbl =>
                rw [btLoop_mono hle hbl trivial]
                simp only []
                split at h
                · next hdel => subst h; exact absurd hr not_settled_exceeded
                · next hdel =>
                    split
                    · next hdel2 => exact absurd hdel2 (by omega)
                    · exact h
            · next st₂ hbl =>
                rw [btLoop_mono hle hbl trivial]
                exact h
            · next st₂ hbl => subst h; exact absurd hr not_settled_exceeded

/-! ## The Pike helpers

Same story on the lockstep side: every helper computes its new state from
the state alone and only reads the limits through refusal comparisons, so
an `ok` answer is reproduced verbatim. -/

theorem pikeTake_fill_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) :
    ∀ {k : Nat} {st st' : PikeSt},
      pikeTake.fill lim₁ k st = .ok st' →
      pikeTake.fill lim₂ k st = .ok st' := by
  intro k
  induction k with
  | zero => intro st st' h; rw [pikeTake.fill] at h ⊢; exact h
  | succ n ih =>
      intro st st' h
      rw [pikeTake.fill] at h ⊢
      split at h
      · cases h
      · next m cap hg => rw [chargeGrow_mono hle hg]; exact ih h

theorem pikeTake_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st : PikeSt} {novec : Nat} {res : PikeSt × Nat}
    (h : pikeTake st novec lim₁ = .ok res) :
    pikeTake st novec lim₂ = .ok res := by
  simp only [pikeTake] at h ⊢
  split at h
  · next hfree => rw [if_pos hfree]; exact h
  · next hfree =>
      rw [if_neg hfree]
      split at h
      · cases h
      · next hmax =>
          rw [if_neg hmax]
          split at h
          · cases h
          · next m cap hg =>
              rw [chargeGrow_mono hle hg]
              simp only []
              split at h
              · cases h
              · next st₂ hf => rw [pikeTake_fill_mono hle hf]; exact h

theorem pikeDrop_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st st' : PikeSt} {handle : Nat}
    (h : pikeDrop st handle lim₁ = .ok st') :
    pikeDrop st handle lim₂ = .ok st' := by
  simp only [pikeDrop] at h ⊢
  split at h
  · next hnone => rw [if_pos hnone]; exact h
  · next hnone =>
      rw [if_neg hnone]
      split at h
      · next hz =>
          rw [if_pos hz]
          split at h
          · cases h
          · next m cap hg => rw [chargeGrow_mono hle hg]; exact h
      · next hz => rw [if_neg hz]; exact h

theorem pikeWrite_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st : PikeSt} {novec handle slot : Nat} {value : UInt32}
    {res : PikeSt × Nat}
    (h : pikeWrite st novec handle slot value lim₁ = .ok res) :
    pikeWrite st novec handle slot value lim₂ = .ok res := by
  have hc := Limits.le_cost hle
  simp only [pikeWrite] at h ⊢
  split at h
  · next hrc =>
      rw [if_pos hrc]
      split at h
      · cases h
      · next hcp =>
          split
          · next hcp2 => exact absurd hcp2 (by omega)
          · split at h
            · cases h
            · next st₂ fresh htk =>
                rw [pikeTake_mono hle htk]
                exact h
  · next hrc => rw [if_neg hrc]; exact h

theorem pikeDefer_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st st' : PikeSt} {pc handle : Nat}
    (h : pikeDefer st pc handle lim₁ = .ok st') :
    pikeDefer st pc handle lim₂ = .ok st' := by
  simp only [pikeDefer] at h ⊢
  split at h
  · cases h
  · next m cap hg => rw [chargeGrow_mono hle hg]; exact h

theorem pikePark_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {st st' : PikeSt} {intoNext : Bool} {pc handle : Nat}
    (h : pikePark st intoNext pc handle lim₁ = .ok st') :
    pikePark st intoNext pc handle lim₂ = .ok st' := by
  simp only [pikePark] at h ⊢
  split at h
  · next hnx =>
      rw [if_pos hnx]
      split at h
      · cases h
      · next m cap hg => rw [chargeGrow_mono hle hg]; exact h
  · next hnx =>
      rw [if_neg hnx]
      split at h
      · cases h
      · next m cap hg => rw [chargeGrow_mono hle hg]; exact h

theorem pikeAdd_go_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {intoNext : Bool} {pos : Nat} :
    ∀ {fuel : Nat} {st st' : PikeSt},
      pikeAdd.go re s mo lim₁ intoNext pos fuel st = .ok st' →
      pikeAdd.go re s mo lim₂ intoNext pos fuel st = .ok st' := by
  have hc := Limits.le_cost hle
  intro fuel
  induction fuel with
  | zero => intro st st' h; rw [pikeAdd.go] at h; cases h
  | succ n ih =>
      intro st st' h
      simp only [pikeAdd.go] at h ⊢
      split at h
      · next hemp => rw [if_pos hemp]; exact h
      · next hemp =>
          rw [if_neg hemp]
          split at h
          · next hseen =>
              rw [if_pos hseen]
              split at h
              · cases h
              · next st₂ hdr => rw [pikeDrop_mono hle hdr]; exact ih h
          · next hseen =>
              rw [if_neg hseen]
              split at h
              · cases h
              · next hg =>
                  split
                  · next hg2 => exact absurd hg2 (by omega)
                  · cases hop : (re.code[(st.stk.back!).pc]!).op <;>
                      simp only [hop] at h ⊢
                    case chr | chrCI | cls | any | anyNoNL | accept =>
                      split at h
                      · cases h
                      · next st₂ hpk =>
                          rw [pikePark_mono hle hpk]; exact ih h
                    case bsr =>
                      split at h
                      · cases h
                      · next st₂ hdr =>
                          rw [pikeDrop_mono hle hdr]; exact ih h
                    case split =>
                      split at h
                      · cases h
                      · next st₂ hd1 =>
                          rw [pikeDefer_mono hle hd1]
                          simp only []
                          split at h
                          · cases h
                          · next st₃ hd2 =>
                              rw [pikeDefer_mono hle hd2]; exact ih h
                    case jump | repZero | repEnter =>
                      split at h
                      · cases h
                      · next st₂ hdf =>
                          rw [pikeDefer_mono hle hdf]; exact ih h
                    case save =>
                      split at h
                      · cases h
                      · next st₂ h' hw =>
                          rw [pikeWrite_mono hle hw]
                          simp only []
                          split at h
                          · cases h
                          · next st₃ hdf =>
                              rw [pikeDefer_mono hle hdf]; exact ih h
                    case circ | doll | dollE | sod | eod
                        | eodn | wordB | notWordB =>
                      split at h <;> rename_i hcnd
                      · rw [if_pos hcnd]
                        split at h
                        · cases h
                        · next st₂ hdf =>
                            rw [pikeDefer_mono hle hdf]; exact ih h
                      · rw [if_neg hcnd]
                        split at h
                        · cases h
                        · next st₂ hdr =>
                            rw [pikeDrop_mono hle hdr]; exact ih h
                    case circM | dollM =>
                      split at h <;> rename_i hz
                      all_goals
                        first
                        | rw [if_pos hz]
                        | rw [if_neg hz]
                      all_goals
                        split at h <;> rename_i hcnd
                        · rw [if_pos hcnd]
                          split at h
                          · cases h
                          · next st₂ hdf =>
                              rw [pikeDefer_mono hle hdf]; exact ih h
                        · rw [if_neg hcnd]
                          split at h
                          · cases h
                          · next st₂ hdr =>
                              rw [pikeDrop_mono hle hdr]; exact ih h
                    case repLoop | repNext =>
                      split at h <;> rename_i hgr
                      · rw [if_pos hgr]
                        split at h
                        · cases h
                        · next st₂ hd1 =>
                            rw [pikeDefer_mono hle hd1]
                            simp only []
                            split at h
                            · cases h
                            · next st₃ hd2 =>
                                rw [pikeDefer_mono hle hd2]; exact ih h
                      · rw [if_neg hgr]
                        split at h
                        · cases h
                        · next st₂ hd1 =>
                            rw [pikeDefer_mono hle hd1]
                            simp only []
                            split at h
                            · cases h
                            · next st₃ hd2 =>
                                rw [pikeDefer_mono hle hd2]; exact ih h

theorem pikeAdd_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {intoNext : Bool} {pos pc0 h0 : Nat} {st st' : PikeSt}
    (h : pikeAdd re s mo lim₁ intoNext pos pc0 h0 st = .ok st') :
    pikeAdd re s mo lim₂ intoNext pos pc0 h0 st = .ok st' := by
  simp only [pikeAdd] at h ⊢
  split at h
  · cases h
  · next st₂ hdf =>
      rw [pikeDefer_mono hle hdf]
      exact pikeAdd_go_mono hle h

theorem dropRest_mono {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) :
    ∀ {rest : List Th} {st st' : PikeSt},
      dropRest lim₁ rest st = .ok st' → dropRest lim₂ rest st = .ok st' := by
  intro rest
  induction rest with
  | nil => intro st st' h; simp only [dropRest] at h ⊢; exact h
  | cons th rest ih =>
      intro st st' h
      simp only [dropRest] at h ⊢
      split at h
      · cases h
      · next st₂ hdr => rw [pikeDrop_mono hle hdr]; exact ih h

theorem stepThreads_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) {start pos : Nat} :
    ∀ {threads : List Th} {st : PikeSt} {mh : Nat} {seeding matched : Bool}
      {o : StepOut},
      stepThreads re s mo lim₁ start pos threads st mh seeding matched
        = .ok o →
      stepThreads re s mo lim₂ start pos threads st mh seeding matched
        = .ok o := by
  have hc := Limits.le_cost hle
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched o h
      simp only [stepThreads] at h ⊢
      exact h
  | cons th rest ih =>
      intro st mh seeding matched o h
      simp only [stepThreads] at h ⊢
      split at h
      · cases h
      · next hg =>
          split
          · next hg2 => exact absurd hg2 (by omega)
          · cases hop : (re.code[th.pc]!).op <;> simp only [hop] at h ⊢
            case chr | chrCI | cls | any | anyNoNL =>
              split at h <;> rename_i hcnd
              · rw [if_pos hcnd]
                split at h
                · cases h
                · next st₂ hadd => rw [pikeAdd_mono hle hadd]; exact ih h
              · rw [if_neg hcnd]
                split at h
                · cases h
                · next st₂ hdr => rw [pikeDrop_mono hle hdr]; exact ih h
            case accept =>
              split at h <;> rename_i href
              · rw [if_pos href]
                split at h
                · cases h
                · next st₂ hdr => rw [pikeDrop_mono hle hdr]; exact ih h
              · rw [if_neg href]
                split at h
                · cases h
                · next st₂ hv hw =>
                    rw [pikeWrite_mono hle hw]
                    simp only []
                    split at h
                    · cases h
                    · next st₃ hdr =>
                        rw [pikeDrop_mono hle hdr]
                        simp only []
                        split at h
                        · cases h
                        · next st₄ hrest =>
                            rw [dropRest_mono hle hrest]; exact h
            all_goals
              split at h
              · cases h
              · next st₂ hdr => rw [pikeDrop_mono hle hdr]; exact ih h

theorem pikeSeed_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {start pos : Nat} {st st' : PikeSt}
    (h : pikeSeed re s mo lim₁ start pos st = .ok st') :
    pikeSeed re s mo lim₂ start pos st = .ok st' := by
  have hc := Limits.le_cost hle
  simp only [pikeSeed] at h ⊢
  split at h
  · next hskip => rw [if_pos hskip]; exact h
  · next hskip =>
      rw [if_neg hskip]
      split at h
      · cases h
      · next st₂ sh htk =>
          rw [pikeTake_mono hle htk]
          simp only []
          split at h
          · cases h
          · next hbl =>
              split
              · next hbl2 => exact absurd hbl2 (by omega)
              · exact pikeAdd_mono hle h

theorem pikeLoop_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {start : Nat} {anchored : Bool} {words : Nat} :
    ∀ {steps pos : Nat} {st : PikeSt} {mh : Nat} {seeding matched : Bool}
      {st' : PikeSt} {mh' : Nat} {e : PikeEnd},
      pikeLoop re s mo lim₁ start anchored words steps pos st mh seeding
        matched = (st', mh', e) →
      e ≠ .exceeded →
      pikeLoop re s mo lim₂ start anchored words steps pos st mh seeding
        matched = (st', mh', e) := by
  have hc := Limits.le_cost hle
  intro steps
  induction steps with
  | zero =>
      intro pos st mh seeding matched st' mh' e h hne
      rw [pikeLoop] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, -, he⟩ := h
      exact absurd he.symm hne
  | succ n ih =>
      intro pos st mh seeding matched st' mh' e h hne
      simp only [pikeLoop] at h ⊢
      by_cases hseed : (seeding && (!anchored || pos == start)) = true
      · rw [if_pos hseed] at h ⊢
        split at h
        · next st₂ hps =>
            simp only [Prod.mk.injEq] at h
            obtain ⟨-, -, he⟩ := h
            exact absurd he.symm hne
        · next st₂ hps =>
            rw [pikeSeed_mono hle hps]
            simp only []
            split at h
            · next hw =>
                simp only [Prod.mk.injEq] at h
                obtain ⟨-, -, he⟩ := h
                exact absurd he.symm hne
            · next hw =>
                split
                · next hw2 => exact absurd hw2 (by omega)
                · split at h
                  · next st₃ hst =>
                      simp only [Prod.mk.injEq] at h
                      obtain ⟨-, -, he⟩ := h
                      exact absurd he.symm hne
                  · next o hst =>
                      rw [stepThreads_mono hle hst]
                      simp only []
                      split at h
                      · next hpos => rw [if_pos hpos]; exact h
                      · next hpos =>
                          rw [if_neg hpos]
                          split at h
                          · next hcl => rw [if_pos hcl]; exact h
                          · next hcl => rw [if_neg hcl]; exact ih h hne
      · rw [if_neg hseed] at h ⊢
        simp only [] at h ⊢
        split at h
        · next hw =>
            simp only [Prod.mk.injEq] at h
            obtain ⟨-, -, he⟩ := h
            exact absurd he.symm hne
        · next hw =>
            split
            · next hw2 => exact absurd hw2 (by omega)
            · split at h
              · next st₃ hst =>
                  simp only [Prod.mk.injEq] at h
                  obtain ⟨-, -, he⟩ := h
                  exact absurd he.symm hne
              · next o hst =>
                  rw [stepThreads_mono hle hst]
                  simp only []
                  split at h
                  · next hpos => rw [if_pos hpos]; exact h
                  · next hpos =>
                      rw [if_neg hpos]
                      split at h
                      · next hcl => rw [if_pos hcl]; exact h
                      · next hcl => rw [if_neg hcl]; exact ih h hne

/-- The same fact over the whole answer triple, phrased on the loop's own
projections: the form `pikeRun`'s destructuring lets ask for. -/
theorem pikeLoop_mono_end {re : Re} {s : ByteArray} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    {start : Nat} {anchored : Bool} {words steps pos : Nat} {st : PikeSt}
    {mh : Nat} {seeding matched : Bool} {e : PikeEnd}
    (hend : (pikeLoop re s mo lim₁ start anchored words steps pos st mh
      seeding matched).2.2 = e)
    (hne : e ≠ .exceeded) :
    pikeLoop re s mo lim₂ start anchored words steps pos st mh seeding
        matched =
      pikeLoop re s mo lim₁ start anchored words steps pos st mh seeding
        matched := by
  have h : pikeLoop re s mo lim₁ start anchored words steps pos st mh
      seeding matched =
      ((pikeLoop re s mo lim₁ start anchored words steps pos st mh seeding
          matched).1,
        (pikeLoop re s mo lim₁ start anchored words steps pos st mh seeding
          matched).2.1,
        (pikeLoop re s mo lim₁ start anchored words steps pos st mh seeding
          matched).2.2) := rfl
  exact (pikeLoop_mono hle h (by rw [hend]; exact hne)).trans h.symm

theorem pikeRun_mono {re : Re} {s : ByteArray} {start : Nat} {mo : MOpts}
    {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂) {init : PikeSt}
    {r : RunResult} (h : pikeRun re s start mo lim₁ init = r)
    (hr : r.settled) :
    pikeRun re s start mo lim₂ init = r := by
  have hc := Limits.le_cost hle
  have hm := Limits.le_mem hle
  simp only [pikeRun] at h ⊢
  split at h
  · next hpk => rw [if_pos hpk]; exact h
  · next hpk =>
      rw [if_neg hpk]
      split at h
      · next hstart => rw [if_pos hstart]; exact h
      · next hstart =>
          rw [if_neg hstart]
          split at h
          · subst h; exact absurd hr not_settled_exceeded
          · next hsetup =>
              split
              · next hsetup2 =>
                  exfalso
                  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
                    at hsetup hsetup2
                  omega
              · split at h
                · next heq => subst h; exact absurd hr not_settled_exceeded
                · next heq =>
                    rw [pikeLoop_mono_end hle heq (by simp), heq]
                    exact h
                · next heq =>
                    rw [pikeLoop_mono_end hle heq (by simp), heq]
                    simp only [] at h ⊢
                    split at h
                    · next hbl => subst h; exact absurd hr not_settled_exceeded
                    · next hbl =>
                        split
                        · next hbl2 => exact absurd hbl2 (by omega)
                        · exact h

/-! ## The context gate and the execution semantics

A context call carries its own cost and stack numbers and pins the memory
limit to the reservation, so monotonicity over a context compares two
calls the context admits. `Config.admits` spells out what that means per
configuration; on a plain configuration there is nothing to admit. -/

theorem ctxMatch_mono {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost₁ stack₁ cost₂ stack₂ : Nat}
    (hcost : cost₁ ≤ cost₂) (hcostcap : cost₂ ≤ ctx.costcap)
    (hstack : stack₁ ≤ stack₂) (hstackcap : stack₂ ≤ ctx.stackcap)
    {r : RunResult} (h : ctxMatch ctx s start mo cost₁ stack₁ = r)
    (hr : r.settled) :
    ctxMatch ctx s start mo cost₂ stack₂ = r := by
  have hle : Limits.le ⟨cost₁, stack₁, ctx.memcap⟩
      ⟨cost₂, stack₂, ctx.memcap⟩ :=
    And.intro hcost (And.intro hstack (Nat.le_refl _))
  simp only [ctxMatch] at h ⊢
  split at h
  · subst h; exact absurd hr not_settled_badInput
  · next hlen =>
      rw [if_neg hlen]
      split at h
      · subst h; exact absurd hr not_settled_badInput
      · next hc1 =>
          split
          · next hc2 => exact absurd hc2 (by omega)
          · split at h
            · subst h; exact absurd hr not_settled_badInput
            · next hs1 =>
                split
                · next hs2 => exact absurd hs2 (by omega)
                · split at h
                  · next hpike =>
                      rw [if_pos hpike]
                      subst h
                      rw [pikeRun_mono hle rfl hr]
                  · next hpike =>
                      rw [if_neg hpike]
                      subst h
                      rw [btRun_mono hle rfl hr]

/-- The calls a configuration admits, S-9's side condition: a plain call
is always its own master, while a context call must sit at or below the
baked ceilings with its memory limit equal to the reservation — anything
else is S-7's BadInput, not a monotonicity question. -/
def Config.admits (cfg : Config) (cp : CompiledPat) (lim : Limits) : Prop :=
  match cfg with
  | .plain _ => True
  | .inCtx _ maxlen creation =>
      ∀ ctx, ctxCreate cp 0 maxlen creation = (.ok, some ctx) →
        lim.cost ≤ ctx.costcap ∧ lim.stack ≤ ctx.stackcap ∧
          lim.mem = ctx.memcap

theorem run_mono {cfg : Config} {cp : CompiledPat} {s : ByteArray}
    {start : Nat} {mo : MOpts} {lim₁ lim₂ : Limits}
    (hle : Limits.le lim₁ lim₂)
    (hv₁ : lim₁.valid = true) (hv₂ : lim₂.valid = true)
    (ha₁ : cfg.admits cp lim₁) (ha₂ : cfg.admits cp lim₂)
    (hs : (run cfg cp s start mo lim₁).settled) :
    run cfg cp s start mo lim₂ = run cfg cp s start mo lim₁ := by
  simp only [run, hv₁, hv₂, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at hs ⊢
  by_cases hsz : s.size > ceiling
  · rw [if_pos hsz, if_pos hsz]
  · rw [if_neg hsz] at hs
    rw [if_neg hsz, if_neg hsz]
    cases cfg with
    | plain m =>
        cases m with
        | memo => rfl
        | pike => exact pikeRun_mono hle rfl hs
        | backtrack => exact btRun_mono hle rfl hs
    | inCtx m maxlen creation =>
        simp only [] at hs ⊢
        by_cases hm : (m != cp.re.selected) = true
        · rw [if_pos hm, if_pos hm]
        · rw [if_neg hm] at hs
          rw [if_neg hm, if_neg hm]
          by_cases hv : (!creation.valid) = true
          · rw [if_pos hv, if_pos hv]
          · rw [if_neg hv] at hs
            rw [if_neg hv, if_neg hv]
            rcases hcc : ctxCreate cp 0 maxlen creation with ⟨cst, octx⟩
            cases cst with
            | ok =>
                cases octx with
                | none => rfl
                | some ctx =>
                    obtain ⟨hac₁, has₁, ham₁⟩ := ha₁ ctx hcc
                    obtain ⟨hac₂, has₂, ham₂⟩ := ha₂ ctx hcc
                    rw [hcc] at hs
                    simp only [] at hs ⊢
                    rw [if_neg (show ¬(lim₁.mem != ctx.memcap) = true by
                      simp [ham₁])] at hs
                    rw [if_neg (show ¬(lim₂.mem != ctx.memcap) = true by
                          simp [ham₂]),
                        if_neg (show ¬(lim₁.mem != ctx.memcap) = true by
                          simp [ham₁])]
                    exact ctxMatch_mono (Limits.le_cost hle) hac₂
                      (Limits.le_stack hle) has₂ rfl hs
            | resourceExceeded => rfl
            | badInput => rfl
            | exceedsBudget => rfl

/-- S-9, `exec_monotone`: raising limits never changes a Found or NotFound
answer. Over two valid limit vectors the configuration admits, one at or
below the other, a settled `Exec` at the lower limits is reproduced whole
at the higher ones — outcome, ovector and usage alike. Raising can only
turn ResourceExceeded into something else, never the reverse. -/
theorem exec_monotone {cfg : Config} {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim₁ lim₂ : Limits} (hle : Limits.le lim₁ lim₂)
    (hv₁ : lim₁.valid = true) (hv₂ : lim₂.valid = true)
    (ha₁ : cfg.admits (compileFull p).2 lim₁)
    (ha₂ : cfg.admits (compileFull p).2 lim₂)
    (hs : (Exec cfg p s start mo lim₁).settled) :
    Exec cfg p s start mo lim₂ = Exec cfg p s start mo lim₁ :=
  run_mono hle hv₁ hv₂ ha₁ ha₂ hs

end Pcrevera.Ref
