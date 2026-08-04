import Pcrevera.Ref.Exec

/-!
# S-7: where Exec answers BadInput

`Exec` refuses exactly where `Matches` does — a start offset outside the
subject, a subject past the documented cap — plus the cases that only exist
at execution: limits that break the section 2.4 validity rules, a
configuration the pattern is not eligible for, and, on a context, a subject
past the declared maximum or a call raising a limit or switching
configuration. All of it is decided before any engine work, which is what
makes the characterization a case analysis over the entry points rather
than an argument about runs.

The execution-only side is a proposition rather than a rerun of the
engine's boolean checks, but it states the same conditions, context
creation included: a context configuration whose creation parameters the
engine would refuse does not name a configuration at all, and a call
through it is BadInput the way DESIGN.md section 6 says. The run cores
contribute exactly one refusal of their own — a start offset past the
subject — which is what the three helper iffs record.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- The execution-only BadInput conditions of S-7, per configuration:
invalid limits, the memoized configuration before M9, a plain Pike call on
an ineligible pattern, and on a context every way a call can disagree with
its creation — the wrong matcher, creation parameters the engine refuses,
a memory limit off the reservation, a subject past the declared maximum,
or a limit raised past the baked ceilings. -/
def execOnlyBadInput (cfg : Config) (cp : CompiledPat) (s : ByteArray)
    (lim : Limits) : Prop :=
  lim.valid = false ∨
  match cfg with
  | .plain .memo => True
  | .plain .pike => cp.re.pike = false
  | .plain .backtrack => False
  | .inCtx m maxlen creation =>
      m ≠ cp.re.selected ∨ creation.valid = false ∨
      match ctxCreate cp 0 maxlen creation with
      | (.ok, some ctx) =>
          lim.mem ≠ ctx.memcap ∨ s.size > ctx.maxlen ∨
          lim.cost > ctx.costcap ∨ lim.stack > ctx.stackcap
      | _ => True

/-- The backtracking core refuses exactly a start offset past the subject:
every later branch delivers one of the other three outcomes. -/
theorem btRun_badInput_iff (re : Re) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (btCap trailCap : Nat) :
    (btRun re s start mo lim btCap trailCap).outcome = .badInput ↔
      start > s.size := by
  unfold btRun
  split
  · next h => simp [h]
  · next h =>
    simp only [Nat.not_lt] at *
    constructor
    · intro hout
      exfalso
      revert hout
      split
      · simp
      · split <;> (try split) <;> simp
    · omega

/-- The Pike core adds one refusal of its own: an ineligible pattern. -/
theorem pikeRun_badInput_iff (re : Re) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (init : PikeSt) :
    (pikeRun re s start mo lim init).outcome = .badInput ↔
      (re.pike = false ∨ start > s.size) := by
  unfold pikeRun
  split
  · next h =>
    simp only [Bool.not_eq_true'] at h
    simp [h]
  · next h =>
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h
    split
    · next h2 => simp [h2]
    · next h2 =>
      simp only [Nat.not_lt] at *
      constructor
      · intro hout
        exfalso
        revert hout
        split
        · simp
        · split <;> (try split) <;> simp
      · rintro (hc | hc)
        · simp [h] at hc
        · omega

/-- A context call refuses its own three checks, and past them only the
start offset is left: the Pike branch only runs on an eligible pattern, so
the core's eligibility refusal never fires through a context. -/
theorem ctxMatch_badInput_iff (ctx : Ctx) (s : ByteArray) (start : Nat)
    (mo : MOpts) (cost stack : Nat) :
    (ctxMatch ctx s start mo cost stack).outcome = .badInput ↔
      (s.size > ctx.maxlen ∨ cost > ctx.costcap ∨ stack > ctx.stackcap ∨
        start > s.size) := by
  unfold ctxMatch
  split
  · next h => simp [h]
  · next h1 =>
    split
    · next h => simp [h]
    · next h2 =>
      split
      · next h => simp [h]
      · next h3 =>
        split
        · next hp =>
          rw [pikeRun_badInput_iff]
          simp [hp]
          omega
        · next hp =>
          rw [btRun_badInput_iff]
          omega

/-- S-7, `exec_badinput_iff`: Exec answers BadInput exactly where Matches
does — the start offset and subject-cap refusals — plus the execution-only
conditions of `execOnlyBadInput`. -/
theorem exec_badinput_iff (cfg : Config) (p : Pat) (s : ByteArray)
    (start : Nat) (mo : MOpts) (lim : Limits) :
    (Exec cfg p s start mo lim).outcome = .badInput ↔
      (start > s.size ∨ s.size > ceiling ∨
        execOnlyBadInput cfg (compileFull p).2 s lim) := by
  unfold Exec run execOnlyBadInput
  split
  · next h =>
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    constructor
    · intro _
      rcases h with h | h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inl h)
    · intro _
      rfl
  · next h =>
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      not_or, Bool.not_eq_false] at h
    obtain ⟨hvalid, hsize⟩ := h
    match cfg with
    | .plain .memo => simp
    | .plain .pike =>
        rw [pikeRun_badInput_iff]
        constructor
        · rintro (hc | hc)
          · exact .inr (.inr (.inr hc))
          · exact .inl hc
        · rintro (hc | hc | hc | hc)
          · exact .inr hc
          · exact absurd hc hsize
          · simp [hvalid] at hc
          · exact .inl hc
    | .plain .backtrack =>
        rw [btRun_badInput_iff]
        constructor
        · exact .inl
        · rintro (hc | hc | hc | hc)
          · exact hc
          · exact absurd hc hsize
          · simp [hvalid] at hc
          · exact hc.elim
    | .inCtx m maxlen creation =>
        dsimp only
        split
        · next hm =>
          simp only [bne_iff_ne] at hm
          simp [hm]
        · next hm =>
          simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hm
          split
          · next hc =>
            simp only [Bool.not_eq_true'] at hc
            simp [hc]
          · next hc =>
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
            cases ctxCreate (compileFull p).2 0 maxlen creation with
            | mk status held =>
              match status, held with
              | .ok, some ctx =>
                  dsimp only
                  split
                  · next hmem =>
                    simp only [bne_iff_ne] at hmem
                    simp [hmem]
                  · next hmem =>
                    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hmem
                    rw [ctxMatch_badInput_iff]
                    simp [hvalid, hm, hc, hmem, hsize]
                    omega
              | .ok, none => simp
              | .resourceExceeded, _ => simp
              | .badInput, _ => simp
              | .exceedsBudget, _ => simp

end Pcrevera.Ref
