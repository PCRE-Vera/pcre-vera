import Pcrevera.Proofs.ExecPike
import Pcrevera.Proofs.BadInput

/-!
# S-8 for the context configurations

The two plain configurations are not the whole of `Config`. A context
configuration runs the same core on scratch that was reserved earlier, and
the core theorems are stated over an arbitrary starting scratch — an
arbitrary pair of capacities on the backtracking side, an arbitrary
`PikeSt` on the lockstep one — so the refinement carries across with the
run itself. What has to be said carefully is which clause carries.

S-8 asks that whenever `Exec cfg` answers Found or NotFound, that answer is
`Matches`. It does not ask for the third clause the two plain wrappers can
also offer, that BadInput coincides — and on a context it must not, because
a context refuses calls the specification has no opinion about at all: the
wrong matcher, creation parameters the engine declines, a memory limit off
the reservation, a subject past the declared maximum, a limit raised past
what creation paid for. Those are S-7's business, and `exec_badinput_iff`
is where they are characterized. So the statement here is exactly the two
clauses the inventory names.
-/

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine

/-- S-8's own conclusion: the answers a run completes on are the
specification's. The BadInput clause `RefinesMatches` also carries is left
to S-7, which is where the execution-only refusals live. -/
def RefinesAnswers (r : RunResult) (p : Pat) (s : ByteArray) (start : Nat)
    (mo : MOpts) : Prop :=
  (r.outcome = .matched → Spec.Matches p s start mo = .found r.ovec) ∧
  (r.outcome = .noMatch → Spec.Matches p s start mo = .notFound)

theorem RefinesMatches.answers {r : RunResult} {p : Pat} {s : ByteArray}
    {start : Nat} {mo : MOpts} (h : RefinesMatches r p s start mo) :
    RefinesAnswers r p s start mo := ⟨h.1, h.2.1⟩

/-- Creation stores the pattern it was handed, so a created context runs
the program its parameters named. -/
theorem ctxCreate_cp {cp : CompiledPat} {mcfg maxlen : Nat} {lim : Limits}
    {ctx : Ctx} (h : ctxCreate cp mcfg maxlen lim = (.ok, some ctx)) :
    ctx.cp = cp := by
  simp only [ctxCreate] at h
  repeat' (split at h; first | simp at h | skip)
  all_goals (first | (cases h; rfl) | simp at h)

/-- A context call is its core on reserved scratch, so its answers are the
core's. The `usage` a context reports is the reservation rather than the
transient peak, which is what `ctxMatch` overwrites — and neither clause
reads the usage. -/
theorem ctxMatch_refinesAnswers {ctx : Ctx} {p : Pat} {s : ByteArray}
    {start : Nat} {mo : MOpts} {cost stack : Nat}
    (hre : ctx.cp.re = compile p)
    (hbt : ∀ btCap trailCap lim,
      RefinesAnswers (btRun (compile p) s start mo lim btCap trailCap)
        p s start mo)
    (hpike : ∀ (init : PikeSt) lim,
      RefinesAnswers (pikeRun (compile p) s start mo lim init) p s start mo) :
    RefinesAnswers (ctxMatch ctx s start mo cost stack) p s start mo := by
  unfold ctxMatch
  split
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · split
    · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
    · split
      · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
      · simp only []
        split
        · next hp =>
          have := hpike
            { clistCap := ctx.listsCap, nlistCap := ctx.listsCap
              stkCap := ctx.stkCap, poolCap := ctx.poolCap
              rcCap := ctx.tablesCap, freeCap := ctx.tablesCap }
            ⟨cost, stack, ctx.memcap⟩
          rw [hre] at *
          exact ⟨fun h => this.1 h, fun h => this.2 h⟩
        · next hp =>
          have := hbt ctx.btCap ctx.trailCap ⟨cost, stack, ctx.memcap⟩
          rw [hre] at *
          exact ⟨fun h => this.1 h, fun h => this.2 h⟩

/-- S-8 over the whole of `Config`: every configuration, plain or behind a
context, answers `Matches` whenever it answers at all. The two plain arms
are the wrappers already proved; the context arms reduce to the same cores
through the creation their own parameters determine. -/
theorem exec_refinesAnswers {cfg : Config} {p : Pat} {s : ByteArray}
    {start : Nat} {mo : MOpts} {lim : Limits}
    (hw : Wf p) (hs : s.size ≤ ceiling) :
    RefinesAnswers (Exec cfg p s start mo lim) p s start mo := by
  have hbt : ∀ btCap trailCap lim',
      RefinesAnswers (btRun (compile p) s start mo lim' btCap trailCap)
        p s start mo :=
    fun _ _ _ => (btRun_refinesMatches hw hs).answers
  have hpk : ∀ (init : PikeSt) lim', (compile p).pike = true →
      RefinesAnswers (pikeRun (compile p) s start mo lim' init) p s start mo :=
    fun _ _ he => (pikeRun_refinesMatches hw hs he).answers
  unfold Exec run
  split
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · match cfg with
    | .plain .memo =>
        exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
    | .plain .pike =>
        by_cases he : (compile p).pike = true
        · exact hpk {} lim he
        · simp only [Bool.not_eq_true] at he
          have : (pikeRun (compile p) s start mo lim {}).outcome = .badInput :=
            (pikeRun_badInput_iff _ _ _ _ _ _).mpr (.inl he)
          exact ⟨fun h => absurd (this ▸ h) (by simp),
                 fun h => absurd (this ▸ h) (by simp)⟩
    | .plain .backtrack => exact hbt 0 0 lim
    | .inCtx m maxlen creation =>
        dsimp only
        split
        · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        · split
          · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
          · split
            · next ctx hcc =>
              split
              · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
              · refine ctxMatch_refinesAnswers ?_ hbt ?_
                · exact congrArg CompiledPat.re (ctxCreate_cp hcc)
                · intro init lim'
                  by_cases he : (compile p).pike = true
                  · exact hpk init lim' he
                  · simp only [Bool.not_eq_true] at he
                    have : (pikeRun (compile p) s start mo lim' init).outcome
                        = .badInput :=
                      (pikeRun_badInput_iff _ _ _ _ _ _).mpr (.inl he)
                    exact ⟨fun h => absurd (this ▸ h) (by simp),
                           fun h => absurd (this ▸ h) (by simp)⟩
            · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩

end Pcrevera.Ref
