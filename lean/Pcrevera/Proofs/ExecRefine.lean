import Pcrevera.Proofs.Agreement

/-!
# From the run cores to `Exec` (S-8's outer layer)

The refinement theorems are proved about the run cores, because that is
where the work is; S-8 is stated about `Exec`, because that is the function
the rest of the inventory quantifies over. The step between them is the
validation prefix of `run`, and it is worth writing down once rather than
inside each core's proof: a call whose limits are representable and whose
subject fits the documented cap is exactly its core, so the core's
refinement is `Exec`'s.

The context configurations reduce the same way, through the creation their
own parameters determine, which is why `Exec` needs no separate refinement
argument for them: a context call is a core call on scratch that was
reserved earlier.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- A plain backtracking call is its core, once the request is well
formed. -/
theorem exec_plain_backtrack {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} (hv : lim.valid = true) (hs : s.size ≤ ceiling) :
    Exec (.plain .backtrack) p s start mo lim =
      btRun (compile p) s start mo lim 0 0 := by
  unfold Exec run
  rw [if_neg (by simp [hv, Nat.not_lt.mpr hs])]
  rfl

/-- And a plain Pike call is its core. -/
theorem exec_plain_pike {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} (hv : lim.valid = true) (hs : s.size ≤ ceiling) :
    Exec (.plain .pike) p s start mo lim =
      pikeRun (compile p) s start mo lim {} := by
  unfold Exec run
  rw [if_neg (by simp [hv, Nat.not_lt.mpr hs])]
  rfl

/-- S-8 for the plain backtracking configuration, drawn from the core's
refinement. The core theorem is the argument; this is the wrapper the
inventory names. -/
theorem exec_refines_backtrack {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} (hv : lim.valid = true) (hs : s.size ≤ ceiling)
    (hcore : RefinesMatches (btRun (compile p) s start mo lim 0 0) p s start mo) :
    RefinesMatches (Exec (.plain .backtrack) p s start mo lim) p s start mo := by
  rw [exec_plain_backtrack hv hs]; exact hcore

/-- S-8 for the plain Pike configuration. -/
theorem exec_refines_pike {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} (hv : lim.valid = true) (hs : s.size ≤ ceiling)
    (hcore : RefinesMatches (pikeRun (compile p) s start mo lim {}) p s start mo) :
    RefinesMatches (Exec (.plain .pike) p s start mo lim) p s start mo := by
  rw [exec_plain_pike hv hs]; exact hcore

/-- S-12, `matchers_agree`, at the level DESIGN.md section 6 states it: on a
pattern both configurations may run, each refining `Matches` and each
completing, the two answers are the same answer. Completing is the
sufficient-budget premise — at equal limits the two matchers may
legitimately part company on ResourceExceeded, since they meter different
work. -/
theorem matchers_agree {p : Pat} {s : ByteArray} {start : Nat} {mo : MOpts}
    {limP limB : Limits}
    (hvP : limP.valid = true) (hvB : limB.valid = true) (hs : s.size ≤ ceiling)
    (hpike : RefinesMatches (pikeRun (compile p) s start mo limP {}) p s start mo)
    (hbt : RefinesMatches (btRun (compile p) s start mo limB 0 0) p s start mo)
    (hneP : (Exec (.plain .pike) p s start mo limP).outcome ≠ .resourceExceeded)
    (hneB : (Exec (.plain .backtrack) p s start mo limB).outcome ≠ .resourceExceeded) :
    (Exec (.plain .pike) p s start mo limP).outcome =
        (Exec (.plain .backtrack) p s start mo limB).outcome ∧
      ((Exec (.plain .pike) p s start mo limP).outcome = .matched →
        (Exec (.plain .pike) p s start mo limP).ovec =
          (Exec (.plain .backtrack) p s start mo limB).ovec) :=
  agree_of_refines (exec_refines_pike hvP hs hpike)
    (exec_refines_backtrack hvB hs hbt) hneP hneB

end Pcrevera.Ref
