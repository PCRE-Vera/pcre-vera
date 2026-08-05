import Pcrevera.Proofs.PikeRefine
import Pcrevera.Proofs.ExecBacktrack

/-!
# S-8 for the lockstep configuration, and S-12 with nothing left to assume

`pikeRun_refines_matches` is the argument and `exec_refines_pike` the
wrapper; this is where the two meet, as `ExecBacktrack.lean` does for the
other matcher.

The lockstep matcher adds one side condition to the three the backtracking
half carries: the program is eligible. A program `pike_ok` refuses is one
the matcher will not run at all, and the specification has no opinion about
that refusal, so the premise belongs in the statement rather than in the
conclusion.

With both halves in hand `matchers_agree` loses the two facts it used to
take. What is left of it is the premise that was always inherent — that
neither run blew its budget — since two matchers metering different work
may legitimately part company on ResourceExceeded.
-/

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine

/-- The core refinement, in the vocabulary the agreement corollary uses. -/
theorem pikeRun_refinesMatches {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} {init : PikeSt}
    (hw : Wf p) (hs : s.size ≤ ceiling) (hpike : (compile p).pike = true)
    (hwrap : Spec.suffFuel s.size p.root < none32) :
    RefinesMatches (pikeRun (compile p) s start mo lim init) p s start mo :=
  pikeRun_refines_matches p s start mo lim init hw hs hpike hwrap

/-- S-8, `exec_refines`, for the lockstep configuration: whenever it
answers Found or NotFound, that answer is `Matches`, and it answers
BadInput exactly where `Matches` does. -/
theorem exec_refines_pike_wf {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hpike : (compile p).pike = true)
    (hwrap : Spec.suffFuel s.size p.root < none32) :
    RefinesMatches (Exec (.plain .pike) p s start mo lim) p s start mo :=
  exec_refines_pike hv hs (pikeRun_refinesMatches hw hs hpike hwrap)

/-- And the same statement spelled out, so a reader who wants the clauses
without unfolding `RefinesMatches` can see them. -/
theorem exec_pike_found {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hpike : (compile p).pike = true)
    (hwrap : Spec.suffFuel s.size p.root < none32)
    (hout : (Exec (.plain .pike) p s start mo lim).outcome = .matched) :
    Spec.Matches p s start mo =
      .found (Exec (.plain .pike) p s start mo lim).ovec :=
  (exec_refines_pike_wf hv hw hs hpike hwrap).1 hout

theorem exec_pike_notFound {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hpike : (compile p).pike = true)
    (hwrap : Spec.suffFuel s.size p.root < none32)
    (hout : (Exec (.plain .pike) p s start mo lim).outcome = .noMatch) :
    Spec.Matches p s start mo = .notFound :=
  (exec_refines_pike_wf hv hw hs hpike hwrap).2.1 hout

/-- S-12 with nothing left to assume about either matcher: on a wave 1
pattern the lockstep matcher may run, the two configurations answer the
same thing wherever both complete, ovector included. -/
theorem matchers_agree_wf {p : Pat} {s : ByteArray} {start : Nat} {mo : MOpts}
    {limP limB : Limits}
    (hvP : limP.valid = true) (hvB : limB.valid = true) (hw : Wf p)
    (hs : s.size ≤ ceiling) (hpike : (compile p).pike = true)
    (hwrap : Spec.suffFuel s.size p.root < none32)
    (hneP : (Exec (.plain .pike) p s start mo limP).outcome ≠ .resourceExceeded)
    (hneB : (Exec (.plain .backtrack) p s start mo limB).outcome ≠
      .resourceExceeded) :
    (Exec (.plain .pike) p s start mo limP).outcome =
        (Exec (.plain .backtrack) p s start mo limB).outcome ∧
      ((Exec (.plain .pike) p s start mo limP).outcome = .matched →
        (Exec (.plain .pike) p s start mo limP).ovec =
          (Exec (.plain .backtrack) p s start mo limB).ovec) :=
  matchers_agree hvP hvB hs (pikeRun_refinesMatches hw hs hpike hwrap)
    (btRun_refinesMatches hw hs hwrap) hneP hneB

end Pcrevera.Ref
