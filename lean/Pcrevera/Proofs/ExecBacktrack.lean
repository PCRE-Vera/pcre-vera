import Pcrevera.Proofs.Refine
import Pcrevera.Proofs.ExecRefine

/-!
# S-8 for the backtracking configuration

`btRun_refines_matches` is the argument, `exec_refines_backtrack` is the
wrapper, and this is where the two meet: the internal plain-backtracking
configuration refines the specification, for every wave 1 pattern the
parser can produce, at every start offset and under every combination of
match options.

The three side conditions are the ones the development names and the
parser satisfies: `Wf` collects the shapes a parse never emits (an
alternation with no branches, a quantifier bound at the u32 sentinel, a
capture slot outside the ovector window), the subject cap is DESIGN.md
section 2.4's, and the wrap bound keeps a repetition's counter register
faithful to the count the specification threads — quantifiers stop at
65535 and subjects at the cap, so it holds wherever the two other
conditions do.
-/

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine

/-- The core refinement, in the vocabulary the agreement corollary uses. -/
theorem btRun_refinesMatches {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} {btCap trailCap : Nat}
    (hw : Wf p) (hs : s.size ≤ ceiling)
    (hwrap : Spec.suffFuel s.size p.root < none32) :
    RefinesMatches (btRun (compile p) s start mo lim btCap trailCap)
      p s start mo :=
  btRun_refines_matches p s start mo lim btCap trailCap hw hs hwrap

/-- S-8, `exec_refines`, for the internal plain-backtracking
configuration: whenever it answers Found or NotFound, that answer is
`Matches`, and it answers BadInput exactly where `Matches` does. -/
theorem exec_refines_backtrack_wf {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hwrap : Spec.suffFuel s.size p.root < none32) :
    RefinesMatches (Exec (.plain .backtrack) p s start mo lim) p s start mo :=
  exec_refines_backtrack hv hs (btRun_refinesMatches hw hs hwrap)

/-- And the same statement spelled out, so a reader who wants the three
clauses without unfolding `RefinesMatches` can see them. -/
theorem exec_backtrack_found {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hwrap : Spec.suffFuel s.size p.root < none32)
    (hout : (Exec (.plain .backtrack) p s start mo lim).outcome = .matched) :
    Spec.Matches p s start mo =
      .found (Exec (.plain .backtrack) p s start mo lim).ovec :=
  (exec_refines_backtrack_wf hv hw hs hwrap).1 hout

theorem exec_backtrack_notFound {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hwrap : Spec.suffFuel s.size p.root < none32)
    (hout : (Exec (.plain .backtrack) p s start mo lim).outcome = .noMatch) :
    Spec.Matches p s start mo = .notFound :=
  (exec_refines_backtrack_wf hv hw hs hwrap).2.1 hout

end Pcrevera.Ref
