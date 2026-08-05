import Pcrevera.Proofs.Refine
import Pcrevera.Proofs.ExecRefine

/-!
# S-8 for the backtracking configuration

`btRun_refines_matches` is the argument, `exec_refines_backtrack` is the
wrapper, and this is where the two meet: the internal plain-backtracking
configuration refines the specification, for every wave 1 pattern the
parser can produce, at every start offset and under every combination of
match options.

Two side conditions travel with it. `Wf` collects the shapes a parse never
emits — an alternation with no branches, a quantifier bound past MAX_QUANT,
a capture slot outside the ovector window — and the subject cap is
DESIGN.md section 2.4's.

The counter-wrap bound that used to travel as a third is gone, discharged
rather than dropped. Keeping a repetition's counter register faithful to
the count the specification threads needs a bound per repetition, and
`Wf.repCap_lt` proves that one from the two conditions above: MAX_QUANT
rounds plus one per byte of the subject is about `2 ^ 31`, half of what a
`UInt32` holds. Reading the same need off the search's fuel was the
overclaim it replaces — fuel adds across sibling repetitions, so `a*b*`
at the longest admissible subject exceeded the sentinel while every
counter in it stayed well inside.
-/

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine

/-- The core refinement, in the vocabulary the agreement corollary uses. -/
theorem btRun_refinesMatches {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} {btCap trailCap : Nat}
    (hw : Wf p) (hs : s.size ≤ ceiling) :
    RefinesMatches (btRun (compile p) s start mo lim btCap trailCap)
      p s start mo :=
  btRun_refines_matches p s start mo lim btCap trailCap hw hs

/-- S-8, `exec_refines`, for the internal plain-backtracking
configuration: whenever it answers Found or NotFound, that answer is
`Matches`, and it answers BadInput exactly where `Matches` does. -/
theorem exec_refines_backtrack_wf {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling) :
    RefinesMatches (Exec (.plain .backtrack) p s start mo lim) p s start mo :=
  exec_refines_backtrack hv hs (btRun_refinesMatches hw hs)

/-- And the same statement spelled out, so a reader who wants the three
clauses without unfolding `RefinesMatches` can see them. -/
theorem exec_backtrack_found {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hout : (Exec (.plain .backtrack) p s start mo lim).outcome = .matched) :
    Spec.Matches p s start mo =
      .found (Exec (.plain .backtrack) p s start mo lim).ovec :=
  (exec_refines_backtrack_wf hv hw hs).1 hout

theorem exec_backtrack_notFound {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits}
    (hv : lim.valid = true) (hw : Wf p) (hs : s.size ≤ ceiling)
    (hout : (Exec (.plain .backtrack) p s start mo lim).outcome = .noMatch) :
    Spec.Matches p s start mo = .notFound :=
  (exec_refines_backtrack_wf hv hw hs).2.1 hout

end Pcrevera.Ref
