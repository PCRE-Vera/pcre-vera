import Pcrevera.Proofs.ExecContext
import Pcrevera.Proofs.BtBounds
import Pcrevera.Proofs.ReWfCompile

/-!
# S-12 with its budgets discharged

`matchers_agree_wf` asks that neither run blew its budget, and that premise
is inherent — two matchers metering different work may legitimately part
company on ResourceExceeded, so agreement is a sufficient-budget statement
or it is nothing. What the inventory promises on top is that the premise is
*discharged* from certificates: give each matcher limits at or above its
own analyzer's bounds and neither can refuse, so the agreement follows from
the certificates rather than from an assumption about the runs.

That is what this file does: no hypothesis below mentions how a run ended.
The lockstep side needs nothing but its accepted certificate, since
`pikeRun_inBudget` covers every program the checker admits. The
backtracking side is the one still bounded by the composition, and it is
what narrows the statement — its sufficiency is proved for the programs
BOUNDS.md sections 4.1 to 4.3 cover, so the two class conditions have to
hold at once.

They intersect more tightly than either alone. Eligibility asks that every
row of the repetition table be a pure star; the composition asks that every
repeat region begin with a split, which is the optional item, and an
optional item claims no row. So what both admit is the patterns whose only
quantifiers are `?` and `??`, with groups and alternations above them
freely — `(a|b)?c` is one. Widening it is not a matter of restating
anything here: it waits on section 4.4, with the rest of the backtracking
family.
-/

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine

/-- S-12 with both budgets discharged from certificates: on a pattern both
matchers' classes admit, limits at or above each matcher's own bounds make
the two agree, with nothing assumed about how either run ended. -/
theorem matchers_agree_sufficient {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {limP limB : Limits} {certP certB : Cert}
    (hvP : limP.valid = true) (hvB : limB.valid = true) (hw : Wf p)
    (hfits : PatFits p) (hcov : Covered p.root)
    (hs : s.size ≤ ceiling) (hpike : (compile p).pike = true)
    (hstart : start ≤ s.size)
    -- the lockstep side's certificate and budget
    (hcertP : pikeCheck (compile p) certP = .crOk)
    (hcostP : certP.cost.val s.size ≤ limP.cost)
    (hmemP : certP.mem.val s.size ≤ limP.mem)
    -- the backtracking side's, on the class its composition covers: an
    -- accepted certificate, the region tree read as groups, alternations and
    -- optional items, the program's own two shape facts, and limits at or
    -- above all three of its bounds
    (hcertB : certCheck (compile p) .backtrack certB = .crOk)
    (hopt : ∀ j, j < (compile p).regions.size →
      ((compile p).regions[j]!).kind = .«repeat» →
      ((compile p).code[((compile p).regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < (compile p).regions.size →
      (((compile p).regions[j]!).kind = .alt ∨
        ((compile p).regions[j]!).kind = .«repeat») →
      ((compile p).regions[j]!).hi < (compile p).code.size)
    (hlast : ((compile p).code[(compile p).code.size - 1]!).op = .accept)
    (hmemB : limB.mem ≤ ceiling)
    (hcostB : certB.cost.val s.size ≤ limB.cost)
    (hmemBb : certB.mem.val s.size ≤ limB.mem)
    (hstackB : certB.stack.val s.size ≤ limB.stack) :
    (Exec (.plain .pike) p s start mo limP).outcome =
        (Exec (.plain .backtrack) p s start mo limB).outcome ∧
      ((Exec (.plain .pike) p s start mo limP).outcome = .matched →
        (Exec (.plain .pike) p s start mo limP).ovec =
          (Exec (.plain .backtrack) p s start mo limB).ovec) := by
  have hwf : ReWf (compile p) := compile_reWf hcov hfits
  have hneP : (Exec (.plain .pike) p s start mo limP).outcome ≠
      .resourceExceeded := by
    rw [exec_plain_pike hvP hs]
    exact pikeRun_inBudget hwf hstart hcertP hcostP hmemP
  have hneB : (Exec (.plain .backtrack) p s start mo limB).outcome ≠
      .resourceExceeded := by
    rw [exec_plain_backtrack hvB hs]
    exact btRun_inBudget_forward hcertB hopt hends hlast hmemB hcostB hmemBb
      hstackB
  exact matchers_agree_wf hvP hvB hw hs hpike hneP hneB

end Pcrevera.Ref
