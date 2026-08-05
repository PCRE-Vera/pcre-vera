import Pcrevera.Proofs.ExecContext
import Pcrevera.Proofs.BtBounds
import Pcrevera.Proofs.ReWfCompile
import Pcrevera.Proofs.RepCompile

/-!
# S-12 with its budgets discharged

`matchers_agree_wf` asks that neither run blew its budget, and that premise
is inherent — two matchers metering different work may legitimately part
company on ResourceExceeded, so agreement is a sufficient-budget statement
or it is nothing. What the inventory promises on top is that the premise is
*discharged* from certificates: give each matcher limits at or above its
own analyzer's bounds — and, on the backtracking side, a memory limit under
the allocation ceiling, which is what makes the growth schedule double — and
neither can refuse, so the agreement follows from the certificates rather
than from an assumption about the runs.

That is what this file does: no hypothesis below mentions how a run ended.
Each side needs its own accepted certificate and nothing about the other, and
the two classes no longer intersect down to something smaller than either.
`pikeRun_inBudget` covers every program the lockstep checker admits, and
`btRun_inBudget_counted` covers every program the backtracking checker admits,
BOUNDS.md section 4.4 included. So the only class of patterns either half
still rules out is the one the lockstep matcher turns away at its own door.

What the backtracking side asks of the program is `ReRules`, the six rules
neither `cert_shape` nor `certCheck` checks — and it no longer asks the caller
for them. `compile_reRules` reads all six off `Ref.compile`, from the same
three pattern hypotheses the lockstep side already wants, so what used to be
six conditions on the compiled form is now nothing at all.

So the only class condition left is eligibility, and it narrows honestly —
`pike_ok` refuses `\R`, every bounded quantifier, and any star whose body can
finish an iteration without consuming, because those are the programs the
lockstep matcher declines at the door. `a*b*` and `(a|b)*c` are in, where the
intersection this statement used to carry admitted only patterns that reach no
repetition table row at all. `a{2,5}b` is still out, and it is out for the
lockstep reason alone: its backtracking bound is proved, and there is simply
no second run to agree with.

Everything else in the list below is a condition rather than a class — the
pattern's own well-formedness and size clauses, an accepted certificate per
side, and limits at or above what each certificate names. A caller can check
all of them, and none of them is about the bytecode.
-/

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine

/-- S-12 with both budgets discharged from certificates: on an eligible
pattern, limits at or above each matcher's own bounds — with the backtracking
side's memory limit inside the allocation ceiling — make the two agree, with
nothing assumed about how either run ended. -/
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
    -- the backtracking side's: an accepted certificate, and limits at or
    -- above all three of its bounds. The rules the checker does not ask
    -- about are read off the compiler rather than asked for.
    (hcertB : certCheck (compile p) .backtrack certB = .crOk)
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
    exact btRun_inBudget_counted hcertB (compile_reRules hw hcov hfits) hmemB
      hcostB hmemBb hstackB
  exact matchers_agree_wf hvP hvB hw hs hpike hneP hneB

end Pcrevera.Ref
