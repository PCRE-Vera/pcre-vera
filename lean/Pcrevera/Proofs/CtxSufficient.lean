import Pcrevera.Proofs.CtxReserve
import Pcrevera.Proofs.ValLength

/-!
# What a context's one memory question buys (towards S-11)

DESIGN.md section 2.4 asks the memory question once, at creation, and
answers it for every call the context will ever admit. That only works
because the bound does not fall as the subject grows: the reservation is
`worstCaseMemory` at the declared maximum, a call runs with that number as
its memory limit whatever its own subject length, and the per-call
requirement at the shorter length sits underneath it.

This file proves that covering fact and then draws S-11 from it. The
sufficiency of the run itself stays where it belongs — with the per-matcher
bound theorems — so it enters here as a hypothesis about the call the
context makes, and what is added is the context-specific half: the memory
component a context call runs under is the one creation reserved, and it is
enough.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- A context's reservation covers every subject it admits. -/
theorem ctx_memcap_covers {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {n : Nat}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hbase : ∀ cert, rePick cp = some cert → 1 ≤ cert.mem.base)
    (hn : n ≤ maxlen)
    (hok : (reMem cp mcfg n).status = .ok) :
    (reMem cp mcfg n).value ≤ ctx.memcap := by
  obtain ⟨_, hcap, hstatus⟩ := ctx_resident_eq_reservation hcreate
  rw [hcap]
  exact reMem_mono_length hbase hn hok hstatus

/-- And the declared maximum is what a call is held to, so the covering
fact applies to every call that gets past the guards. -/
theorem ctxMatch_memcap_covers {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hbase : ∀ cert, rePick cp = some cert → 1 ≤ cert.mem.base)
    (hadmit : s.size ≤ ctx.maxlen)
    (hmax : ctx.maxlen = maxlen)
    (hok : (reMem cp mcfg s.size).status = .ok) :
    (reMem cp mcfg s.size).value ≤ ctx.memcap :=
  ctx_memcap_covers hcreate hbase (hmax ▸ hadmit) hok

/-- S-11, `ctx_sufficient`: conditional on creation having succeeded, a
context whose per-call limits sit at or above the analyzer's bounds never
answers ResourceExceeded on a call it admits.

The run's own sufficiency is the premise `hsuff`, stated about the limits
the context call actually passes down — cost and stack as the caller gave
them, memory pinned to the reservation, which is DESIGN.md section 2.4's
rule that memory has no per-call role on a context. What this theorem adds
is that the pinned number is at or above the per-call memory bound, so a
caller who satisfied the cost and stack bounds has satisfied all three. -/
theorem ctx_sufficient {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost stack : Nat}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hbase : ∀ cert, rePick cp = some cert → 1 ≤ cert.mem.base)
    (hmax : ctx.maxlen = maxlen)
    (hadmit : s.size ≤ ctx.maxlen)
    (hcostcap : cost ≤ ctx.costcap)
    (hstackcap : stack ≤ ctx.stackcap)
    (hmemok : (reMem cp mcfg s.size).status = .ok)
    (hcp : ctx.cp = cp)
    (hsuff : ∀ lim' : Limits,
      (reMem cp mcfg s.size).value ≤ lim'.mem →
      lim'.cost = cost → lim'.stack = stack →
      (if ctx.cp.re.pike then
          pikeRun ctx.cp.re s start mo lim'
            { clistCap := ctx.listsCap, nlistCap := ctx.listsCap
              stkCap := ctx.stkCap, poolCap := ctx.poolCap
              rcCap := ctx.tablesCap, freeCap := ctx.tablesCap }
        else btRun ctx.cp.re s start mo lim' ctx.btCap ctx.trailCap).outcome ≠
          .resourceExceeded) :
    (ctxMatch ctx s start mo cost stack).outcome ≠ .resourceExceeded := by
  have hcovers : (reMem cp mcfg s.size).value ≤ ctx.memcap :=
    ctxMatch_memcap_covers hcreate hbase hadmit hmax hmemok
  unfold ctxMatch
  rw [if_neg (by simpa using Nat.not_lt.mpr hadmit),
      if_neg (by simpa using Nat.not_lt.mpr hcostcap),
      if_neg (by simpa using Nat.not_lt.mpr hstackcap)]
  subst hcp
  simpa using hsuff ⟨cost, stack, ctx.memcap⟩ hcovers rfl rfl

end Pcrevera.Ref
