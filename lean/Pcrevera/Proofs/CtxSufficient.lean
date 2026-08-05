import Pcrevera.Proofs.CtxReserve
import Pcrevera.Proofs.ValLength
import Pcrevera.Proofs.PikeBounds
import Pcrevera.Proofs.BtBounds
import Pcrevera.Proofs.RepRun

/-!
# What a context's one memory question buys (towards S-11)

DESIGN.md section 2.4 asks the memory question once, at creation, and
answers it for every call the context will ever admit. That only works
because the bound does not fall as the subject grows: the reservation is
`worstCaseMemory` at the declared maximum, a call runs with that number as
its memory limit whatever its own subject length, and the per-call
requirement at the shorter length sits underneath it.

This file proves that covering fact and then draws S-11 from it, on both
paths and with no premise about how a run ends.

The lockstep path was the easy one: `pikeRun_inBudget_ctx` prices a call at
whatever scratch it was handed, `ctx_created_caps` says what creation handed
it, and the two meet at the very state `ctx_match` builds.

The backtracking path took two changes to the section 5 account, both made
for this. Its claim numbers and its capacity numbers used to be the same
numbers, and a context parts them: creation reserves at the declared maximum
while a call is priced at its own subject length. And its memory reading used
to be an equation the meter satisfies outright, which a preallocated call
breaks — its meter was never told about the arrays it was handed. `Within`
now carries both, a capacity beside each claim and the reservation the call
arrived with, and what the second costs is the argument that the declared
array maxima never clamp a growth step: a call that buys its own scratch
reads that off the meter, and one that arrived with it reads it off the
capacities instead.

What comes out is the better statement rather than a weaker one. A context
call's growth allowance is already paid for, so the cost a caller has to
supply is the certificate's bound at its own subject length, exactly as for a
plain call.
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

/-- A bound that answers answers the polynomial's own value: the roof it is
held to was cleared, so nothing but `polyValue`'s reading is left. -/
theorem bound_ok_val {which : Poly} {roof n : Nat}
    (h : (if (polyValue which n).ok = true ∧ (polyValue which n).value > roof then
        Bound.exceeds else polyValue which n).ok = true) :
    (if (polyValue which n).ok = true ∧ (polyValue which n).value > roof then
        Bound.exceeds else polyValue which n).value = which.val n := by
  by_cases hc : (polyValue which n).ok = true ∧ (polyValue which n).value > roof
  · rw [if_pos hc] at h
    simp [Bound.exceeds] at h
  · rw [if_neg hc] at h ⊢
    refine polyValue_ok ?_
    cases hpv : polyValue which n with
    | mk ok value =>
        rw [hpv] at h
        cases ok
        · simp at h
        · rfl

/-- So an accessor's number is the selected certificate's bound at that
length, which is what lets a caller's check be read as the core's own
hypothesis. -/
theorem reCost_val {cp : CompiledPat} {cert : Cert} {mcfg n : Nat}
    (hpick : rePick cp = some cert) (h : (reCost cp mcfg n).status = .ok) :
    (reCost cp mcfg n).value = cert.cost.val n := by
  simp only [reCost] at h ⊢
  obtain ⟨cert', hpick', hok, hval⟩ := reBound_ok_elim h
  rw [hpick] at hpick'
  have hcc : cert = cert' := Option.some.inj hpick'
  subst hcc
  rw [hval]
  exact bound_ok_val hok

theorem reStack_val {cp : CompiledPat} {cert : Cert} {mcfg n : Nat}
    (hpick : rePick cp = some cert) (h : (reStack cp mcfg n).status = .ok) :
    (reStack cp mcfg n).value = cert.stack.val n := by
  simp only [reStack] at h ⊢
  obtain ⟨cert', hpick', hok, hval⟩ := reBound_ok_elim h
  rw [hpick] at hpick'
  have hcc : cert = cert' := Option.some.inj hpick'
  subst hcc
  rw [hval]
  exact bound_ok_val hok

theorem reMem_val {cp : CompiledPat} {cert : Cert} {mcfg n : Nat}
    (hpick : rePick cp = some cert) (h : (reMem cp mcfg n).status = .ok) :
    (reMem cp mcfg n).value = cert.mem.val n := by
  simp only [reMem] at h ⊢
  obtain ⟨cert', hpick', hok, hval⟩ := reBound_ok_elim h
  rw [hpick] at hpick'
  have hcc : cert = cert' := Option.some.inj hpick'
  subst hcc
  rw [hval]
  exact bound_ok_val hok

/-- The scratch `ctx_match` hands the lockstep core is exactly the growth
schedule's final capacity for every one of its six arrays. This is where
creation and the run-side account meet: `ctx_create` takes its four numbers
off `pike_room`, and `pikeRun_inBudget_ctx` asks for nothing else. -/
theorem ctx_pike_reserved {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hpike : cp.re.pike = true) :
    Reserved cp.re
      { clistCap := ctx.listsCap, nlistCap := ctx.listsCap
        stkCap := ctx.stkCap, poolCap := ctx.poolCap
        rcCap := ctx.tablesCap, freeCap := ctx.tablesCap } := by
  obtain ⟨-, -, -, -, hcaps, -⟩ := ctx_created_caps hcreate
  obtain ⟨room, hroom, hl, hs, ht, hp⟩ := hcaps hpike
  rw [hl, hs, ht, hp]
  exact Reserved.ofRoom hroom

/-- S-11 on the lockstep path, with nothing left assumed about the run: a
context whose per-call cost sits at or above the analyzer's bound for the
subject never answers ResourceExceeded on a call it admits.

The memory component has no per-call role, which is DESIGN.md section 2.4's
rule: the call runs against the reservation, and `ctx_memcap_covers` is what
says the reservation is at or above the per-call memory bound. So the caller's
own two checks — the length the context admits, and a cost at or above
`re_cost` — are the whole of what it has to do.

What the core asks for on top is about the program rather than about the
call: the program's successors stay inside it, and the certificate the
accessor answered from is one the lockstep checker accepted. -/
theorem ctx_sufficient_pike {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost stack : Nat} {cert : Cert}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hpike : cp.re.pike = true)
    (hwf : ReWf cp.re)
    (hpick : rePick cp = some cert)
    (hcheck : pikeCheck cp.re cert = .crOk)
    (hbase : ∀ c, rePick cp = some c → 1 ≤ c.mem.base)
    (hadmit : s.size ≤ ctx.maxlen)
    (hstart : start ≤ s.size)
    (hcostcap : cost ≤ ctx.costcap)
    (hstackcap : stack ≤ ctx.stackcap)
    (hmemok : (reMem cp mcfg s.size).status = .ok)
    (hcostok : (reCost cp mcfg s.size).status = .ok)
    (hcostbd : (reCost cp mcfg s.size).value ≤ cost) :
    (ctxMatch ctx s start mo cost stack).outcome ≠ .resourceExceeded := by
  obtain ⟨hcp, hmax, -, -, -, -⟩ := ctx_created_caps hcreate
  have hcovers : (reMem cp mcfg s.size).value ≤ ctx.memcap :=
    ctxMatch_memcap_covers hcreate hbase hadmit hmax hmemok
  rw [reMem_val hpick hmemok] at hcovers
  rw [reCost_val hpick hcostok] at hcostbd
  have hres := ctx_pike_reserved hcreate hpike
  unfold ctxMatch
  rw [if_neg (by simpa using Nat.not_lt.mpr hadmit),
      if_neg (by simpa using Nat.not_lt.mpr hcostcap),
      if_neg (by simpa using Nat.not_lt.mpr hstackcap)]
  subst hcp
  simpa [hpike] using pikeRun_inBudget_ctx (lim := ⟨cost, stack, ctx.memcap⟩) hwf
    hres.rooms hstart hcheck hcostbd hcovers

/-- A memory answer is under the allocation ceiling, because that is the roof
the accessor holds it to. This is what a context call reads its own limit
against: the reservation it runs on is a number the caller was given, and the
growth schedule's maxima are out of its reach. -/
theorem reMem_le_ceiling {cp : CompiledPat} {mcfg n : Nat}
    (h : (reMem cp mcfg n).status = .ok) : (reMem cp mcfg n).value ≤ ceiling := by
  simp only [reMem] at h ⊢
  obtain ⟨cert, -, hok, hval⟩ := reBound_ok_elim h
  rw [hval]
  by_cases hc : (polyValue cert.mem n).ok = true ∧
      (polyValue cert.mem n).value > ceiling
  · have hex : certBound cert .mem n = Bound.exceeds := by
      simp only [certBound]
      rw [if_pos hc]
    rw [hex] at hok
    simp [Bound.exceeds] at hok
  · have heq : certBound cert .mem n = polyValue cert.mem n := by
      simp only [certBound]
      rw [if_neg hc]
    rw [heq] at hok ⊢
    simp only [not_and, Nat.not_lt] at hc
    exact hc hok

/-- What a created context reserved for the backtracking core, as the growth
schedule's own answer for the claims the certificate makes at the declared
maximum. -/
theorem ctx_bt_reserved {cp : CompiledPat} {mcfg maxlen : Nat} {lim : Limits}
    {ctx : Ctx} {cert : Cert}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hplain : cp.re.pike = false) (hpick : rePick cp = some cert) :
    capacityOf (cert.stack.val maxlen) = ctx.btCap ∧
      capacityOf (cert.trail.val maxlen) = ctx.trailCap := by
  obtain ⟨-, -, -, -, -, hcaps⟩ := ctx_created_caps hcreate
  obtain ⟨cert', hpick', hdeep, hlong, hbt, htr⟩ := hcaps hplain
  rw [hpick] at hpick'
  have hcc : cert = cert' := Option.some.inj hpick'
  subst hcc
  have hdv : (polyValue cert.stack maxlen).value = cert.stack.val maxlen :=
    polyValue_ok (by rw [← hdeep])
  have hlv : (polyValue cert.trail maxlen).value = cert.trail.val maxlen :=
    polyValue_ok (by rw [← hlong])
  rw [hdv] at hbt
  rw [hlv] at htr
  exact ⟨capacityOf_growthCap hbt, capacityOf_growthCap htr⟩

/-- S-11 on the backtracking path, with nothing left assumed about the run and
no class left to stay inside: `btRun_inBudget_ctx_counted` covers a counted
repetition too, so what the program has to satisfy is `ReRules`, the rules the
engine keeps by construction and the checker does not ask about.

The reservation is doing the work the plain call does with its cost budget.
Creation sized both arrays at the declared maximum, so a call the context
admits arrives holding more than its own claims ask for; the growth allowance
in the section 5 cost line is therefore already paid for, and what the caller
has to supply is the per-call cost and stack at this subject length and
nothing more.

`ReRules` cannot be read off the compiler here the way `compile_reRules` reads
it for a whole pattern, because a `CompiledPat` is whatever it was handed and
nothing ties its program to `Ref.compile`. So the bundle travels, and closing
that gap means an invariant on `CompiledPat` rather than another walk. -/
theorem ctx_sufficient_bt {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost stack : Nat} {cert : Cert}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hplain : cp.re.pike = false)
    (hpick : rePick cp = some cert)
    (hcheck : certCheck cp.re .backtrack cert = .crOk)
    (hrules : ReRules cp.re)
    (hbase : ∀ c, rePick cp = some c → 1 ≤ c.mem.base)
    (hadmit : s.size ≤ ctx.maxlen)
    (hcostcap : cost ≤ ctx.costcap)
    (hstackcap : stack ≤ ctx.stackcap)
    (hmemok : (reMem cp mcfg s.size).status = .ok)
    (hcostok : (reCost cp mcfg s.size).status = .ok)
    (hcostbd : (reCost cp mcfg s.size).value ≤ cost)
    (hstackok : (reStack cp mcfg s.size).status = .ok)
    (hstackbd : (reStack cp mcfg s.size).value ≤ stack) :
    (ctxMatch ctx s start mo cost stack).outcome ≠ .resourceExceeded := by
  obtain ⟨hcp, hmax, -, -, -, -⟩ := ctx_created_caps hcreate
  obtain ⟨hres, hcap, hstatus⟩ := ctx_resident_eq_reservation hcreate
  obtain ⟨hbtcap, htrcap⟩ := ctx_bt_reserved hcreate hplain hpick
  obtain ⟨hsb, htb⟩ := certCheck_bt_bases hcheck
  have hlen : s.size ≤ maxlen := by rw [← hmax]; exact hadmit
  have hmemval : ctx.memcap = cert.mem.val maxlen := by
    rw [hcap, reMem_val hpick hstatus]
  have hceil : ctx.memcap ≤ ceiling := by
    rw [hcap]
    exact reMem_le_ceiling hstatus
  have hroom : btSetup cp.re + 2 * capScratch ctx.btCap ctx.trailCap ≤
      ctx.memcap := by
    obtain ⟨-, hdomm⟩ := certCheck_bt_dom hcheck maxlen
    rw [hmemval, ← hbtcap, ← htrcap, ← btScratch_eq]
    omega
  have hgrow : capacityOf (cert.stack.val s.size) ≤ ctx.btCap := by
    rw [← hbtcap]
    exact capacityOf_mono (val_mono_length hsb hlen)
  have htgrow : capacityOf (cert.trail.val s.size) ≤ ctx.trailCap := by
    rw [← htrcap]
    exact capacityOf_mono (val_mono_length htb hlen)
  have hcovers : (reMem cp mcfg s.size).value ≤ ctx.memcap :=
    ctxMatch_memcap_covers hcreate hbase hadmit hmax hmemok
  rw [reCost_val hpick hcostok] at hcostbd
  rw [reStack_val hpick hstackok] at hstackbd
  unfold ctxMatch
  rw [if_neg (by simpa using Nat.not_lt.mpr hadmit),
      if_neg (by simpa using Nat.not_lt.mpr hcostcap),
      if_neg (by simpa using Nat.not_lt.mpr hstackcap)]
  subst hcp
  simpa [hplain] using btRun_inBudget_ctx_counted (lim := ⟨cost, stack, ctx.memcap⟩)
    hcheck hrules hceil hgrow htgrow hroom hcostbd hstackbd

/-- S-11, `ctx_sufficient`: conditional on creation having succeeded, a
context whose per-call limits sit at or above the analyzer's bounds never
answers ResourceExceeded on a call it admits — with nothing assumed about how
the run ends on either path.

What is left to ask for is what a caller can check and what the two cores need
of the program. The caller's half is the three admission conditions, a start
offset inside the subject, and the accessor readings at its own subject
length; the program's half is `ReWf`, the certificate the accessor answered
from, and — on the backtracking path only, which is why it is asked for under
the flag — `ReRules`, the rules that path reads the compiled form through.
There is no class condition left on either path. -/
theorem ctx_sufficient {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost stack : Nat} {cert : Cert}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hwf : ReWf cp.re)
    (hpick : rePick cp = some cert)
    (hcheckP : cp.re.pike = true → pikeCheck cp.re cert = .crOk)
    (hcheckB : cp.re.pike = false → certCheck cp.re .backtrack cert = .crOk)
    (hrules : cp.re.pike = false → ReRules cp.re)
    (hbase : ∀ c, rePick cp = some c → 1 ≤ c.mem.base)
    (hadmit : s.size ≤ ctx.maxlen)
    (hstart : start ≤ s.size)
    (hcostcap : cost ≤ ctx.costcap)
    (hstackcap : stack ≤ ctx.stackcap)
    (hmemok : (reMem cp mcfg s.size).status = .ok)
    (hcostok : (reCost cp mcfg s.size).status = .ok)
    (hcostbd : (reCost cp mcfg s.size).value ≤ cost)
    (hstackok : (reStack cp mcfg s.size).status = .ok)
    (hstackbd : (reStack cp mcfg s.size).value ≤ stack) :
    (ctxMatch ctx s start mo cost stack).outcome ≠ .resourceExceeded := by
  by_cases hpike : cp.re.pike = true
  · exact ctx_sufficient_pike hcreate hpike hwf hpick (hcheckP hpike) hbase hadmit
      hstart hcostcap hstackcap hmemok hcostok hcostbd
  · have hplain : cp.re.pike = false := by simpa using hpike
    exact ctx_sufficient_bt hcreate hplain hpick (hcheckB hplain) (hrules hplain)
      hbase hadmit hcostcap hstackcap hmemok hcostok hcostbd hstackok hstackbd

/-- R-9's no-allocation clause for a context call on the lockstep path. What
the call reports resident is the reservation creation took, whatever the call
did, and underneath that the core really did allocate nothing: every array it
was handed already held the growth schedule's final capacity, so no growth
step was ever reached. -/
theorem ctxMatch_no_growth_pike {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost stack : Nat}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hpike : cp.re.pike = true) (hwf : ReWf cp.re)
    (hadmit : s.size ≤ ctx.maxlen)
    (hcostcap : cost ≤ ctx.costcap) (hstackcap : stack ≤ ctx.stackcap) :
    (ctxMatch ctx s start mo cost stack).usage.mem = ctx.resident ∧
      (pikeRun cp.re s start mo ⟨cost, stack, ctx.memcap⟩
          { clistCap := ctx.listsCap, nlistCap := ctx.listsCap
            stkCap := ctx.stkCap, poolCap := ctx.poolCap
            rcCap := ctx.tablesCap, freeCap := ctx.tablesCap }).usage.mem ≤
        pikeSetup cp.re := by
  obtain ⟨hres, -, -⟩ := ctx_resident_eq_reservation hcreate
  refine ⟨?_, pikeRun_no_growth hwf (ctx_pike_reserved hcreate hpike)⟩
  unfold ctxMatch
  rw [if_neg (by simpa using Nat.not_lt.mpr hadmit),
      if_neg (by simpa using Nat.not_lt.mpr hcostcap),
      if_neg (by simpa using Nat.not_lt.mpr hstackcap)]
  simp [hres]

/-- And on the backtracking path, with the same reach: creation sizes each of
the two arrays through the growth schedule at the declared maximum, and a
claim never falls as the subject shortens, so a call the context admits
arrives with more room than its own claim asks for and never reaches a growth
step either. A counted repetition changes none of that, only what the claim
had to be proved from. -/
theorem ctxMatch_no_growth_bt {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx} {s : ByteArray} {start : Nat} {mo : MOpts}
    {cost stack : Nat} {cert : Cert}
    (hcreate : ctxCreate cp mcfg maxlen lim = (.ok, some ctx))
    (hplain : cp.re.pike = false)
    (hpick : rePick cp = some cert)
    (hcert : certCheck cp.re .backtrack cert = .crOk)
    (hrules : ReRules cp.re)
    (hadmit : s.size ≤ ctx.maxlen)
    (hcostcap : cost ≤ ctx.costcap) (hstackcap : stack ≤ ctx.stackcap) :
    (ctxMatch ctx s start mo cost stack).usage.mem = ctx.resident ∧
      (btRun cp.re s start mo ⟨cost, stack, ctx.memcap⟩ ctx.btCap
        ctx.trailCap).usage.mem ≤ btSetup cp.re := by
  obtain ⟨hres, -, -⟩ := ctx_resident_eq_reservation hcreate
  obtain ⟨-, hmax, -, -, -, -⟩ := ctx_created_caps hcreate
  obtain ⟨hbtcap, htrcap⟩ := ctx_bt_reserved hcreate hplain hpick
  obtain ⟨hsb, htb⟩ := certCheck_bt_bases hcert
  have hlen : s.size ≤ maxlen := by rw [← hmax]; exact hadmit
  refine ⟨?_, btRun_no_growth_ctx_counted hcert hrules ?_ ?_⟩
  · unfold ctxMatch
    rw [if_neg (by simpa using Nat.not_lt.mpr hadmit),
        if_neg (by simpa using Nat.not_lt.mpr hcostcap),
        if_neg (by simpa using Nat.not_lt.mpr hstackcap)]
    simp [hres]
  · rw [← hbtcap]
    exact capacityOf_mono (val_mono_length hsb hlen)
  · rw [← htrcap]
    exact capacityOf_mono (val_mono_length htb hlen)

end Pcrevera.Ref
