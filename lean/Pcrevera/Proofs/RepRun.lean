import Pcrevera.Proofs.RepOnce

/-!
# The backtracking resource bounds, counted repetitions included

`BtBounds.lean` states R-6 to R-9 and S-10 over a pricing of the program's
control flow, and the versions of them that read that pricing off a
certificate carry `hopt`: every repeat region is an optional item. That
hypothesis is not about the run, it is about the pricing — `flowCost` indexes
a price by the program point alone, and a counted repetition's price has to
name the counter.

`RepFlow.lean` and `RepPriced.lean` between them build the pricing that does,
and prove of it the two things the accounts ask: it satisfies `RegFlow`, and
at the entry point it is inside the certificate's three whole-call numbers.
What is left is to hand those to the accounts, and that is this file: R-6,
R-7, R-8, S-10 and R-9's no-allocation clause, each concluding what its
forward-class sibling concludes and none of them restricted to optional
items.

What comes in where `hopt` went out is not a restriction on the pattern but
`ReRules`, the rules THEOREMS.md records the checker as not having. They
travel in the statements because an arbitrary `Re` is whatever it is, and not
because they are hard to come by: `compile_repRegs` below and the rest of
`RepCompile.lean` prove every one of the six for what `Ref.compile` emits.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## What a compiled program satisfies and a certificate does not promise -/

/-- The six rules the backtracking bounds read a program through, and that no
clause of `certCheck` asks about. THEOREMS.md keeps the same list, and this is
where a reader meets it: every one of them holds of what `Ref.compile` emits,
and not one of them follows from an accepted certificate, so they travel in
the statements rather than in the proofs.

`accept` and `ends` are one idea in two places, that a run never falls off the
end of its own code. The program's last instruction is an `Accept`, so a
fall-through stops there; and no alternation and no repeat region ends the
program, so a branch's closing jump and a skipped body do not carry control
past it either. The two layers part company on a program without them: TIR's
checked indexing traps, while the Lean reference reads a default instruction.

`saves` keeps a capture write off a counter register. A `Save` naming a
counter would move a count with no `RepZero` or `RepNext` to account for it,
which breaks the pass count of BOUNDS.md section 4.4 and the measure its proof
descends on. The compiler emits a `Save` only for a numbered group, so the
slot it names is below `novec`.

`counts` and `regs` are what make a counter a counter. The two declared bounds
have to be values a counter register can hold, because the head's own maximum
test is read against them and a wrap would price a repetition for more passes
than the value before it. And the register file has to have room for two slots
per repetition, because a `RepEnter` with nowhere to write would leave the
empty-match rule with nothing to fire on, and an unbounded repetition would
count without ever spending a byte.

`regions` is the one rule that is about the reference rather than about the
engine. There a region index is a `u32` and NONE is `0xFFFFFFFF`, so a real
region and the sentinel cannot be confused; here indices are `Nat`, and a
program with `0xFFFFFFFF + 1` regions would have one that hangs off no
parent's child list and is invisible to every walk the checker runs. -/
structure ReRules (re : Re) : Prop where
  accept : (re.code[re.code.size - 1]!).op = .accept
  ends : ∀ j, j < re.regions.size →
    ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
    (re.regions[j]!).hi < re.code.size
  saves : ∀ q, q < re.code.size → (re.code[q]!).op = .save →
    (re.code[q]!).arg < re.novec
  counts : ∀ a : Nat, a < re.reps.size →
    (re.reps[a]!).lo ≤ none32 ∧ (re.reps[a]!).hi ≤ none32
  regs : re.novec + re.reps.size * 2 ≤ re.nregs
  regions : re.regions.size ≤ none32

/-! ## The three accounts, read off a certificate -/

/-- Section 4 for a tree that may hold counted repetitions: one entry into
the program visits at most the root region's claimed `work`, records at most
its `trail` and never pushes past its `stack`. -/
theorem attemptsWithin_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start bcap tcap carried : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling) (hsafe : Unclamped bcap tcap carried)
    (hbcap : capacityOf (cert.stack.val s.size) ≤ bcap)
    (htcap : capacityOf (cert.trail.val s.size) ≤ tcap) :
    AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) bcap tcap carried
      ((cert.prices[0]!).work.val s.size) := by
  obtain ⟨hroot, hpass⟩ :=
    rep_cert_priced_once hcert hrules.ends hrules.accept hrules.regions s.size
  exact attemptsWithin_of_regflow
    (regFlow_of_cert (n := s.size) (ways := repWays re cert.prices s.size)
      (chargeW := repChargeW re cert.prices s.size)
      (chargeR := repChargeR re cert.prices s.size)
      (chargeT := repChargeT re cert.prices s.size) hcert hrules.ends
      hrules.accept hrules.saves hrules.counts
      (fun _ _ => by simp only [repChargeW]; omega)
      (fun _ _ => by simp only [repChargeT]; omega)
      (fun q _ hq => (hpass q hq).1) (fun q _ hq => (hpass q hq).2.1)
      (fun q _ hq => (hpass q hq).2.2))
    (fun _ _ _ hok => hok.2.1) hlim hsafe hbcap htcap
    (fun pos hpos => ⟨code_size_pos hrules.accept, hpos,
      by rw [Array.size_replicate]; exact hrules.regs⟩)
    (fun pos => (hroot _ pos).1) (fun pos => (hroot _ pos).2.1)
    (fun pos => (hroot _ pos).2.2)

/-- R-6 for a pattern that may count its repetitions. -/
theorem btRun_cost_le_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size :=
  btRun_cost_le hcert
    (attemptsWithin_counted hcert hrules hlim
      (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _))

/-- R-7 on the same programs. A repetition's head forks once per pass, so the
backtrack stack is where the pass count is felt. -/
theorem btRun_stack_le_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  btRun_stack_le
    (attemptsWithin_counted hcert hrules hlim
      (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _))

/-- And R-8. Each of the three repetition opcodes that moves a register leaves
an undo entry behind it, so the trail carries the pass count too. -/
theorem btRun_mem_le_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size :=
  btRun_mem_le hcert
    (attemptsWithin_counted hcert hrules hlim
      (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _))

/-! ## The budget account -/

/-- The companion of `attemptsWithin_counted`: no attempt of the run refuses
for want of a resource. -/
theorem attemptsInBudget_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start bcap tcap carried : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling)
    (hbcap : capacityOf (cert.stack.val s.size) ≤ bcap)
    (htcap : capacityOf (cert.trail.val s.size) ≤ tcap)
    (hmemlim : btSetup re + 2 * capScratch bcap tcap ≤ lim.mem)
    (hstacklim : cert.stack.val s.size ≤ lim.stack) :
    AttemptsInBudget re s mo lim start (btSetup re) (cert.trail.val s.size)
      bcap tcap carried ((cert.prices[0]!).work.val s.size) := by
  obtain ⟨hroot, hpass⟩ :=
    rep_cert_priced_once hcert hrules.ends hrules.accept hrules.regions s.size
  exact attemptsInBudget_of_regflow (stack := cert.stack.val s.size)
    (regFlow_of_cert (n := s.size) (ways := repWays re cert.prices s.size)
      (chargeW := repChargeW re cert.prices s.size)
      (chargeR := repChargeR re cert.prices s.size)
      (chargeT := repChargeT re cert.prices s.size) hcert hrules.ends
      hrules.accept hrules.saves hrules.counts
      (fun _ _ => by simp only [repChargeW]; omega)
      (fun _ _ => by simp only [repChargeT]; omega)
      (fun q _ hq => (hpass q hq).1) (fun q _ hq => (hpass q hq).2.1)
      (fun q _ hq => (hpass q hq).2.2))
    (fun _ _ _ hok => hok.2.1) hlim hbcap htcap hmemlim hstacklim
    (fun pos hpos => ⟨code_size_pos hrules.accept, hpos,
      by rw [Array.size_replicate]; exact hrules.regs⟩)
    (fun pos => (hroot _ pos).1) (fun pos => (hroot _ pos).2.1)
    (fun pos => (hroot _ pos).2.2)

/-- S-10 for a pattern that may count its repetitions: a caller whose three
limits sit at or above what the certificate names never sees
ResourceExceeded. -/
theorem btRun_inBudget_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling)
    (hcost : cert.cost.val s.size ≤ lim.cost)
    (hmem : cert.mem.val s.size ≤ lim.mem)
    (hstack : cert.stack.val s.size ≤ lim.stack) :
    (btRun re s start mo lim 0 0).outcome ≠ .resourceExceeded := by
  obtain ⟨hdomc, hdomm⟩ := certCheck_bt_dom hcert s.size
  obtain ⟨hsetupc, hsetupm⟩ := btRun_setup_ok hcert hcost hmem
  have hattw := attemptsWithin_counted (s := s) (mo := mo) (lim := lim)
    (start := start) (carried := 0) hcert hrules hlim
    (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  have hmemlim : btSetup re + 2 * capScratch (capacityOf (cert.stack.val s.size))
      (capacityOf (cert.trail.val s.size)) ≤ lim.mem := by
    rw [← btScratch_eq]
    omega
  have hatt := attemptsInBudget_counted (s := s) (mo := mo) (lim := lim)
    (start := start) (carried := 0) hcert hrules hlim
    (Nat.le_refl _) (Nat.le_refl _) hmemlim hstack
  have hsteps : (s.size + 1 - start) * (btReset re + ((cert.prices[0]!).work.val s.size
      + regSize * cert.trail.val s.size)) ≤
      (s.size + 1) * (btReset re + ((cert.prices[0]!).work.val s.size
        + regSize * cert.trail.val s.size)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [btRun_caps]
  split
  · simp
  rename_i hstartle
  split
  · rename_i hguard
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hguard
    omega
  have hloopin := btLoop_budget (deliver := btDeliver re) hatt hattw
    (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], 0, #[], 0,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ (by omega) (by omega)
    (Nat.zero_le _) (Nat.zero_le _) (by simp [BtSt.reserved])
    (by simp only [BtSt.reserved, ← btScratch_eq]; omega)
  have hloopw := btLoop_within hattw (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], 0, #[], 0,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ (by omega) (Nat.zero_le _)
    (Nat.zero_le _) (by simp [BtSt.reserved])
  split
  · rename_i st' hout
    rw [hout] at hloopw
    simp only [RunEnd.state] at hloopw
    have hr2 := reserved_le hloopw.btRoom hloopw.trailRoom
    have hch := hloopw.charged
    simp only [BtSt.reserved, ← btScratch_eq] at hch hr2
    split
    · rename_i hbad
      exfalso
      omega
    · simp
  · simp
  · rename_i st' hout
    rw [hout] at hloopin
    exact absurd hloopin (by simp [RunEnd.inBudget])

/-- S-10 at the capacities a preallocated context hands over, for a pattern
that may count its repetitions.

Nothing about the counted route changes what a context call needs beyond the
plain one, and the three differences are the ones the forward statement
already carries. The claims and the capacities are no longer the same numbers,
since creation reserves at the declared maximum while a call runs at its own
length, so `hbtcap` and `htrcap` only ask that the arrays cover the schedule's
answer for this call. The meter was never told about the scratch, so what it
reads is short by exactly what the call arrived holding, which is what the
account is instantiated at. And the growth allowance on the cost line is
already paid for, which is why the cost asked of the caller is the one at this
subject length.

`hroom` is the memory line at the reservation, and it is what rules the
declared array maxima out. -/
theorem btRun_inBudget_ctx_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start btCap trailCap : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hlim : lim.mem ≤ ceiling)
    (hbtcap : capacityOf (cert.stack.val s.size) ≤ btCap)
    (htrcap : capacityOf (cert.trail.val s.size) ≤ trailCap)
    (hroom : btSetup re + 2 * capScratch btCap trailCap ≤ lim.mem)
    (hcost : cert.cost.val s.size ≤ lim.cost)
    (hstack : cert.stack.val s.size ≤ lim.stack) :
    (btRun re s start mo lim btCap trailCap).outcome ≠ .resourceExceeded := by
  obtain ⟨hdomc, hdomm⟩ := certCheck_bt_dom hcert s.size
  have hsafe : Unclamped btCap trailCap (capScratch btCap trailCap) :=
    unclamped_of_memlim (setup := btSetup re) hroom hlim
  have hattw := attemptsWithin_counted (s := s) (mo := mo) (lim := lim)
    (start := start) (carried := capScratch btCap trailCap) hcert hrules hlim
    hsafe hbtcap htrcap
  have hatt := attemptsInBudget_counted (s := s) (mo := mo) (lim := lim)
    (start := start) (carried := capScratch btCap trailCap) hcert hrules hlim
    hbtcap htrcap hroom hstack
  have hsteps : (s.size + 1 - start) * (btReset re + ((cert.prices[0]!).work.val s.size
      + regSize * cert.trail.val s.size)) ≤
      (s.size + 1) * (btReset re + ((cert.prices[0]!).work.val s.size
        + regSize * cert.trail.val s.size)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [btRun_caps]
  split
  · simp
  rename_i hstartle
  split
  · rename_i hguard
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hguard
    simp only [capScratch] at hroom
    omega
  have hstart0 : (⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ : BtSt).m.mem
        + capScratch btCap trailCap
      = btSetup re + (⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
        ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ : BtSt).reserved := by
    simp only [BtSt.reserved, capScratch]
  have hloopin := btLoop_budget (deliver := btDeliver re) hatt hattw
    (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ (by omega) (by omega)
    (Nat.le_refl _) (Nat.le_refl _) hstart0
    (by simp only [BtSt.reserved, capScratch] at *; omega)
  have hloopw := btLoop_within hattw (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ (by omega) (Nat.le_refl _)
    (Nat.le_refl _) hstart0
  split
  · rename_i st' hout
    rw [hout] at hloopw
    simp only [RunEnd.state] at hloopw
    have hr2 := reserved_le hloopw.btRoom hloopw.trailRoom
    have hch := hloopw.charged
    simp only [BtSt.reserved, capScratch] at hch hr2
    split
    · rename_i hbad
      exfalso
      omega
    · simp
  · simp
  · rename_i st' hout
    rw [hout] at hloopin
    exact absurd hloopin (by simp [RunEnd.inBudget])

/-! ## The steady account -/

/-- R-9's second half for a pattern that may count its repetitions: a call
whose two arrays already hold the claims never grows either, so the resident
bytes it reports are the register file and the ovector it was handed.

Nothing here asks anything of the caller's limits. A run that never grows
never reaches a growth test, and the two tests that remain can still refuse
without allocating. -/
theorem btRun_no_growth_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start btCap trailCap : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hbtcap : cert.stack.val s.size ≤ btCap)
    (htrcap : cert.trail.val s.size ≤ trailCap) :
    (btRun re s start mo lim btCap trailCap).usage.mem ≤ btSetup re := by
  obtain ⟨hroot, hpass⟩ :=
    rep_cert_priced_once hcert hrules.ends hrules.accept hrules.regions s.size
  have hatt := attemptsSteady_of_regflow (s := s) (mo := mo) (lim := lim)
    (start := start)
    (regFlow_of_cert (n := s.size) (ways := repWays re cert.prices s.size)
      (chargeW := repChargeW re cert.prices s.size)
      (chargeR := repChargeR re cert.prices s.size)
      (chargeT := repChargeT re cert.prices s.size) hcert hrules.ends
      hrules.accept hrules.saves hrules.counts
      (fun _ _ => by simp only [repChargeW]; omega)
      (fun _ _ => by simp only [repChargeT]; omega)
      (fun q _ hq => (hpass q hq).1) (fun q _ hq => (hpass q hq).2.1)
      (fun q _ hq => (hpass q hq).2.2))
    (fun _ _ _ hok => hok.2.1)
    (fun pos hpos => ⟨code_size_pos hrules.accept, hpos,
      by rw [Array.size_replicate]; exact hrules.regs⟩)
    (fun pos => Nat.le_trans (hroot _ pos).2.1 htrcap)
    (fun pos => Nat.le_trans (hroot _ pos).2.2 hbtcap)
  rw [btRun_caps]
  split
  · exact Nat.zero_le _
  rename_i hstartle
  split
  · exact Nat.zero_le _
  have hloop := btLoop_steady hatt (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ (by omega) (Nat.le_refl _)
    (Nat.le_refl _)
  have hpeak := hloop.resident
  dsimp only at hpeak
  split
  · rename_i st' hout
    rw [hout] at hpeak
    simp only [RunEnd.state] at hpeak
    split <;> simp only [BtSt.usage] <;> omega
  · rename_i st' hout
    rw [hout] at hpeak
    simp only [RunEnd.state] at hpeak
    simp only [BtSt.usage]
    omega
  · rename_i st' hout
    rw [hout] at hpeak
    simp only [RunEnd.state] at hpeak
    simp only [BtSt.usage]
    omega

/-- The same, at the capacities a preallocated context hands over. Creation
sizes each array through the growth schedule rather than at the claim itself,
and the schedule never sizes one below what it was asked to hold, so a call
through a context is a call that has nothing left to buy. -/
theorem btRun_no_growth_ctx_counted {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start btCap trailCap : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hrules : ReRules re)
    (hbtcap : capacityOf (cert.stack.val s.size) ≤ btCap)
    (htrcap : capacityOf (cert.trail.val s.size) ≤ trailCap) :
    (btRun re s start mo lim btCap trailCap).usage.mem ≤ btSetup re :=
  btRun_no_growth_counted hcert hrules
    (Nat.le_trans (le_capacityOf _) hbtcap)
    (Nat.le_trans (le_capacityOf _) htrcap)

/-! ## The bundle for a compiled pattern -/

/-- `ReRules.regs` is a fact about the register count alone, and `Ref.compile`
settles it: the file it asks for is the ovector window plus two slots per
repetition, exactly, which is the whole of what the counted pricing reads.

The equality is worth stating rather than the bound, because it is also what
says the file is no larger than it needs to be. -/
theorem compile_nregs (p : Pat) :
    (compile p).nregs = (compile p).novec + (compile p).reps.size * 2 := by
  show ((compile p).ncap + 1) * 2 + (compile p).reps.size * 2 = _
  show ((compile p).ncap + 1) * 2 + (compile p).reps.size * 2 =
    2 * ((compile p).ncap + 1) + (compile p).reps.size * 2
  omega

/-- And in the direction the theorems above ask for it. -/
theorem compile_repRegs (p : Pat) :
    (compile p).novec + (compile p).reps.size * 2 ≤ (compile p).nregs :=
  Nat.le_of_eq (compile_nregs p).symm

end Pcrevera.Ref
