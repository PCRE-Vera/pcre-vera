import Pcrevera.Proofs.PolySound
import Pcrevera.Proofs.PikeTermination

/-!
# What a lockstep run may spend (R-6 through R-8, the Pike half)

BOUNDS.md section 9 prices a Pike call in a handful of counts read straight
off the program, and `pikePrice` computes exactly that price with saturating
counter arithmetic. This file takes the counter arithmetic back off: on the
success path every `satAdd` and `satMul` was exact, so the certificate the
analyzer hands out is one explicit polynomial, and `Poly.val` reads it as the
number BOUNDS.md writes down.

Ten things live here.

The stack line is the easy one and it is R-7 for this configuration: no
backtrack entry exists on the lockstep path, the field is only ever written
zero, and every claimed stack bound is therefore met with room to spare.

The closed form comes next. `pikeRoom` and `pikePrice` are read the way
`CtxReserve.lean` reads `ctxCreate` — flag chain first, then the values it
certifies — which turns the certificate into `setup + B + 3R` plus `position`
per starting position for cost, and `setup + B + 2R` for memory, with `R`
itself spelled out as the four capacities times their entry sizes.

The transfer follows. `pikeCheck` recomputes that same price and asks for
domination, so an accepted certificate is worth at least the closed form at
every subject length, whatever else it claims.

Last is the enforcement invariant: a run's reported cost and memory never
pass the limits it was called under, because every charge on this path is
compared against the remaining budget before it is made and a refused helper
keeps only what it had already charged.

Fifth is the dedup that the per-position count rests on. A closure build
marks each instruction at most once and parks at most one thread per mark, so
a thread list never holds more than `C` entries; that is a loop invariant,
and `pikeRun` enters the loop inside it. The argument needs the program's
successors to stay inside the program, which is what `ReWf` says and what the
matcher cannot check for itself.

Sixth is the block pool's ownership. Every block the run has allocated is
either on the free list or held by one of the handles the caller is
carrying, and its refcount says exactly how many carry it. `pike_take`
lengthens the refcount table only when the free list has nothing on it, and
at that moment the ownership says every block is one of those handles —
which is how `4*C + 2` is read off the lists rather than off the number of
allocations. The reading is carried through a whole scan: a closure build's
own handles are its worklist and the list it is parking into, a list step's
are the snapshot it has still to consume and the match it is carrying, and
one measure — the worklist, the parked list, and twice the marks not yet
made — never rises and bounds them all. `pikeRun_pool_le` is the payoff.

Seventh is the growth schedule, weighed. `charge_grow` clamps at a declared
maximum, and the section 9 accounting only reads as `3R` and `2R` if the
schedule is left to grow; the clamp is out of reach here because every array
has an entry bound read off the program and the four maxima of `Pike.lean`
sit above twice the largest such bound. That is what `ReWf.coded` and
`ReWf.slots` are in the predicate for.

Eighth is the per-position account, which is what joins the closed form to
the run. It is kept against the visited set: `closureLeft` weighs what a set
still admits — a unit per unmarked pc, and a block more at a `Save`, that
being the one instruction whose arm can copy — and marking a pc releases
exactly what the arm that follows then spends. `Spent` is that reading, and
everything below it is stated over the state either arm of a helper hands
back, since a refusal keeps its partial charges and does not end a build the
way it ends the loop. A build spends its own marks (`pikeAdd_go_spent`), a
list step a unit per thread and a block for the accept, a seed a block, a
position one clear on top of those — which is `2*C + (S + 2)*B + W`, exactly
section 9's price — and `pikeLoop_spent` telescopes them across the scan.

The account carries a full visited set on the left, and that is not slack:
the seed at the first position draws on the set `pike_run` created rather
than on a clear, so the run makes one set's worth of marks more than it has
clears. What pays for it is the last position, where the step opens no
closure at all — a consuming thread there fails the `pos < n` test and lets
its handle go — so the clear charged there is never drawn on.
`pikeRun_cost_le` and `pikeRun_mem_le` are the payoff, and R-6 and R-8 follow
against a computed price, against a checked certificate, and at the accessor.

Ninth is S-10's Pike half. It wants the same account read over the
charges a run *attempts* rather than the ones it completes: a refusal is a
pre-charge test failing, so ruling one out under a sufficient budget means
covering the charge that was refused as well as the ones that were made.
`Blown` is that reading — some state the account already covers has passed a
limit, which against a certificate the limits dominate is a contradiction —
and `Tried` carries it beside `Spent` up the same four inductions, all the way
to `pikeRun_inBudget_ctx`, which asks nothing of the scratch it was handed
beyond every capacity being inside the schedule's own answer for it. The plain
call is the instance of that at empty scratch.

Every charging helper is read that way, `chargeGrow_refused` being the one
with anything in it: neither of a growth step's two tests can be blamed on the
clamp, so what was refused is the capacity the schedule means to take, weighed
by the same three inequalities a step that ran satisfies. Two premises come
with the threading, both about a loop that answers `error` for a reason the
budget has nothing to say about: the closure build carries the termination
measure of `PikeTermination.lean` against its own fuel, and the position loop
a step count that covers the scan. And one thing is special about the last
position — the step there opens no closure, so what a refusal was asking for
is pure charge and the visited set cleared there is never drawn on. That is
`BlownFlat` and `stepThreads_last`, and it is what keeps the leftover of the
last clear available for the seed at the very first position.

Tenth, and last, is R-9's no-allocation clause, which reads the same account
backwards. `Charged` says a stretch never reserves more than the schedule
allows, never gives a reservation back, and moves its resident reading only
with that reservation. A call that arrives at the schedule's ceiling is
therefore pinned to it, and being pinned is what leaves the meter alone:
`pikeRun_no_growth` is the lockstep twin of `btRun_no_growth_forward`, and
like it, it mentions no limit at all.

`ReWf` itself is a hypothesis throughout: it is a fact about compiler output,
and no proof that `Ref.compile` supplies it is in this file.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## The stack a lockstep run never touches -/

/-- R-7 for `CfgPike`: the reported stack usage is zero, on every path. The
backtracking stack does not exist here — `PikeSt` has no field for it — so
`pikeRun` writes the constant and the stack limit has nothing to refuse. -/
theorem pikeRun_stack_zero (re : Re) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (init : PikeSt) :
    (pikeRun re s start mo lim init).usage.stack = 0 := by
  simp only [pikeRun]
  repeat' split
  all_goals rfl

/-- And so every stack claim a certificate makes is met, whatever the
certificate says. -/
theorem pikeRun_stack_le (re : Re) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (init : PikeSt) (cert : Cert) (v : Nat)
    (_h : certBound cert .stack s.size = ⟨true, v⟩) :
    (pikeRun re s start mo lim init).usage.stack ≤ v := by
  rw [pikeRun_stack_zero]
  exact Nat.zero_le v

/-! ## The counts of BOUNDS.md section 9 -/

/-- The growth schedule's final capacity for that many entries, with the
counter arithmetic taken out: nothing for none, else what a doubling run
ends up holding. -/
def capFor (entries : Nat) : Nat :=
  if entries = 0 then 0 else growMin + growFactor * entries

/-- `B`: the IR bytes of one capture block, which is also the ovector's. -/
def pikeBlock (re : Re) : Nat := re.novec * regSize

/-- `W`: the bytes of one visited set. -/
def pikeWords (re : Re) : Nat := re.code.size / 8 + 1

/-- `S`: the Save instructions, the most copy-on-write a single closure
build can trigger. -/
def pikeSaves (re : Re) : Nat :=
  re.code.foldl (fun n inst => if inst.op = .save then n + 1 else n) 0

/-- What one starting position costs: the closure's marks and the steps at
one each per instruction, a copy-on-write per Save plus the accept's own,
the seed's block fill, and the visited set cleared. -/
def pikePosition (re : Re) : Nat :=
  re.code.size * 2 + (pikeSaves re + 2) * pikeBlock re + pikeWords re

/-- What the call pays before it starts: the ovector and the visited set,
zeroed once. -/
def pikeSetup (re : Re) : Nat := pikeBlock re + pikeWords re

/-- `R`: the scratch reservation, the number `pikeRoom` weighs. -/
def pikeReserved (re : Re) : Nat := (pikeRoom re false).1.reserved

/-! ## Reading the reservation -/

/-- `growthCap` in projection form, the shape a flag chain leaves behind. -/
theorem growthCap_val {e : Nat} {over : Bool}
    (h : (growthCap e over).2 = false) :
    (growthCap e over).1 = capFor e ∧ over = false := by
  have hp : growthCap e over = ((growthCap e over).1, (growthCap e over).2) := rfl
  rw [h] at hp
  exact ⟨growthCap_sound hp, growthCap_snd h⟩

/-- `pike_room` read off its own flag chain: a clean flag means every
capacity is the growth schedule's exact answer at its entry bound, and
means the flag went in clean too. -/
theorem pikeRoom_spec {re : Re} {room : Room} {over : Bool}
    (h : pikeRoom re over = (room, false)) :
    over = false ∧
      room.lists = capFor re.code.size ∧
      room.stk = capFor (re.code.size * 2) ∧
      room.tables = capFor (re.code.size * 4 + 2) ∧
      room.pool = capFor ((re.code.size * 4 + 2) * ((re.ncap + 1) * 2)) ∧
      room.words = re.code.size / 8 + 1 := by
  simp only [pikeRoom, Prod.mk.injEq] at h
  obtain ⟨hroom, hover⟩ := h
  subst hroom
  obtain ⟨-, f14⟩ := satAdd_snd hover
  obtain ⟨-, f13⟩ := satMul_snd f14
  obtain ⟨-, f12⟩ := satAdd_snd f13
  obtain ⟨-, f11⟩ := satMul_snd f12
  obtain ⟨-, f10⟩ := satAdd_snd f11
  obtain ⟨-, f9⟩ := satMul_snd f10
  obtain ⟨-, f8⟩ := satMul_snd f9
  obtain ⟨v8, f7⟩ := growthCap_val f8
  obtain ⟨v7, f6⟩ := satMul_snd f7
  obtain ⟨v6, f5⟩ := growthCap_val f6
  obtain ⟨v5, f4⟩ := satAdd_snd f5
  obtain ⟨v4, f3⟩ := satMul_snd f4
  obtain ⟨v3, f2⟩ := growthCap_val f3
  obtain ⟨v2, f1⟩ := satMul_snd f2
  obtain ⟨v1, f0⟩ := growthCap_val f1
  refine ⟨f0, ?_, ?_, ?_, ?_, rfl⟩
  · dsimp only
    rw [v1]
  · dsimp only
    rw [v3, v2]
  · dsimp only
    rw [v6, v5, v4]
  · dsimp only
    rw [v8, v7, v5, v4]

/-- The reservation itself, spelled out: the two thread lists, the closure
stack, the refcounts beside the free list, and the pool, each capacity times
its entry size. This is BOUNDS.md section 9's `R`, and — because context
creation reserves from these same counts — the bytes a preallocated context
holds. -/
theorem pikeReserved_eq {re : Re} (h : (pikeRoom re false).2 = false) :
    pikeReserved re =
      capFor re.code.size * (2 * thSize) + capFor (re.code.size * 2) * thSize +
        capFor (re.code.size * 4 + 2) * (2 * regSize) +
        capFor ((re.code.size * 4 + 2) * ((re.ncap + 1) * 2)) * regSize := by
  have hp : pikeRoom re false =
      ((pikeRoom re false).1, (pikeRoom re false).2) := rfl
  rw [h] at hp
  obtain ⟨-, hl, hs, ht, hpo, -⟩ := pikeRoom_spec hp
  rw [pikeReserved, pikeRoom_reserved hp, hl, hs, ht, hpo]

/-! ## Reading the price -/

/-- `pike_price` on its success path is one explicit certificate: the cost a
line in `n + 1` with the closed form's two coefficients, the stack and the
trail exactly nothing, the memory a constant, and no region prices at all. -/
theorem pikePrice_eq {re : Re} {cert : Cert} (h : pikePrice re = some cert) :
    (pikeRoom re false).2 = false ∧
      cert = ⟨.pike, .linear,
        ⟨1, pikeSetup re + pikeBlock re + 3 * pikeReserved re,
          pikePosition re, 0, 0, 0⟩,
        Poly.zero, Poly.zero,
        Poly.const (pikeSetup re + pikeBlock re + 2 * pikeReserved re), #[]⟩ := by
  simp only [pikePrice] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hover
    rw [Bool.not_eq_true] at hover
    obtain ⟨vres, f12⟩ := satAdd_snd hover
    obtain ⟨vheld, f11⟩ := satMul_snd f12
    obtain ⟨vsteady, f10⟩ := satAdd_snd f11
    obtain ⟨vgrowth, f9⟩ := satMul_snd f10
    obtain ⟨vbase, f8⟩ := satAdd_snd f9
    obtain ⟨vpos3, f7⟩ := satAdd_snd f8
    obtain ⟨vpos2, f6⟩ := satAdd_snd f7
    obtain ⟨vwrites, f5⟩ := satMul_snd f6
    obtain ⟨vwriters, f4⟩ := satAdd_snd f5
    obtain ⟨vpos1, f3⟩ := satMul_snd f4
    obtain ⟨vsetup, f2⟩ := satAdd_snd f3
    have hroomp : pikeRoom re (satMul ((re.ncap + 1) * 2) regSize false).2 =
        ((pikeRoom re (satMul ((re.ncap + 1) * 2) regSize false).2).1,
          (pikeRoom re (satMul ((re.ncap + 1) * 2) regSize false).2).2) := rfl
    rw [f2] at hroomp
    obtain ⟨f1, -⟩ := pikeRoom_spec hroomp
    obtain ⟨vblock, -⟩ := satMul_snd f1
    have hblock : (satMul ((re.ncap + 1) * 2) regSize false).1 = pikeBlock re := by
      rw [vblock, pikeBlock, Re.novec, Nat.mul_comm 2 (re.ncap + 1)]
    have hroom : (pikeRoom re (satMul ((re.ncap + 1) * 2) regSize false).2).1 =
        (pikeRoom re false).1 := by rw [f1]
    have hwords : (pikeRoom re (satMul ((re.ncap + 1) * 2) regSize false).2).1.words =
        pikeWords re := by rw [hroom]; rfl
    have hres : (pikeRoom re (satMul ((re.ncap + 1) * 2) regSize false).2).1.reserved =
        pikeReserved re := by rw [hroom]; rfl
    refine ⟨by rwa [f1] at f2, ?_⟩
    have hcert := h.symm
    simp only [Option.some.injEq] at hcert
    rw [hcert, vres, vheld, vsteady, vgrowth, vbase, vpos3, vpos2, vwrites,
      vwriters, vpos1, vsetup, hblock, hwords, hres]
    simp only [Cert.mk.injEq, Poly.zero, Poly.const, Poly.mk.injEq, pikeSetup,
      pikePosition, pikeSaves, true_and, and_true]
    omega

/-- The certified cost, as the number BOUNDS.md section 9 writes down. -/
theorem pikePrice_cost_val {re : Re} {cert : Cert} (h : pikePrice re = some cert)
    (n : Nat) :
    cert.cost.val n =
      pikeSetup re + pikeBlock re + 3 * pikeReserved re + pikePosition re * (n + 1) := by
  obtain ⟨-, hc⟩ := pikePrice_eq h
  subst hc
  simp [Poly.val, Poly.part]

/-- And the certified memory, which does not depend on the subject length —
the number a context sizes once. -/
theorem pikePrice_mem_val {re : Re} {cert : Cert} (h : pikePrice re = some cert)
    (n : Nat) :
    cert.mem.val n = pikeSetup re + pikeBlock re + 2 * pikeReserved re := by
  obtain ⟨-, hc⟩ := pikePrice_eq h
  subst hc
  simp [Poly.val, Poly.part, Poly.const]

/-! ## What an accepted certificate is worth -/

/-- Everything `pike_check`'s verdict carries: the program is eligible, the
price recomputes, the claimed cost and memory dominate it, and the stack and
the trail are exactly nothing. -/
theorem pikeCheck_spec {re : Re} {cert : Cert} (h : pikeCheck re cert = .crOk) :
    pikeOk re.code re.reps = true ∧ cert.config = .pike ∧
      cert.prices.size = 0 ∧ cert.complexity = .linear ∧
      ∃ need : Cert, pikePrice re = some need ∧
        polyGe cert.cost need.cost = true ∧ polyGe cert.mem need.mem = true ∧
        cert.stack = Poly.zero ∧ cert.trail = Poly.zero := by
  unfold pikeCheck at h
  split at h
  · cases h
  rename_i hok
  split at h
  · cases h
  rename_i hcfg
  split at h
  · cases h
  rename_i hpr
  split at h
  · cases h
  rename_i hcc
  split at h
  · cases h
  split at h
  · cases h
  rename_i need hneed
  split at h
  · cases h
  rename_i hcost
  split at h
  · cases h
  rename_i hstack
  split at h
  · cases h
  rename_i htrail
  split at h
  · cases h
  rename_i hmem
  obtain ⟨-, hneedc⟩ := pikePrice_eq hneed
  refine ⟨by simpa using hok, by simpa using hcfg, by simpa using hpr, hcc,
    need, hneed, by simpa using hcost, by simpa using hmem, ?_, ?_⟩
  · rw [polyEq_eq (show polyEq cert.stack need.stack = true by simpa using hstack),
      hneedc]
  · rw [polyEq_eq (show polyEq cert.trail need.trail = true by simpa using htrail),
      hneedc]

/-- The cost half of the transfer: an accepted claim is at least the closed
form at every subject length. -/
theorem pikeCheck_cost_dom {re : Re} {cert : Cert} (h : pikeCheck re cert = .crOk)
    (n : Nat) :
    pikeSetup re + pikeBlock re + 3 * pikeReserved re + pikePosition re * (n + 1) ≤
      cert.cost.val n := by
  obtain ⟨-, -, -, -, need, hneed, hge, -, -, -⟩ := pikeCheck_spec h
  have := polyGe_sound hge n
  rw [pikePrice_cost_val hneed n] at this
  exact this

/-- The memory half. -/
theorem pikeCheck_mem_dom {re : Re} {cert : Cert} (h : pikeCheck re cert = .crOk)
    (n : Nat) :
    pikeSetup re + pikeBlock re + 2 * pikeReserved re ≤ cert.mem.val n := by
  obtain ⟨-, -, -, -, need, hneed, -, hge, -, -⟩ := pikeCheck_spec h
  have := polyGe_sound hge n
  rw [pikePrice_mem_val hneed n] at this
  exact this

/-! ## What the pre-charge tests buy

Every charge on the lockstep path is compared against the remaining budget
before it is made, and a helper that is refused hands its state back with
whatever it had already charged. So the reading "the meter is inside both
ceilings" survives both arms of every step, and a whole run reports usage
no larger than the limits it was called under. That is the enforcement half
of R-6 and R-8 — the half that is about the matcher rather than about the
certificate — and it is what turns a certified budget into the absence of a
refusal, since a refusal is exactly a pre-charge test failing. -/

/-- The state a charging step hands back, whichever way it ended. The
helpers keep their partial charges on a refusal, so both arms carry a state
and an invariant about the meter has to hold of both. -/
def outSt {α : Type} (get : α → PikeSt) : POut α → PikeSt
  | .ok a => get a
  | .error st => st

/-- The meter inside both ceilings, the peak counted too. -/
def Meter.within (m : Meter) (lim : Limits) : Prop :=
  m.cost ≤ lim.cost ∧ m.mem ≤ lim.mem ∧ m.peak ≤ lim.mem

/-- A growth step keeps the reading. Both of its tests are pre-charge — the
new buffer against the memory left, the zeroing and copying against the cost
left — and the memory it hands back drops the old buffer, so the total it
briefly held is what the peak records and what the test compared. -/
theorem chargeGrow_meter {oldcap len esize maxv : Nat} {m m' : Meter}
    {lim : Limits} {cap : Nat} (hm : m.within lim)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    m'.within lim := by
  simp only [Meter.within] at hm ⊢
  simp only [chargeGrow] at h
  split at h
  · cases h
    exact hm
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          dsimp only
          omega

/-- Adding a charge that was tested against the cost left keeps the reading;
nothing else on the meter moves. The test comes first so that the state it
was made about is what the conclusion is about. -/
theorem within_charge {st : PikeSt} {lim : Limits} {k : Nat}
    (hk : ¬ k > lim.cost - st.m.cost) (hst : st.m.within lim) :
    ({ st with m := { st.m with cost := st.m.cost + k } } : PikeSt).m.within lim := by
  simp only [Meter.within] at hst ⊢
  omega

/-- Reading the invariant off a refusal. -/
theorem within_of_error {α : Type} {get : α → PikeSt} {x : POut α}
    {stE : PikeSt} {lim : Limits} (he : x = .error stE)
    (h : (outSt get x).m.within lim) : stE.m.within lim := by
  rw [he] at h
  exact h

/-- And off a success, for a step that answers a state. -/
theorem within_ok_id {x : POut PikeSt} {a : PikeSt} {lim : Limits}
    (he : x = .ok a) (h : (outSt id x).m.within lim) : a.m.within lim := by
  rw [he] at h
  exact h

/-- For one that answers a state and a handle. -/
theorem within_ok_fst {x : POut (PikeSt × Nat)} {a : PikeSt × Nat}
    {lim : Limits} (he : x = .ok a) (h : (outSt Prod.fst x).m.within lim) :
    a.1.m.within lim := by
  rw [he] at h
  exact h

/-- And for the list step, which answers a whole `StepOut`. -/
theorem within_ok_step {x : POut StepOut} {a : StepOut} {lim : Limits}
    (he : x = .ok a) (h : (outSt StepOut.st x).m.within lim) :
    a.st.m.within lim := by
  rw [he] at h
  exact h

/-! ### The charging helpers -/

theorem pikeDefer_within {st : PikeSt} {pc h : Nat} {lim : Limits}
    (hst : st.m.within lim) :
    (outSt id (pikeDefer st pc h lim)).m.within lim := by
  simp only [pikeDefer]
  split
  · exact hst
  · rename_i m cap hg
    exact chargeGrow_meter hst hg

theorem pikePark_within {st : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} (hst : st.m.within lim) :
    (outSt id (pikePark st intoNext pc h lim)).m.within lim := by
  simp only [pikePark]
  split <;> split
  · exact hst
  · rename_i m cap hg
    exact chargeGrow_meter hst hg
  · exact hst
  · rename_i m cap hg
    exact chargeGrow_meter hst hg

theorem pikeDrop_within {st : PikeSt} {h : Nat} {lim : Limits}
    (hst : st.m.within lim) :
    (outSt id (pikeDrop st h lim)).m.within lim := by
  simp only [pikeDrop]
  split
  · exact hst
  · split
    · split
      · exact hst
      · rename_i m cap hg
        exact chargeGrow_meter hst hg
    · exact hst

theorem pikeTake_fill_within {lim : Limits} : ∀ (k : Nat) (st : PikeSt),
    st.m.within lim → (outSt id (pikeTake.fill lim k st)).m.within lim := by
  intro k
  induction k with
  | zero =>
      intro st hst
      rw [pikeTake.fill]
      exact hst
  | succ n ih =>
      intro st hst
      rw [pikeTake.fill]
      split
      · exact hst
      · rename_i m cap hg
        exact ih _ (chargeGrow_meter hst hg)

theorem pikeTake_within {st : PikeSt} {novec : Nat} {lim : Limits}
    (hst : st.m.within lim) :
    (outSt Prod.fst (pikeTake st novec lim)).m.within lim := by
  simp only [pikeTake]
  split
  · exact hst
  · split
    · exact hst
    · split
      · exact hst
      · rename_i m cap hg
        split
        · rename_i he
          refine within_of_error he (pikeTake_fill_within _ _ ?_)
          exact chargeGrow_meter hst hg
        · rename_i he
          refine within_ok_id he (pikeTake_fill_within _ _ ?_)
          exact chargeGrow_meter hst hg

theorem pikeWrite_within {st : PikeSt} {novec h slot : Nat} {value : UInt32}
    {lim : Limits} (hst : st.m.within lim) :
    (outSt Prod.fst (pikeWrite st novec h slot value lim)).m.within lim := by
  simp only [pikeWrite]
  split
  · split
    · exact hst
    · rename_i hcopy
      have hb := within_charge hcopy hst
      split
      · rename_i he
        exact within_of_error he (pikeTake_within hb)
      · rename_i he
        -- The answered state carries the copy, which the meter does not read,
        -- so the invariant has to be read off before it is matched.
        have hfresh := within_ok_fst he (pikeTake_within hb)
        exact hfresh
  · exact hst

/-! ### The closure, the step, and the position loop -/

-- The dispatch below covers two dozen opcode arms by trying one helper
-- shape after another, and a shape that does not fit is only found not to
-- fit by unfolding two helpers against each other. That is where the budget
-- goes; the proof itself is shallow.
set_option maxHeartbeats 1000000 in
/-- The closure loop keeps the reading. Each iteration either hands back the
state it was given, charges the one unit it has just tested for the mark, or
passes the charged state to a helper that keeps the reading itself. -/
theorem pikeAdd_go_within (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (intoNext : Bool) (pos : Nat) :
    ∀ (fuel : Nat) (st : PikeSt), st.m.within lim →
      (outSt id (pikeAdd.go re s mo lim intoNext pos fuel st)).m.within lim := by
  intro fuel
  induction fuel with
  | zero =>
      intro st hst
      rw [pikeAdd.go]
      exact hst
  | succ f ih =>
      intro st hst
      simp only [pikeAdd.go]
      split
      · exact hst
      · split
        · split
          · rename_i he
            refine within_of_error he (pikeDrop_within ?_)
            exact hst
          · rename_i he
            refine ih _ (within_ok_id he (pikeDrop_within ?_))
            exact hst
        · split
          · exact hst
          · rename_i hmark
            have hb := within_charge hmark hst
            repeat' split
            all_goals first
              | exact hb
              -- one helper, then the loop again
              | (rename_i he
                 first
                   | (refine within_of_error he (pikeDrop_within ?_); exact hb)
                   | (refine within_of_error he (pikeDefer_within ?_); exact hb)
                   | (refine within_of_error he (pikePark_within ?_); exact hb)
                   | (refine ih _ (within_ok_id he (pikeDrop_within ?_)); exact hb)
                   | (refine ih _ (within_ok_id he (pikeDefer_within ?_)); exact hb)
                   | (refine ih _ (within_ok_id he (pikePark_within ?_)); exact hb))
              -- a fork or a Save: two helpers in a row
              | (rename_i h₁ _x _stB he
                 first
                   | (refine within_of_error he (pikeDefer_within
                        (within_ok_id h₁ (pikeDefer_within ?_))); exact hb)
                   | (refine ih _ (within_ok_id he (pikeDefer_within
                        (within_ok_id h₁ (pikeDefer_within ?_)))); exact hb)
                   | (refine within_of_error he (pikeDefer_within
                        (within_ok_fst h₁ (pikeWrite_within ?_))); exact hb)
                   | (refine ih _ (within_ok_id he (pikeDefer_within
                        (within_ok_fst h₁ (pikeWrite_within ?_)))); exact hb))
              -- the Save's own copy-on-write, refused
              | (rename_i he
                 refine within_of_error he (pikeWrite_within ?_)
                 exact hb)

theorem pikeAdd_within {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {intoNext : Bool} {pos pc0 h0 : Nat} {st : PikeSt}
    (hst : st.m.within lim) :
    (outSt id (pikeAdd re s mo lim intoNext pos pc0 h0 st)).m.within lim := by
  rw [pikeAdd]
  split
  · rename_i he
    exact within_of_error he (pikeDefer_within hst)
  · rename_i he
    exact pikeAdd_go_within re s mo lim intoNext pos _ _
      (within_ok_id he (pikeDefer_within hst))

theorem dropRest_within {lim : Limits} : ∀ (rest : List Th) (st : PikeSt),
    st.m.within lim → (outSt id (dropRest lim rest st)).m.within lim := by
  intro rest
  induction rest with
  | nil =>
      intro st hst
      rw [dropRest]
      exact hst
  | cons th rest ih =>
      intro st hst
      rw [dropRest]
      split
      · rename_i he
        exact within_of_error he (pikeDrop_within hst)
      · rename_i he
        exact ih _ (within_ok_id he (pikeDrop_within hst))

/-- Stepping a built list keeps the reading: one tested unit per suspended
thread, and every survivor handed to a helper. -/
theorem stepThreads_within (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (start pos : Nat) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      st.m.within lim →
      (outSt StepOut.st (stepThreads re s mo lim start pos threads st mh
        seeding matched)).m.within lim := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched hst
      rw [stepThreads]
      exact hst
  | cons th rest ih =>
      intro st mh seeding matched hst
      simp only [stepThreads]
      split
      · exact hst
      · rename_i hstep
        have hb := within_charge hstep hst
        repeat' split
        all_goals first
          | exact hb
          | (rename_i he
             first
               | (refine within_of_error he (pikeDrop_within ?_); exact hb)
               | (refine ih _ _ _ _ (within_ok_id he (pikeDrop_within ?_))
                  exact hb)
               | (refine within_of_error he (pikeAdd_within ?_); exact hb)
               | (refine ih _ _ _ _ (within_ok_id he (pikeAdd_within ?_))
                  exact hb)
               | (refine within_of_error he (pikeWrite_within ?_); exact hb))
          | (rename_i h₁ _x _stB he
             refine within_of_error he
               (pikeDrop_within (within_ok_fst h₁ (pikeWrite_within ?_)))
             exact hb)
          | (rename_i h₁ _x₁ _s₁ h₂ _x₂ _s₂ he
             first
               | (refine within_of_error he (dropRest_within _ _
                    (within_ok_id h₂ (pikeDrop_within
                      (within_ok_fst h₁ (pikeWrite_within ?_)))))
                  exact hb)
               | (refine within_ok_id he (dropRest_within _ _
                    (within_ok_id h₂ (pikeDrop_within
                      (within_ok_fst h₁ (pikeWrite_within ?_)))))
                  exact hb))

theorem pikeSeed_within {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start pos : Nat} {st : PikeSt} (hst : st.m.within lim) :
    (outSt id (pikeSeed re s mo lim start pos st)).m.within lim := by
  simp only [pikeSeed]
  split
  · exact hst
  · split
    · rename_i he
      exact within_of_error he (pikeTake_within hst)
    · rename_i he
      split
      · exact within_ok_fst he (pikeTake_within hst)
      · rename_i hblock
        refine pikeAdd_within ?_
        exact within_charge hblock (within_ok_fst he (pikeTake_within hst))

/-- The position loop keeps the reading: it charges the visited set's clear
against the budget left, and everything else it does is a helper's. -/
theorem pikeLoop_within (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) (anchored : Bool) (words : Nat) :
    ∀ (steps pos : Nat) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      st.m.within lim →
      (pikeLoop re s mo lim start anchored words steps pos st mh seeding
        matched).1.m.within lim := by
  intro steps
  induction steps with
  | zero =>
      intro pos st mh seeding matched hst
      rw [pikeLoop]
      exact hst
  | succ k ih =>
      intro pos st mh seeding matched hst
      have hseeded : (outSt id (if seeding && (!anchored || pos == start) then
          pikeSeed re s mo lim start pos st
          else (Except.ok st : POut PikeSt))).m.within lim := by
        split
        · exact pikeSeed_within hst
        · exact hst
      simp only [pikeLoop]
      split
      · rename_i he
        exact within_of_error he hseeded
      · rename_i he
        have hstO := within_ok_id he hseeded
        split
        · exact hstO
        · rename_i hwords
          have hb := within_charge hwords hstO
          split
          · rename_i hx
            refine within_of_error hx (stepThreads_within re s mo lim start pos
              _ _ mh seeding matched ?_)
            exact hb
          · rename_i out hx
            have hout : out.st.m.within lim := by
              refine within_ok_step hx (stepThreads_within re s mo lim start pos
                _ _ mh seeding matched ?_)
              exact hb
            split
            · exact hout
            · split
              · exact hout
              · exact ih _ _ _ _ _ hout

/-! ### The whole call -/

/-- A lockstep run never reports a cost above the limit it was called under:
the setup is tested before it is charged, and so is everything after it. -/
theorem pikeRun_cost_le_limit (re : Re) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (init : PikeSt) :
    (pikeRun re s start mo lim init).usage.cost ≤ lim.cost := by
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · rename_i hsetup
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hsetup
        have hin : ∀ st : PikeSt,
            st.m = ⟨re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1)⟩ → st.m.within lim := by
          intro st hm
          simp only [Meter.within, hm]
          omega
        split
        · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).1
          exact hin _ rfl
        · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).1
          exact hin _ rfl
        · split
          · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).1
            exact hin _ rfl
          · rename_i hblock
            have key : ∀ c : Nat, c ≤ lim.cost →
                ¬ re.novec * regSize > lim.cost - c →
                c + re.novec * regSize ≤ lim.cost := by
              intro c h₁ h₂
              omega
            refine key _ ?_ hblock
            refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).1
            exact hin _ rfl

/-- And never a memory peak above the limit: the growth helper tests the new
buffer against the memory left before it takes it, and the peak it records is
that same total. -/
theorem pikeRun_mem_le_limit (re : Re) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (init : PikeSt) :
    (pikeRun re s start mo lim init).usage.mem ≤ lim.mem := by
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · rename_i hsetup
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hsetup
        have hin : ∀ st : PikeSt,
            st.m = ⟨re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1)⟩ → st.m.within lim := by
          intro st hm
          simp only [Meter.within, hm]
          omega
        split
        · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).2.2
          exact hin _ rfl
        · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).2.2
          exact hin _ rfl
        · split
          · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).2.2
            exact hin _ rfl
          · refine (pikeLoop_within re s mo lim start _ _ _ _ _ _ _ _ ?_).2.2
            exact hin _ rfl

/-! ## What the closure needs from the program

The per-position count of BOUNDS.md section 9 rests on the visited set: a
build marks each instruction at most once and parks at most one thread per
mark, so a thread list never holds more than `C` entries. That argument needs
one thing from the program which `pikeRun` cannot see for itself — that the
pcs the matcher moves to are real instructions. An out-of-range pc reads as
the default instruction, a `chr`, which parks without ever being marked (the
visited set is only as long as the program), and a pattern that could reach
one would park without paying.

`ReWf` states exactly that, plus the two declared maxima the growth argument
needs. It is a fact about compiler output; proving `Ref.compile` supplies it
is the natural next step, and until then it travels as a hypothesis. -/

/-- Where the lockstep matcher can go from `pc`: the epsilon successors the
closure defers, and the one a consuming instruction advances to. Read off
the instruction the same way the two loops read it. -/
def pikeTargets (re : Re) (pc : Nat) : List Nat :=
  match (re.code[pc]!).op with
  | .chr | .chrCI | .cls | .any | .anyNoNL => [pc + 1]
  | .split => [(re.code[pc]!).arg, (re.code[pc]!).alt]
  | .jump => [(re.code[pc]!).arg]
  | .save | .repZero | .repEnter
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => [pc + 1]
  | .repLoop | .repNext =>
      [(re.reps[(re.code[pc]!).arg]!).body, (re.reps[(re.code[pc]!).arg]!).after]
  | _ => []

/-- The program-shape facts the lockstep bound needs: a program with
something in it, successors that stay inside it, and the two declared maxima
that keep the growth schedule from clamping. -/
structure ReWf (re : Re) : Prop where
  sized : 0 < re.code.size
  targets : ∀ pc, pc < re.code.size → ∀ t ∈ pikeTargets re pc, t < re.code.size
  coded : re.code.size ≤ maxCode
  slots : re.novec ≤ maxOvec

/-- Every pc in this array is a real instruction. -/
def listInRange (re : Re) (a : Array Th) : Prop :=
  ∀ th ∈ a.toList, th.pc < re.code.size

theorem listInRange_push {re : Re} {a : Array Th} {pc hh : Nat}
    (h : listInRange re a) (ht : pc < re.code.size) :
    listInRange re (a.push ⟨pc, hh⟩) := by
  intro y hy
  rw [Array.toList_push] at hy
  rcases List.mem_append.mp hy with h1 | h1
  · exact h y h1
  · simp only [List.mem_singleton] at h1
    subst h1
    exact ht

theorem listInRange_pop {re : Re} {a : Array Th} (h : listInRange re a) :
    listInRange re a.pop := by
  intro y hy
  rw [Array.toList_pop] at hy
  exact h y (List.dropLast_subset _ hy)

theorem listInRange_back {re : Re} {a : Array Th} (h : listInRange re a)
    (hne : a.size ≠ 0) : a.back!.pc < re.code.size := by
  have hlt : a.size - 1 < a.toList.length := by simp; omega
  rw [Array.back!, getElem!_pos a (a.size - 1) (by simpa using hlt),
    ← Array.getElem_toList]
  exact h _ (List.getElem_mem hlt)

theorem listInRange_mem {re : Re} {a : Array Th} (h : listInRange re a)
    {th : Th} (hth : th ∈ a.toList) : th.pc < re.code.size := h th hth

/-- What a closure build starts from and hands on: a visited set sized to the
program, and nothing but real instructions on the stack and in the lists. -/
structure BuildOk (re : Re) (st : PikeSt) : Prop where
  seenSize : st.seen.size = re.code.size
  stk : listInRange re st.stk
  clist : listInRange re st.clist
  nlist : listInRange re st.nlist

/-! ### What the helpers leave alone -/

/-- The three fields the closure's bookkeeping reads, unmoved. Every helper
but `pikePark` preserves this, which is why a build's list growth is exactly
its park count. -/
def Untouched (re : Re) (seen0 : Array Bool) (c0 n0 : Array Th)
    (st : PikeSt) : Prop :=
  st.seen = seen0 ∧ listInRange re st.stk ∧ st.clist = c0 ∧ st.nlist = n0

theorem pikeDefer_lists {st st' : PikeSt} {pc h : Nat} {lim : Limits}
    (hok : pikeDefer st pc h lim = .ok st') :
    st'.clist = st.clist ∧ st'.nlist = st.nlist := by
  unfold pikeDefer at hok
  split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩

theorem pikeDrop_lists {st st' : PikeSt} {h : Nat} {lim : Limits}
    (hok : pikeDrop st h lim = .ok st') :
    st'.clist = st.clist ∧ st'.nlist = st.nlist := by
  unfold pikeDrop at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩
  · split at hok
    · split at hok
      · simp at hok
      · injection hok with hok
        subst hok
        exact ⟨rfl, rfl⟩
    · injection hok with hok
      subst hok
      exact ⟨rfl, rfl⟩

theorem pikeTake_fill_lists {lim : Limits} : ∀ {k : Nat} {st st' : PikeSt},
    pikeTake.fill lim k st = .ok st' →
    st'.clist = st.clist ∧ st'.nlist = st.nlist := by
  intro k
  induction k with
  | zero =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      injection hok with hok
      subst hok
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      split at hok
      · simp at hok
      · obtain ⟨h1, h2⟩ := ih hok
        exact ⟨h1, h2⟩

theorem pikeTake_lists {st st' : PikeSt} {novec hOut : Nat} {lim : Limits}
    (hok : pikeTake st novec lim = .ok (st', hOut)) :
    st'.clist = st.clist ∧ st'.nlist = st.nlist := by
  unfold pikeTake at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    injection hok with hok _
    subst hok
    exact ⟨rfl, rfl⟩
  · split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i hfill
          injection hok with hok
          injection hok with hok _
          subst hok
          obtain ⟨h1, h2⟩ := pikeTake_fill_lists hfill
          exact ⟨h1, h2⟩

theorem pikeWrite_lists {st st' : PikeSt} {novec h slot hOut : Nat}
    {value : UInt32} {lim : Limits}
    (hok : pikeWrite st novec h slot value lim = .ok (st', hOut)) :
    st'.clist = st.clist ∧ st'.nlist = st.nlist := by
  unfold pikeWrite at hok
  simp only [] at hok
  split at hok
  · split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i hTake
        injection hok with hok
        injection hok with hok _
        subst hok
        obtain ⟨h1, h2⟩ := pikeTake_lists hTake
        exact ⟨h1, h2⟩
  · injection hok with hok
    injection hok with hok _
    subst hok
    exact ⟨rfl, rfl⟩

/-- A park pushes onto exactly one list and leaves the other where it was. -/
theorem pikePark_lists {st st' : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} (hok : pikePark st intoNext pc h lim = .ok st') :
    (intoNext = true → st'.clist = st.clist ∧ st'.nlist = st.nlist.push ⟨pc, h⟩) ∧
      (intoNext = false →
        st'.nlist = st.nlist ∧ st'.clist = st.clist.push ⟨pc, h⟩) := by
  unfold pikePark at hok
  split at hok
  · rename_i hin
    split at hok
    · simp at hok
    · injection hok with hok
      subst hok
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun hf => by simp [hin] at hf⟩
  · rename_i hin
    split at hok
    · simp at hok
    · injection hok with hok
      subst hok
      exact ⟨fun ht => absurd ht hin, fun _ => ⟨rfl, rfl⟩⟩

theorem Untouched.defer {re : Re} {seen0 : Array Bool} {c0 n0 : Array Th}
    {stA stB : PikeSt} {pc h : Nat} {lim : Limits}
    (he : pikeDefer stA pc h lim = .ok stB) (ht : pc < re.code.size)
    (hU : Untouched re seen0 c0 n0 stA) : Untouched re seen0 c0 n0 stB := by
  obtain ⟨hs, hk, hc, hn⟩ := hU
  obtain ⟨hstk, hseen⟩ := pikeDefer_ok he
  obtain ⟨hcl, hnl⟩ := pikeDefer_lists he
  exact ⟨hseen.trans hs, by rw [hstk]; exact listInRange_push hk ht,
    hcl.trans hc, hnl.trans hn⟩

theorem Untouched.drop {re : Re} {seen0 : Array Bool} {c0 n0 : Array Th}
    {stA stB : PikeSt} {h : Nat} {lim : Limits}
    (he : pikeDrop stA h lim = .ok stB) (hU : Untouched re seen0 c0 n0 stA) :
    Untouched re seen0 c0 n0 stB := by
  obtain ⟨hs, hk, hc, hn⟩ := hU
  obtain ⟨hstk, hseen⟩ := pikeDrop_ok he
  obtain ⟨hcl, hnl⟩ := pikeDrop_lists he
  exact ⟨hseen.trans hs, by rw [hstk]; exact hk, hcl.trans hc, hnl.trans hn⟩

theorem Untouched.write {re : Re} {seen0 : Array Bool} {c0 n0 : Array Th}
    {stA stB : PikeSt} {novec h slot hOut : Nat} {value : UInt32}
    {lim : Limits}
    (he : pikeWrite stA novec h slot value lim = .ok (stB, hOut))
    (hU : Untouched re seen0 c0 n0 stA) : Untouched re seen0 c0 n0 stB := by
  obtain ⟨hs, hk, hc, hn⟩ := hU
  obtain ⟨hstk, hseen⟩ := pikeWrite_ok he
  obtain ⟨hcl, hnl⟩ := pikeWrite_lists he
  exact ⟨hseen.trans hs, by rw [hstk]; exact hk, hcl.trans hc, hnl.trans hn⟩

/-! ### The dedup bound on one closure build -/

/-- What a build may still add to the lists: the entries already parked, plus
one for every instruction it has yet to mark. -/
def buildMeasure (st : PikeSt) : Nat :=
  st.clist.size + st.nlist.size + unmarked st.seen

set_option maxHeartbeats 1000000 in
/-- One closure build never adds more to the thread lists than it has marks
left to make. Each iteration pops one entry: a pc already seen only lets a
handle go, and a fresh pc marks the visited set — paying one off the
unvisited count — before it parks at most one thread. That the mark really
lands is what `ReWf` buys: the pc is a real instruction, so it is inside the
visited set rather than read as the default `chr`, which would park for
free. -/
theorem pikeAdd_go_build (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (intoNext : Bool) (pos : Nat) :
    ∀ (fuel : Nat) (st st' : PikeSt),
      pikeAdd.go re s mo lim intoNext pos fuel st = .ok st' → BuildOk re st →
      BuildOk re st' ∧ buildMeasure st' ≤ buildMeasure st ∧
        (intoNext = true → st'.clist = st.clist) ∧
        (intoNext = false → st'.nlist = st.nlist) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st st' h _
      rw [pikeAdd.go] at h
      cases h
  | succ f ih =>
      intro st st' h hok
      obtain ⟨hsz, hstk, hcl0, hnl0⟩ := hok
      simp only [pikeAdd.go] at h
      -- The whole dispatch funnels into one composition step: whatever a
      -- branch hands the loop, it is measured against the state this
      -- iteration began with.
      have hstep : ∀ stA : PikeSt, BuildOk re stA →
          buildMeasure stA ≤ buildMeasure st →
          (intoNext = true → stA.clist = st.clist) →
          (intoNext = false → stA.nlist = st.nlist) →
          pikeAdd.go re s mo lim intoNext pos f stA = .ok st' →
          BuildOk re st' ∧ buildMeasure st' ≤ buildMeasure st ∧
            (intoNext = true → st'.clist = st.clist) ∧
            (intoNext = false → st'.nlist = st.nlist) := by
        intro stA hokA hmA hcA hnA hgo
        obtain ⟨h1, h2, h3, h4⟩ := ih stA st' hgo hokA
        exact ⟨h1, Nat.le_trans h2 hmA, fun hin => (h3 hin).trans (hcA hin),
          fun hin => (h4 hin).trans (hnA hin)⟩
      split at h
      · injection h with h
        subst h
        exact ⟨⟨hsz, hstk, hcl0, hnl0⟩, Nat.le_refl _, fun _ => rfl, fun _ => rfl⟩
      · rename_i hemp
        have hne : st.stk.size ≠ 0 := by simpa using hemp
        have hpcv : st.stk.back!.pc < re.code.size := listInRange_back hstk hne
        have hpop : listInRange re st.stk.pop := listInRange_pop hstk
        have htgt := hwf.targets _ hpcv
        split at h
        · -- Already visited: the pop pays for the iteration.
          split at h
          · cases h
          · rename_i stD hdr
            obtain ⟨hstkD, hseenD⟩ := pikeDrop_ok hdr
            obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
            refine hstep stD ⟨by rw [hseenD]; exact hsz,
                by rw [hstkD]; exact hpop, by rw [hclD]; exact hcl0,
                by rw [hnlD]; exact hnl0⟩ ?_
              (fun _ => hclD) (fun _ => hnlD) h
            exact Nat.le_of_eq (by simp only [buildMeasure, hseenD, hclD, hnlD])
        · -- A fresh pc: the mark pays for the park.
          rename_i hseenF
          have hfalse : st.seen[st.stk.back!.pc]! = false := by simpa using hseenF
          have hu1 : unmarked (st.seen.set! st.stk.back!.pc true) + 1 =
              unmarked st.seen := unmarked_set_lt (by omega) hfalse
          split at h
          · cases h
          · have hU0 : Untouched re (st.seen.set! st.stk.back!.pc true)
                st.clist st.nlist
                { st with
                  stk := st.stk.pop
                  seen := st.seen.set! st.stk.back!.pc true
                  m := { st.m with cost := st.m.cost + 1 } } :=
              ⟨rfl, hpop, rfl, rfl⟩
            have hfromU : ∀ stA : PikeSt,
                Untouched re (st.seen.set! st.stk.back!.pc true)
                  st.clist st.nlist stA →
                pikeAdd.go re s mo lim intoNext pos f stA = .ok st' →
                BuildOk re st' ∧ buildMeasure st' ≤ buildMeasure st ∧
                  (intoNext = true → st'.clist = st.clist) ∧
                  (intoNext = false → st'.nlist = st.nlist) := by
              intro stA hU hgo
              obtain ⟨hs, hk, hc, hn⟩ := hU
              refine hstep stA ⟨by rw [hs, Array.size_set!]; exact hsz, hk,
                  by rw [hc]; exact hcl0, by rw [hn]; exact hnl0⟩ ?_
                (fun _ => hc) (fun _ => hn) hgo
              simp only [buildMeasure, hs, hc, hn]
              omega
            have hfromP : ∀ stA stB : PikeSt,
                Untouched re (st.seen.set! st.stk.back!.pc true)
                  st.clist st.nlist stA →
                pikePark stA intoNext st.stk.back!.pc st.stk.back!.h lim = .ok stB →
                pikeAdd.go re s mo lim intoNext pos f stB = .ok st' →
                BuildOk re st' ∧ buildMeasure st' ≤ buildMeasure st ∧
                  (intoNext = true → st'.clist = st.clist) ∧
                  (intoNext = false → st'.nlist = st.nlist) := by
              intro stA stB hU hpk hgo
              obtain ⟨hs, hk, hc, hn⟩ := hU
              obtain ⟨hstkB, hseenB⟩ := pikePark_ok hpk
              obtain ⟨hinT, hinF⟩ := pikePark_lists hpk
              have hszB : stB.seen.size = re.code.size := by
                rw [hseenB, hs, Array.size_set!]; exact hsz
              have hstkB' : listInRange re stB.stk := by rw [hstkB]; exact hk
              by_cases hin : intoNext = true
              · obtain ⟨hcB, hnB⟩ := hinT hin
                refine hstep stB ⟨hszB, hstkB', by rw [hcB, hc]; exact hcl0,
                    by rw [hnB, hn]
                       exact listInRange_push hnl0 hpcv⟩ ?_
                  (fun _ => hcB.trans hc) (fun hf => by simp [hin] at hf) hgo
                simp only [buildMeasure, hseenB, hs, hcB, hnB, hc, hn,
                  Array.size_push]
                omega
              · obtain ⟨hnB, hcB⟩ := hinF (by simpa using hin)
                refine hstep stB ⟨hszB, hstkB',
                    by rw [hcB, hc]
                       exact listInRange_push hcl0 hpcv,
                    by rw [hnB, hn]; exact hnl0⟩ ?_
                  (fun ht => absurd ht hin) (fun _ => hnB.trans hn) hgo
                simp only [buildMeasure, hseenB, hs, hcB, hnB, hc, hn,
                  Array.size_push]
                omega
            cases hop : (re.code[(st.stk.back!).pc]!).op <;> simp only [hop] at h
            case chr | chrCI | cls | any | anyNoNL | accept =>
              split at h
              · cases h
              · rename_i stB hpk
                exact hfromP _ _ hU0 hpk h
            case bsr =>
              split at h
              · cases h
              · rename_i stB hdr
                exact hfromU _ (hU0.drop hdr) h
            case split =>
              split at h
              · cases h
              · rename_i stB hd1
                split at h
                · cases h
                · rename_i stC hd2
                  exact hfromU _
                    ((hU0.defer hd1 (htgt _ (by simp [pikeTargets, hop]))).defer
                      hd2 (htgt _ (by simp [pikeTargets, hop]))) h
            case jump | repZero | repEnter =>
              split at h
              · cases h
              · rename_i stB hdf
                exact hfromU _
                  (hU0.defer hdf (htgt _ (by simp [pikeTargets, hop]))) h
            case save =>
              split at h
              · cases h
              · rename_i stB hOut hw
                split at h
                · cases h
                · rename_i stC hdf
                  exact hfromU _
                    ((hU0.write hw).defer hdf
                      (htgt _ (by simp [pikeTargets, hop]))) h
            case circ | doll | dollE | sod | eod | eodn | wordB | notWordB =>
              split at h <;> rename_i hcnd
              · split at h
                · cases h
                · rename_i stB hdf
                  exact hfromU _
                    (hU0.defer hdf (htgt _ (by simp [pikeTargets, hop]))) h
              · split at h
                · cases h
                · rename_i stB hdr
                  exact hfromU _ (hU0.drop hdr) h
            case circM | dollM =>
              split at h <;> rename_i hz <;> split at h <;> rename_i hcnd
              · split at h
                · cases h
                · rename_i stB hdf
                  exact hfromU _
                    (hU0.defer hdf (htgt _ (by simp [pikeTargets, hop]))) h
              · split at h
                · cases h
                · rename_i stB hdr
                  exact hfromU _ (hU0.drop hdr) h
              · split at h
                · cases h
                · rename_i stB hdf
                  exact hfromU _
                    (hU0.defer hdf (htgt _ (by simp [pikeTargets, hop]))) h
              · split at h
                · cases h
                · rename_i stB hdr
                  exact hfromU _ (hU0.drop hdr) h
            case repLoop | repNext =>
              split at h <;> rename_i hgr <;>
                (split at h
                 · cases h
                 · rename_i stB hd1
                   split at h
                   · cases h
                   · rename_i stC hd2
                     exact hfromU _
                       ((hU0.defer hd1 (htgt _ (by simp [pikeTargets, hop]))).defer
                         hd2 (htgt _ (by simp [pikeTargets, hop]))) h)

/-- `pikeAdd` itself: the one entry it seeds the stack with is a real
instruction, so the build's own bound carries over to the whole call. -/
theorem pikeAdd_build (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (intoNext : Bool) (pos pc0 h0 : Nat) {st st' : PikeSt}
    (h : pikeAdd re s mo lim intoNext pos pc0 h0 st = .ok st')
    (hpc : pc0 < re.code.size) (hok : BuildOk re st) :
    BuildOk re st' ∧ buildMeasure st' ≤ buildMeasure st ∧
      (intoNext = true → st'.clist = st.clist) ∧
      (intoNext = false → st'.nlist = st.nlist) := by
  rw [pikeAdd] at h
  split at h
  · cases h
  · rename_i stD hdf
    obtain ⟨hstkD, hseenD⟩ := pikeDefer_ok hdf
    obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdf
    obtain ⟨h1, h2, h3, h4⟩ := pikeAdd_go_build re s mo lim hwf intoNext pos _ _ _ h
      ⟨by rw [hseenD]; exact hok.seenSize,
        by rw [hstkD]; exact listInRange_push hok.stk hpc,
        by rw [hclD]; exact hok.clist, by rw [hnlD]; exact hok.nlist⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · simp only [buildMeasure, hseenD, hclD, hnlD] at h2
      exact h2
    · intro hin
      exact (h3 hin).trans hclD
    · intro hin
      exact (h4 hin).trans hnlD

/-! ### The bound carried through one position -/

theorem dropRest_build {lim : Limits} : ∀ (rest : List Th) (st st' : PikeSt),
    dropRest lim rest st = .ok st' →
    st'.seen = st.seen ∧ st'.stk = st.stk ∧ st'.clist = st.clist ∧
      st'.nlist = st.nlist := by
  intro rest
  induction rest with
  | nil =>
      intro st st' h
      rw [dropRest] at h
      injection h with h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons th rest ih =>
      intro st st' h
      rw [dropRest] at h
      split at h
      · cases h
      · rename_i stD hdr
        obtain ⟨hstkD, hseenD⟩ := pikeDrop_ok hdr
        obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
        obtain ⟨h1, h2, h3, h4⟩ := ih _ _ h
        exact ⟨h1.trans hseenD, h2.trans hstkD, h3.trans hclD, h4.trans hnlD⟩

/-- Seeding a position builds into the current list, so it leaves the next
one alone and spends marks for what it parks. -/
theorem pikeSeed_build (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos : Nat) {st st' : PikeSt}
    (h : pikeSeed re s mo lim start pos st = .ok st') (hok : BuildOk re st) :
    BuildOk re st' ∧ buildMeasure st' ≤ buildMeasure st ∧
      st'.nlist = st.nlist := by
  simp only [pikeSeed] at h
  split at h
  · injection h with h
    subst h
    exact ⟨hok, Nat.le_refl _, rfl⟩
  · split at h
    · cases h
    · rename_i stT sh ht
      obtain ⟨hstkT, hseenT⟩ := pikeTake_ok ht
      obtain ⟨hclT, hnlT⟩ := pikeTake_lists ht
      have hokT : BuildOk re stT :=
        ⟨by rw [hseenT]; exact hok.seenSize, by rw [hstkT]; exact hok.stk,
          by rw [hclT]; exact hok.clist, by rw [hnlT]; exact hok.nlist⟩
      split at h
      · cases h
      · obtain ⟨h1, h2, -, h4⟩ :=
          pikeAdd_build re s mo lim hwf false pos 0 sh h hwf.sized
            ⟨hokT.seenSize, hokT.stk, hokT.clist, hokT.nlist⟩
        refine ⟨h1, ?_, (h4 rfl).trans hnlT⟩
        simp only [buildMeasure] at h2 ⊢
        rw [hclT, hnlT, hseenT] at h2
        exact h2

set_option maxHeartbeats 1000000 in
/-- Stepping the built list closes the survivors into the next one, and each
of those builds pays its own marks. The list is a snapshot of `clist`, whose
pcs are all real instructions, so every closure the step opens starts from
one too. -/
theorem stepThreads_build (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos : Nat) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool)
      (out : StepOut),
      stepThreads re s mo lim start pos threads st mh seeding matched = .ok out →
      (∀ th ∈ threads, th.pc < re.code.size) → BuildOk re st →
      BuildOk re out.st ∧ buildMeasure out.st ≤ buildMeasure st ∧
        out.st.clist = st.clist := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched out h _ hok
      rw [stepThreads] at h
      injection h with h
      subst h
      exact ⟨hok, Nat.le_refl _, rfl⟩
  | cons th rest ih =>
      intro st mh seeding matched out h hpcs hok
      have hthpc : th.pc < re.code.size := hpcs th List.mem_cons_self
      have hrest : ∀ t ∈ rest, t.pc < re.code.size :=
        fun t htm => hpcs t (List.mem_cons_of_mem _ htm)
      have hstep : ∀ stA : PikeSt, BuildOk re stA →
          buildMeasure stA ≤ buildMeasure st → stA.clist = st.clist →
          stepThreads re s mo lim start pos rest stA mh seeding matched = .ok out →
          BuildOk re out.st ∧ buildMeasure out.st ≤ buildMeasure st ∧
            out.st.clist = st.clist := by
        intro stA hokA hmA hcA hgo
        obtain ⟨h1, h2, h3⟩ := ih stA mh seeding matched out hgo hrest hokA
        exact ⟨h1, Nat.le_trans h2 hmA, h3.trans hcA⟩
      have hdrop : ∀ (stA stB : PikeSt) (hh : Nat), BuildOk re stA →
          buildMeasure stA ≤ buildMeasure st → stA.clist = st.clist →
          pikeDrop stA hh lim = .ok stB →
          BuildOk re stB ∧ buildMeasure stB ≤ buildMeasure st ∧
            stB.clist = st.clist := by
        intro stA stB hh hokA hmA hcA hdr
        obtain ⟨hstkD, hseenD⟩ := pikeDrop_ok hdr
        obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
        refine ⟨⟨by rw [hseenD]; exact hokA.seenSize,
          by rw [hstkD]; exact hokA.stk, by rw [hclD]; exact hokA.clist,
          by rw [hnlD]; exact hokA.nlist⟩, ?_, hclD.trans hcA⟩
        simp only [buildMeasure] at hmA ⊢
        rw [hseenD, hclD, hnlD]
        exact hmA
      simp only [stepThreads] at h
      split at h
      · cases h
      · have hokc : BuildOk re { st with
            m := { st.m with cost := st.m.cost + 1 } } :=
          ⟨hok.seenSize, hok.stk, hok.clist, hok.nlist⟩
        cases hop : (re.code[th.pc]!).op <;> simp only [hop] at h
        case chr | chrCI | cls | any | anyNoNL =>
          have hnext : th.pc + 1 < re.code.size :=
            hwf.targets _ hthpc _ (by simp [pikeTargets, hop])
          split at h
          · split at h
            · cases h
            · rename_i stA hadd
              obtain ⟨o1, o2, o3, -⟩ :=
                pikeAdd_build re s mo lim hwf true (pos + 1) (th.pc + 1) th.h
                  hadd hnext hokc
              exact hstep stA o1 o2 (o3 rfl) h
          · split at h
            · cases h
            · rename_i stA hdr
              obtain ⟨o1, o2, o3⟩ :=
                hdrop _ _ _ hokc (Nat.le_refl _) rfl hdr
              exact hstep stA o1 o2 o3 h
        case accept =>
          split at h
          · split at h
            · cases h
            · rename_i stA hdr
              obtain ⟨o1, o2, o3⟩ := hdrop _ _ _ hokc (Nat.le_refl _) rfl hdr
              exact hstep stA o1 o2 o3 h
          · split at h
            · cases h
            · rename_i stW hv hw
              obtain ⟨hstkW, hseenW⟩ := pikeWrite_ok hw
              obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hw
              have hokW : BuildOk re stW :=
                ⟨by rw [hseenW]; exact hok.seenSize,
                  by rw [hstkW]; exact hok.stk, by rw [hclW]; exact hok.clist,
                  by rw [hnlW]; exact hok.nlist⟩
              have hmW : buildMeasure stW ≤ buildMeasure st := by
                simp only [buildMeasure]
                rw [hseenW, hclW, hnlW]
                exact Nat.le_refl _
              split at h
              · cases h
              · rename_i stD hdr
                obtain ⟨o1, o2, o3⟩ := hdrop _ _ _ hokW hmW hclW hdr
                split at h
                · cases h
                · rename_i stR hdrop2
                  injection h with h
                  subst h
                  obtain ⟨r1, r2, r3, r4⟩ := dropRest_build _ _ _ hdrop2
                  refine ⟨⟨by rw [r1]; exact o1.seenSize,
                    by rw [r2]; exact o1.stk, by rw [r3]; exact o1.clist,
                    by rw [r4]; exact o1.nlist⟩, ?_, r3.trans o3⟩
                  simp only [buildMeasure] at o2 ⊢
                  rw [r1, r3, r4]
                  exact o2
        case bsr | split | jump | save | circ | circM | doll | dollE | dollM
            | sod | eod | eodn | wordB | notWordB | repZero | repLoop
            | repEnter | repNext =>
          all_goals
            split at h
            · cases h
            · rename_i stA hdr
              obtain ⟨o1, o2, o3⟩ := hdrop _ _ _ hokc (Nat.le_refl _) rfl hdr
              exact hstep stA o1 o2 o3 h

/-! ### The bound as a loop invariant -/

/-- What a position loop iteration starts from: a visited set sized to the
program, no pc outside it, the next list still empty, and the current list
already paid for by the marks that put it there. -/
structure LoopOk (re : Re) (st : PikeSt) : Prop where
  build : BuildOk re st
  empty : st.nlist.size = 0
  bounded : st.clist.size + unmarked st.seen ≤ re.code.size

/-- Neither thread list ever outgrows the program. -/
theorem LoopOk.clist_le {re : Re} {st : PikeSt} (h : LoopOk re st) :
    st.clist.size ≤ re.code.size := by
  have := h.bounded
  omega

/-- `LoopOk` is inductive: an iteration either blows the budget — and the
loop stops there — or hands the next one a state of the same shape. The
seeding build spends its marks in the current list, the clear hands the step
a full budget of marks, and the swap turns the next list into the current
one with the marks that paid for it still counted. -/
theorem pikeLoop_lists (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) (anchored : Bool) (words : Nat) (hwf : ReWf re) :
    ∀ (steps pos : Nat) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      LoopOk re st →
      LoopOk re (pikeLoop re s mo lim start anchored words steps pos st mh
          seeding matched).1 ∨
        (pikeLoop re s mo lim start anchored words steps pos st mh seeding
          matched).2.2 = .exceeded := by
  intro steps
  induction steps with
  | zero =>
      intro pos st mh seeding matched _
      rw [pikeLoop]
      exact Or.inr rfl
  | succ k ih =>
      intro pos st mh seeding matched hok
      have hseeded : ∀ stS : PikeSt,
          (if seeding && (!anchored || pos == start) then
            pikeSeed re s mo lim start pos st
            else (Except.ok st : POut PikeSt)) = .ok stS →
          BuildOk re stS ∧
            stS.clist.size + stS.nlist.size + unmarked stS.seen ≤ re.code.size ∧
            stS.nlist.size = 0 := by
        intro stS hs
        have hbd := hok.bounded
        have hem := hok.empty
        split at hs
        · obtain ⟨h1, h2, h3⟩ :=
            pikeSeed_build re s mo lim hwf start pos hs hok.build
          simp only [buildMeasure] at h2
          have h3' := congrArg Array.size h3
          exact ⟨h1, by omega, by omega⟩
        · injection hs with hs
          subst hs
          exact ⟨hok.build, by omega, hem⟩
      simp only [pikeLoop]
      split
      · exact Or.inr rfl
      · rename_i stS hs
        obtain ⟨hb, hbd, hemp⟩ := hseeded stS hs
        split
        · exact Or.inr rfl
        · have hokc : BuildOk re { stS with
              m := { stS.m with cost := stS.m.cost + words }
              seen := Array.replicate re.code.size false } :=
            ⟨by simp, hb.stk, hb.clist, hb.nlist⟩
          have hfull : unmarked (Array.replicate re.code.size false) ≤
              re.code.size := by
            have := unmarked_le_size (Array.replicate re.code.size false)
            simpa using this
          split
          · exact Or.inr rfl
          · rename_i out hx
            obtain ⟨o1, o2, o3⟩ := stepThreads_build re s mo lim hwf start pos
              _ _ mh seeding matched out hx hb.clist hokc
            have hrec : buildMeasure { stS with
                m := { stS.m with cost := stS.m.cost + words }
                seen := Array.replicate re.code.size false } =
                stS.clist.size + stS.nlist.size +
                  unmarked (Array.replicate re.code.size false) := rfl
            rw [hrec] at o2
            simp only [buildMeasure] at o2
            have o3' : out.st.clist.size = stS.clist.size := by rw [o3]
            have hfin : LoopOk re { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } := by
              refine ⟨⟨o1.seenSize, o1.stk, o1.nlist, ?_⟩, rfl, ?_⟩
              · intro y hy
                simp at hy
              · simp only []
                omega
            split
            · exact Or.inl hfin
            · split
              · exact Or.inl hfin
              · exact ih _ _ _ _ _ hfin

/-- A run enters the loop inside the invariant: it clears both lists and
sizes the visited set to the program, so the first position starts with
nothing parked and every mark still to spend. Composed with
`pikeLoop_lists`, that is the dedup half of BOUNDS.md section 9's
per-position count — neither thread list ever holds more than `C` entries. -/
theorem pikeRun_loopOk (re : Re) (init : PikeSt) (setup : Nat) :
    LoopOk re { init with
      clist := #[], nlist := #[], stk := #[]
      pool := #[], rc := #[], free := #[]
      seen := Array.replicate re.code.size false
      m := ⟨setup, setup, setup⟩ } := by
  have hempty : ∀ a : Array Th, a = #[] → listInRange re a := by
    intro a ha y hy
    rw [ha] at hy
    simp at hy
  have hfull : unmarked (Array.replicate re.code.size false) ≤ re.code.size := by
    have := unmarked_le_size (Array.replicate re.code.size false)
    simpa using this
  refine ⟨⟨by simp, hempty _ rfl, hempty _ rfl, hempty _ rfl⟩, rfl, ?_⟩
  simp only [Array.size_empty]
  omega

/-! ## Who owns a capture block

BOUNDS.md section 9 sizes the block pool at `4*C + 2`, and the argument is
about ownership rather than about counting allocations: `pike_take` takes a
fresh block only when the free list is empty, so a block the run has
finished with comes back to be handed out again. What makes that close is
that nothing leaks — every block ever allocated is on the free list or held
by one of the handles someone is carrying, and its refcount says exactly how
many carry it.

That reading and its helper-by-helper algebra are what is below, and no
more. The list of handles is a parameter: which of them a state actually
reaches is the caller's business, since a closure build and a list step
reach different ones — during a step the current thread list is a snapshot
the step is consuming, and what it has consumed is gone. Naming those
handles as the two thread lists, the closure stack, the recorded match and
the seed in flight, and reading `4*C + 2` off the dedup bound, is the step
that is not here yet. -/

/-- How many of the handles below `n` a list holds, counted with
multiplicity. Adding the free list's tally to the live one's is what closes
the pool's size against them. -/
def countBelow (l : List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => countBelow l n + l.count n

theorem countBelow_nil : ∀ n, countBelow ([] : List Nat) n = 0
  | 0 => rfl
  | n + 1 => by rw [countBelow, countBelow_nil n]; rfl

theorem countBelow_cons {a : Nat} {l : List Nat} : ∀ n,
    countBelow (a :: l) n = countBelow l n + (if a < n then 1 else 0)
  | 0 => by simp [countBelow]
  | n + 1 => by
      have hc : (a :: l).count n = l.count n + (if a = n then 1 else 0) := by
        rw [List.count_cons]
        simp
      rw [countBelow, countBelow, countBelow_cons n, hc]
      split <;> split <;> split <;> omega

theorem countBelow_le {l : List Nat} (n : Nat) : countBelow l n ≤ l.length := by
  induction l with
  | nil => rw [countBelow_nil]; exact Nat.zero_le _
  | cons a l ih =>
      rw [countBelow_cons]
      simp only [List.length_cons]
      split <;> omega

/-- The last entry of a nonempty array, split off its list. -/
private theorem toList_pop_back {α : Type _} [Inhabited α] {a : Array α}
    (h : 0 < a.size) : a.toList = a.pop.toList ++ [a.back!] := by
  have hne : a.toList ≠ [] := by
    intro he
    have hz : a.toList.length = 0 := by rw [he]; rfl
    rw [Array.length_toList] at hz
    omega
  have hlast : a.toList.getLast hne = a.back! := by
    rw [Array.back!, getElem!_pos a (a.size - 1) (by omega),
      ← Array.getElem_toList, List.getLast_eq_getElem]
    simp
  rw [Array.toList_pop, ← hlast, List.dropLast_concat_getLast hne]

private theorem getBang_push_lt {α : Type _} [Inhabited α] (a : Array α) (v : α)
    {x : Nat} (h : x < a.size) : (a.push v)[x]! = a[x]! := by
  rw [getElem!_pos (a.push v) x (by simp; omega), getElem!_pos a x h]
  exact Array.getElem_push_lt h

private theorem getBang_push_eq {α : Type _} [Inhabited α] (a : Array α)
    (v : α) : (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by simp)]
  simp

private theorem foldl_size {α : Type _} (f : Array α → Nat → Array α)
    (hf : ∀ a k, (f a k).size = a.size) : ∀ (l : List Nat) (p : Array α),
    (l.foldl f p).size = p.size := by
  intro l
  induction l with
  | nil => intro p; rfl
  | cons a l ih =>
      intro p
      rw [List.foldl_cons, ih, hf]

private theorem count_cons_self {a : Nat} {l : List Nat} :
    (a :: l).count a = l.count a + 1 := by
  rw [List.count_cons]
  simp

private theorem count_cons_ne {a b : Nat} {l : List Nat} (hne : b ≠ a) :
    (b :: l).count a = l.count a := by
  rw [List.count_cons, if_neg (by simp [hne])]
  omega

private theorem count_singleton {a b : Nat} :
    List.count a [b] = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · rw [hab]
    simp
  · rw [if_neg hab]
    exact List.count_eq_zero.mpr (by simp [hab])

/-- The pool read as ownership, against the handles `live` names: every
block ever allocated is on the free list or held, its refcount is exactly
how many holders it has, and the free list carries no block twice and none
that anyone still holds. The pool travels with them for its layout alone:
one block of `novec` slots per refcount entry, which is what says a handle
someone holds names a block the pool has room for. The arrays travel on
their own because that is all of a state the reading looks at. -/
structure Owned (novec : Nat) (rc free : Array Nat) (pool : Array UInt32)
    (live : List Nat) : Prop where
  capped : rc.size ≤ maxBlocks
  reach : ∀ h ∈ live, h < rc.size
  count : ∀ h, h < rc.size → rc[h]! = live.count h
  onFree : ∀ h, h < rc.size → (rc[h]! = 0 ↔ 0 < free.toList.count h)
  freeRange : ∀ h ∈ free.toList, h < rc.size
  freeOnce : ∀ h, free.toList.count h ≤ 1
  blocks : pool.size = rc.size * novec

/-- Which order the caller lists its handles in is not the pool's business. -/
theorem Owned.perm {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {l₁ l₂ : List Nat} (h : Owned novec rc free pool l₁) (hp : l₂.Perm l₁) :
    Owned novec rc free pool l₂ where
  capped := h.capped
  reach := fun x hx => h.reach x (hp.mem_iff.mp hx)
  count := fun x hx => by rw [h.count x hx, hp.count_eq]
  onFree := h.onFree
  freeRange := h.freeRange
  freeOnce := h.freeOnce
  blocks := h.blocks

/-- Nor is which slots the pool holds, as long as it holds as many. -/
theorem Owned.ofPool {novec : Nat} {rc free : Array Nat}
    {pool pool' : Array UInt32} {live : List Nat}
    (h : Owned novec rc free pool live) (hsize : pool'.size = pool.size) :
    Owned novec rc free pool' live :=
  { h with blocks := by rw [hsize]; exact h.blocks }

/-- What the pool has room for: a handle anyone holds names a block whose
slots all sit inside the pool. That is the layout read against the handles
in reach, and it is what a decoder needs before it may read a block out. -/
theorem Owned.blockFits {novec : Nat} {rc free : Array Nat}
    {pool : Array UInt32} {live : List Nat} (h : Owned novec rc free pool live)
    {x : Nat} (hx : x ∈ live) : (x + 1) * novec ≤ pool.size := by
  rw [h.blocks]
  exact Nat.mul_le_mul_right novec (h.reach x hx)

/-- The payoff: a block is on the free list or someone holds it, so there
are no more blocks than the free list and the live handles together have
room for. -/
theorem Owned.size_le {novec : Nat} {rc free : Array Nat}
    {pool : Array UInt32} {live : List Nat}
    (h : Owned novec rc free pool live) :
    rc.size ≤ free.size + live.length := by
  have key : ∀ n, n ≤ rc.size →
      n ≤ countBelow free.toList n + countBelow live n := by
    intro n
    induction n with
    | zero => intro _; simp [countBelow]
    | succ k ih =>
        intro hk
        have hk' : k < rc.size := by omega
        have hstep : 1 ≤ free.toList.count k + live.count k := by
          rcases Nat.eq_zero_or_pos (live.count k) with hz | hp
          · have hzero : rc[k]! = 0 := by rw [h.count k hk']; exact hz
            have := (h.onFree k hk').mp hzero
            omega
          · omega
        have hrec := ih (by omega)
        simp only [countBelow]
        omega
  have h1 := key rc.size (Nat.le_refl _)
  have h2 : countBelow free.toList rc.size ≤ free.toList.length := countBelow_le _
  have h3 : countBelow live rc.size ≤ live.length := countBelow_le _
  rw [Array.length_toList] at h2
  omega

/-! ### What each helper does to the ownership -/

/-- One reference let go of a block someone else still holds: the count
falls by one and nothing joins the free list, because a block with a holder
left is not free. -/
theorem owned_release {novec : Nat} {rc free : Array Nat}
    {pool : Array UInt32} {h : Nat} {rest : List Nat}
    (how : Owned novec rc free pool (h :: rest)) (hpos : 0 < rest.count h) :
    Owned novec (rc.set! h (rc[h]! - 1)) free pool rest := by
  have hlt : h < rc.size := how.reach h List.mem_cons_self
  have hch : rc[h]! = rest.count h + 1 := by
    rw [how.count h hlt, count_cons_self]
  have hfree : free.toList.count h = 0 := by
    have := how.onFree h hlt
    omega
  have hsize : (rc.set! h (rc[h]! - 1)).size = rc.size := Array.size_set! _ _ _
  have hset : ∀ x, x < rc.size → (rc.set! h (rc[h]! - 1))[x]! = rest.count x := by
    intro x hx
    by_cases hxh : x = h
    · rw [hxh, Array.getElem!_set!_self _ _ _ hlt]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hxh he.symm),
        how.count x hx, count_cons_ne (fun he => hxh he.symm)]
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, how.freeOnce,
    by rw [hsize]; exact how.blocks⟩
  · intro x hx
    rw [hsize]
    exact how.reach x (List.mem_cons_of_mem _ hx)
  · intro x hx
    rw [hsize] at hx
    exact hset x hx
  · intro x hx
    rw [hsize] at hx
    rw [hset x hx]
    by_cases hxh : x = h
    · rw [hxh, hfree]
      omega
    · have hc := how.count x hx
      rw [count_cons_ne (fun he => hxh he.symm)] at hc
      rw [← hc]
      exact how.onFree x hx
  · intro x hx
    rw [hsize]
    exact how.freeRange x hx

/-- The last holder let go, so the block joins the free list — where
nothing else can be holding it, which is what keeps the free list clean. -/
theorem owned_free {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {h : Nat} {rest : List Nat}
    (how : Owned novec rc free pool (h :: rest)) (hz : rest.count h = 0) :
    Owned novec (rc.set! h (rc[h]! - 1)) (free.push h) pool rest := by
  have hlt : h < rc.size := how.reach h List.mem_cons_self
  have hch : rc[h]! = rest.count h + 1 := by
    rw [how.count h hlt, count_cons_self]
  have hfree : free.toList.count h = 0 := by
    have := how.onFree h hlt
    omega
  have hsize : (rc.set! h (rc[h]! - 1)).size = rc.size := Array.size_set! _ _ _
  have hset : ∀ x, x < rc.size → (rc.set! h (rc[h]! - 1))[x]! = rest.count x := by
    intro x hx
    by_cases hxh : x = h
    · rw [hxh, Array.getElem!_set!_self _ _ _ hlt]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hxh he.symm),
        how.count x hx, count_cons_ne (fun he => hxh he.symm)]
  have hpush : ∀ x, (free.push h).toList.count x =
      free.toList.count x + (if x = h then 1 else 0) := by
    intro x
    rw [Array.toList_push, List.count_append, count_singleton]
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, ?_,
    by rw [hsize]; exact how.blocks⟩
  · intro x hx
    rw [hsize]
    exact how.reach x (List.mem_cons_of_mem _ hx)
  · intro x hx
    rw [hsize] at hx
    exact hset x hx
  · intro x hx
    rw [hsize] at hx
    rw [hset x hx, hpush]
    by_cases hxh : x = h
    · rw [hxh, if_pos rfl, hz, hfree]
      simp
    · rw [if_neg hxh]
      have hc := how.count x hx
      rw [count_cons_ne (fun he => hxh he.symm)] at hc
      rw [← hc]
      exact how.onFree x hx
  · intro x hx
    rw [hsize]
    rw [Array.toList_push] at hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact how.freeRange x hx'
    · simp only [List.mem_singleton] at hx'
      subst hx'
      exact hlt
  · intro x
    rw [hpush]
    have hone := how.freeOnce x
    split
    · rename_i he
      rw [he, hfree]
      omega
    · omega

/-- And one reference more, which is what a fork hands out: the block now
has two holders where it had one. -/
theorem owned_share {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {h : Nat} {rest : List Nat} (how : Owned novec rc free pool (h :: rest)) :
    Owned novec (rc.set! h (rc[h]! + 1)) free pool (h :: h :: rest) := by
  have hlt : h < rc.size := how.reach h List.mem_cons_self
  have hch : rc[h]! = rest.count h + 1 := by
    rw [how.count h hlt, count_cons_self]
  have hfree : free.toList.count h = 0 := by
    have := how.onFree h hlt
    omega
  have hsize : (rc.set! h (rc[h]! + 1)).size = rc.size := Array.size_set! _ _ _
  have hset : ∀ x, x < rc.size →
      (rc.set! h (rc[h]! + 1))[x]! = (h :: h :: rest).count x := by
    intro x hx
    by_cases hxh : x = h
    · rw [hxh, Array.getElem!_set!_self _ _ _ hlt]
      rw [hxh] at hx
      rw [count_cons_self, count_cons_self]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hxh he.symm),
        how.count x hx, count_cons_ne (fun he => hxh he.symm),
        count_cons_ne (fun he => hxh he.symm),
        count_cons_ne (fun he => hxh he.symm)]
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, how.freeOnce,
    by rw [hsize]; exact how.blocks⟩
  · intro x hx
    rw [hsize]
    rcases List.mem_cons.mp hx with he | hx'
    · subst he; exact hlt
    · exact how.reach x hx'
  · intro x hx
    rw [hsize] at hx
    exact hset x hx
  · intro x hx
    rw [hsize] at hx
    rw [hset x hx]
    by_cases hxh : x = h
    · rw [hxh, count_cons_self, count_cons_self, hfree]
      omega
    · rw [count_cons_ne (fun he => hxh he.symm),
        count_cons_ne (fun he => hxh he.symm)]
      have hc := how.count x hx
      rw [count_cons_ne (fun he => hxh he.symm)] at hc
      rw [← hc]
      exact how.onFree x hx
  · intro x hx
    rw [hsize]
    exact how.freeRange x hx

/-- A block off the free list. Its refcount was zero and nobody held it, so
handing it out makes the caller its only holder. -/
theorem owned_reuse {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {live : List Nat} (how : Owned novec rc free pool live)
    (hpos : 0 < free.size) :
    Owned novec (rc.set! free.back! 1) free.pop pool
      (free.back! :: live) := by
  have hsplit := toList_pop_back (a := free) hpos
  have hcount : ∀ x, free.toList.count x =
      free.pop.toList.count x + (if x = free.back! then 1 else 0) := by
    intro x
    rw [hsplit, List.count_append, count_singleton]
  have hmem : free.back! ∈ free.toList := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hlt : free.back! < rc.size := how.freeRange _ hmem
  have hzero : rc[free.back!]! = 0 := by
    refine (how.onFree _ hlt).mpr ?_
    exact List.count_pos_iff.mpr hmem
  have hlive : live.count free.back! = 0 := by
    have := how.count _ hlt
    omega
  have hpopz : free.pop.toList.count free.back! = 0 := by
    have h1 := hcount free.back!
    have h2 := how.freeOnce free.back!
    have h3 : 0 < free.toList.count free.back! := List.count_pos_iff.mpr hmem
    rw [if_pos rfl] at h1
    omega
  have hsize : (rc.set! free.back! 1).size = rc.size := Array.size_set! _ _ _
  have hset : ∀ x, x < rc.size →
      (rc.set! free.back! 1)[x]! = (free.back! :: live).count x := by
    intro x hx
    by_cases hxh : x = free.back!
    · rw [hxh, Array.getElem!_set!_self _ _ _ hlt, count_cons_self, hlive]
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hxh he.symm),
        how.count x hx, count_cons_ne (fun he => hxh he.symm)]
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, ?_,
    by rw [hsize]; exact how.blocks⟩
  · intro x hx
    rw [hsize]
    rcases List.mem_cons.mp hx with he | hx'
    · subst he; exact hlt
    · exact how.reach x hx'
  · intro x hx
    rw [hsize] at hx
    exact hset x hx
  · intro x hx
    rw [hsize] at hx
    rw [hset x hx]
    by_cases hxh : x = free.back!
    · rw [hxh, count_cons_self, hlive, hpopz]
      omega
    · rw [count_cons_ne (fun he => hxh he.symm)]
      have hf := how.onFree x hx
      rw [how.count x hx, hcount x, if_neg hxh] at hf
      simpa using hf
  · intro x hx
    rw [hsize]
    refine how.freeRange x ?_
    rw [hsplit]
    exact List.mem_append_left _ hx
  · intro x
    have h1 := how.freeOnce x
    have h2 := hcount x
    omega

/-- A fresh block, taken because the free list had nothing on it. Its handle
is the first index the refcount table did not have, so nobody could have
been holding it. -/
theorem owned_fresh {novec : Nat} {rc free : Array Nat}
    {pool pool' : Array UInt32} {live : List Nat}
    (how : Owned novec rc free pool live) (hnil : free.size = 0)
    (hcap : rc.size < maxBlocks) (hfill : pool'.size = pool.size + novec) :
    Owned novec (rc.push 1) free pool' (rc.size :: live) := by
  have hlist : free.toList = [] := by
    have : free.toList.length = 0 := by rw [Array.length_toList, hnil]
    exact List.eq_nil_of_length_eq_zero this
  have hsz : (rc.push 1).size = rc.size + 1 := by simp
  have hnew : ∀ x, x < rc.size + 1 → (rc.push 1)[x]! = (rc.size :: live).count x := by
    intro x hx
    by_cases hxs : x = rc.size
    · have hz : live.count rc.size = 0 := by
        rcases Nat.eq_zero_or_pos (live.count rc.size) with hz | hp
        · exact hz
        · exact absurd (how.reach _ (List.count_pos_iff.mp hp)) (by omega)
      rw [hxs, getBang_push_eq, count_cons_self, hz]
    · rw [getBang_push_lt _ _ (by omega), how.count x (by omega),
        count_cons_ne (fun he => hxs he.symm)]
  refine ⟨by rw [hsz]; omega, ?_, ?_, ?_, ?_, ?_,
    by rw [hfill, how.blocks, hsz, Nat.succ_mul]⟩
  · intro x hx
    rw [hsz]
    rcases List.mem_cons.mp hx with he | hx'
    · subst he; omega
    · have := how.reach x hx'; omega
  · intro x hx
    rw [hsz] at hx
    exact hnew x hx
  · intro x hx
    rw [hsz] at hx
    rw [hnew x hx, hlist]
    simp only [List.count_nil, Nat.lt_irrefl, iff_false]
    by_cases hxs : x = rc.size
    · rw [hxs, count_cons_self]
      omega
    · rw [count_cons_ne (fun he => hxs he.symm)]
      have hc := how.count x (by omega)
      have hf := how.onFree x (by omega)
      rw [hlist] at hf
      simp only [List.count_nil, Nat.lt_irrefl, iff_false] at hf
      omega
  · intro x hx
    rw [hlist] at hx
    simp at hx
  · intro x
    rw [hlist]
    simp

theorem pikeDefer_pool {st st' : PikeSt} {pc h : Nat} {lim : Limits}
    (hok : pikeDefer st pc h lim = .ok st') :
    st'.rc = st.rc ∧ st'.free = st.free ∧ st'.pool = st.pool := by
  unfold pikeDefer at hok
  split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl, rfl⟩

theorem pikePark_pool {st st' : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} (hok : pikePark st intoNext pc h lim = .ok st') :
    st'.rc = st.rc ∧ st'.free = st.free ∧ st'.pool = st.pool := by
  unfold pikePark at hok
  split at hok <;> split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl, rfl⟩
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl, rfl⟩

theorem pikeTake_fill_pool {lim : Limits} : ∀ {k : Nat} {st st' : PikeSt},
    pikeTake.fill lim k st = .ok st' →
    st'.rc = st.rc ∧ st'.free = st.free ∧
      st'.pool.size = st.pool.size + k := by
  intro k
  induction k with
  | zero =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      injection hok with hok
      subst hok
      exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      split at hok
      · simp at hok
      · obtain ⟨h1, h2, h3⟩ := ih hok
        refine ⟨h1, h2, ?_⟩
        simp only [Array.size_push] at h3
        omega

/-! ### The helpers, read against the state -/

/-- Letting a handle go. The block returns to the free list exactly when its
last holder let it go. -/
theorem pikeDrop_owned {novec : Nat} {st st' : PikeSt} {h : Nat}
    {rest : List Nat} {lim : Limits} (hok : pikeDrop st h lim = .ok st')
    (how : Owned novec st.rc st.free st.pool (h :: rest)) :
    Owned novec st'.rc st'.free st'.pool rest := by
  have hlt : h < st.rc.size := how.reach h List.mem_cons_self
  have hne : ¬ ((h == none32) = true) := by
    have hb := how.capped
    simp only [maxBlocks, liveBlocks, maxCode, maxNodes, growMin,
      growFactor] at hb
    simp only [beq_iff_eq, none32]
    omega
  unfold pikeDrop at hok
  simp only [] at hok
  split at hok
  · rename_i hn
    exact absurd hn hne
  · split at hok
    · rename_i hzero
      have hz : rest.count h = 0 := by
        have hch : st.rc[h]! = rest.count h + 1 := by
          rw [how.count h hlt, count_cons_self]
        simp only [beq_iff_eq] at hzero
        omega
      split at hok
      · simp at hok
      · rename_i mm cap hg
        injection hok with hok
        subst hok
        exact owned_free how hz
    · rename_i hzero
      have hpos : 0 < rest.count h := by
        have hch : st.rc[h]! = rest.count h + 1 := by
          rw [how.count h hlt, count_cons_self]
        simp only [beq_iff_eq] at hzero
        omega
      injection hok with hok
      subst hok
      exact owned_release how hpos

/-- The sentinel drop, which is the one a step makes before it has a match
to let go of. Nothing moves, so the reading carries over untouched — and it
has to be a lemma of its own, because the sentinel is no block and the
handle list `Owned` is stated against never holds it. -/
theorem pikeDrop_none_owned {novec : Nat} {st st' : PikeSt} {live : List Nat}
    {lim : Limits} (hok : pikeDrop st none32 lim = .ok st')
    (how : Owned novec st.rc st.free st.pool live) :
    Owned novec st'.rc st'.free st'.pool live := by
  unfold pikeDrop at hok
  rw [if_pos (by simp)] at hok
  injection hok with hok
  subst hok
  exact how

/-- Taking a block, either way, leaves the caller holding it — and the
refcount table only ever gets longer when the free list had nothing on it.
That second half is where the pool's bound will come from: at the one moment
the table can grow, every block in it is one of the caller's handles, so the
handle count is what limits it. -/
theorem pikeTake_owned {st st' : PikeSt} {novec hOut : Nat} {live : List Nat}
    {lim : Limits} (hok : pikeTake st novec lim = .ok (st', hOut))
    (how : Owned novec st.rc st.free st.pool live) :
    Owned novec st'.rc st'.free st'.pool (hOut :: live) ∧
      st'.rc.size ≤ max st.rc.size (live.length + 1) := by
  unfold pikeTake at hok
  simp only [] at hok
  split at hok
  · rename_i hne
    have hpos : 0 < st.free.size := by
      rcases Nat.eq_zero_or_pos st.free.size with hz | hp
      · exact absurd hne (by simp [hz])
      · exact hp
    injection hok with hok
    injection hok with hok hh
    subst hok
    subst hh
    exact ⟨owned_reuse how hpos, by simp; omega⟩
  · rename_i hempty
    have hzero : st.free.size = 0 := by
      rcases Nat.eq_zero_or_pos st.free.size with hz | hp
      · exact hz
      · exact absurd (by simpa using hp) hempty
    split at hok
    · simp at hok
    · rename_i hcap
      split at hok
      · simp at hok
      · rename_i mm cap hg
        split at hok
        · simp at hok
        · rename_i stF hfill
          injection hok with hok
          injection hok with hok hh
          subst hok
          subst hh
          obtain ⟨hrcF, hfreeF, hpoolF⟩ := pikeTake_fill_pool hfill
          have hcount := how.size_le
          rw [hzero] at hcount
          refine ⟨by rw [hrcF, hfreeF]
                     exact owned_fresh how hzero (by omega) hpoolF, ?_⟩
          rw [hrcF]
          simp only [Array.size_push]
          omega

/-- A copy-on-write hands the caller a fresh block and lets go of the shared
one, which someone else still holds — that is why the write had to copy. -/
theorem pikeWrite_owned {st st' : PikeSt} {novec h slot hOut : Nat}
    {value : UInt32} {rest : List Nat} {lim : Limits}
    (hok : pikeWrite st novec h slot value lim = .ok (st', hOut))
    (how : Owned novec st.rc st.free st.pool (h :: rest)) :
    Owned novec st'.rc st'.free st'.pool (hOut :: rest) ∧
      st'.rc.size ≤ max st.rc.size (rest.length + 2) := by
  have hlt : h < st.rc.size := how.reach h List.mem_cons_self
  unfold pikeWrite at hok
  simp only [] at hok
  split at hok
  · rename_i hshared
    have hpos : 0 < rest.count h := by
      have hc := how.count h hlt
      rw [count_cons_self] at hc
      omega
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i hTake
        injection hok with hok
        injection hok with hok hh
        subst hok
        subst hh
        obtain ⟨htake, hsize⟩ := pikeTake_owned hTake how
        refine ⟨Owned.ofPool (owned_release (htake.perm (List.Perm.swap _ _ _))
          (by rw [List.count_cons]; split <;> omega)) ?_, ?_⟩
        · rw [Array.size_set!]
          exact foldl_size _ (fun a k => Array.size_set! _ _ _) _ _
        · simp only [Array.size_set!]
          simpa using hsize
  · injection hok with hok
    injection hok with hok hh
    subst hok
    subst hh
    exact ⟨Owned.ofPool how (by rw [Array.size_set!]), Nat.le_max_left _ _⟩

/-! ### What a closure build reaches

A build's own handles are on its worklist and in the list it is parking
into; the rest of what it holds is its caller's. The list it is *not*
writing stays out of the reckoning on purpose: during a list step the
current list is a snapshot the step is consuming, and an entry it has
consumed is not held any more. -/

/-- The handles a thread array carries. -/
def handles (a : Array Th) : List Nat := a.toList.map Th.h

theorem handles_length (a : Array Th) : (handles a).length = a.size := by
  simp [handles]

theorem handles_push (a : Array Th) (pc hh : Nat) :
    handles (a.push ⟨pc, hh⟩) = handles a ++ [hh] := by
  simp [handles]

theorem handles_pop_back {a : Array Th} (h : 0 < a.size) :
    handles a = handles a.pop ++ [a.back!.h] := by
  rw [handles, handles, toList_pop_back h]
  simp

/-- The thread list a build parks into. -/
def parkList (intoNext : Bool) (st : PikeSt) : Array Th :=
  if intoNext then st.nlist else st.clist

theorem parkList_eq {intoNext : Bool} {stA stB : PikeSt}
    (hc : stB.clist = stA.clist) (hn : stB.nlist = stA.nlist) :
    parkList intoNext stB = parkList intoNext stA := by
  unfold parkList
  split <;> simp [hc, hn]

theorem parkList_push {intoNext : Bool} {stA stB : PikeSt} {pc hh : Nat}
    (hT : intoNext = true →
      stB.clist = stA.clist ∧ stB.nlist = stA.nlist.push ⟨pc, hh⟩)
    (hF : intoNext = false →
      stB.nlist = stA.nlist ∧ stB.clist = stA.clist.push ⟨pc, hh⟩) :
    parkList intoNext stB = (parkList intoNext stA).push ⟨pc, hh⟩ := by
  unfold parkList
  by_cases hin : intoNext = true
  · rw [if_pos hin, if_pos hin, (hT hin).2]
  · have hin' : intoNext = false := by simpa using hin
    rw [if_neg hin, if_neg hin, (hF hin').2]

/-- What a build and its caller hold between them. -/
def buildLive (intoNext : Bool) (st : PikeSt) (ext : List Nat) : List Nat :=
  handles st.stk ++ handles (parkList intoNext st) ++ ext

/-- What a build has left to spend: what is on the worklist, what it has
parked, and twice the marks it has not made — a mark buys at most two
deferrals. No iteration raises it, and it is what bounds the handles in
reach. -/
def addMeasure (intoNext : Bool) (st : PikeSt) : Nat :=
  st.stk.size + (parkList intoNext st).size + 2 * unmarked st.seen

theorem buildLive_length (intoNext : Bool) (st : PikeSt) (ext : List Nat) :
    (buildLive intoNext st ext).length ≤
      addMeasure intoNext st + ext.length := by
  simp only [buildLive, addMeasure, List.length_append, handles_length]
  omega

/-! ### The handle in flight -/

private theorem perm_head (A B C : List Nat) (x : Nat) :
    (A ++ [x] ++ B ++ C).Perm (x :: (A ++ B ++ C)) := by
  have h1 : A ++ [x] ++ B ++ C = A ++ x :: (B ++ C) := by simp
  have h2 : x :: (A ++ B ++ C) = x :: (A ++ (B ++ C)) := by simp
  rw [h1, h2]
  exact List.perm_middle

private theorem perm_mid (A B C : List Nat) (x : Nat) :
    ((A ++ (B ++ [x])) ++ C).Perm (x :: (A ++ B ++ C)) := by
  have h1 : (A ++ (B ++ [x])) ++ C = (A ++ B) ++ x :: C := by simp
  have h2 : x :: (A ++ B ++ C) = x :: ((A ++ B) ++ C) := by simp
  rw [h1, h2]
  exact List.perm_middle

/-- Popping the worklist takes its top handle into flight. -/
theorem owned_pop {novec : Nat} {intoNext : Bool} {ext : List Nat}
    {st : PikeSt} (hne : 0 < st.stk.size)
    (how : Owned novec st.rc st.free st.pool (buildLive intoNext st ext)) :
    Owned novec st.rc st.free st.pool
      (st.stk.back!.h ::
        (handles st.stk.pop ++ handles (parkList intoNext st) ++ ext)) := by
  refine how.perm ?_
  simp only [buildLive]
  rw [handles_pop_back hne]
  exact (perm_head _ _ _ _).symm

/-- A deferral lands the handle on the worklist. -/
theorem defer_owned {novec : Nat} {intoNext : Bool} {ext : List Nat}
    {stA stB : PikeSt} {pc hh : Nat} {lim : Limits}
    (hok : pikeDefer stA pc hh lim = .ok stB)
    (how : Owned novec stA.rc stA.free stA.pool
      (hh :: buildLive intoNext stA ext)) :
    Owned novec stB.rc stB.free stB.pool (buildLive intoNext stB ext) := by
  obtain ⟨hstk, -⟩ := pikeDefer_ok hok
  obtain ⟨hcl, hnl⟩ := pikeDefer_lists hok
  obtain ⟨hrc, hfree, hpl⟩ := pikeDefer_pool hok
  rw [hrc, hfree, hpl]
  refine how.perm ?_
  simp only [buildLive, hstk, handles_push, parkList_eq hcl hnl]
  exact perm_head _ _ _ _

/-- The second of a fork's two deferrals, with the first still in flight. -/
theorem defer_owned_two {novec : Nat} {intoNext : Bool} {ext : List Nat}
    {stA stB : PikeSt} {pc hh : Nat} {lim : Limits}
    (hok : pikeDefer stA pc hh lim = .ok stB)
    (how : Owned novec stA.rc stA.free stA.pool
      (hh :: hh :: buildLive intoNext stA ext)) :
    Owned novec stB.rc stB.free stB.pool
      (hh :: buildLive intoNext stB ext) := by
  obtain ⟨hstk, -⟩ := pikeDefer_ok hok
  obtain ⟨hcl, hnl⟩ := pikeDefer_lists hok
  obtain ⟨hrc, hfree, hpl⟩ := pikeDefer_pool hok
  rw [hrc, hfree, hpl]
  refine how.perm ?_
  simp only [buildLive, hstk, handles_push, parkList_eq hcl hnl]
  exact (perm_head _ _ _ _).cons hh

/-- A park lands it on the list the build is writing. -/
theorem park_owned {novec : Nat} {intoNext : Bool} {ext : List Nat}
    {stA stB : PikeSt} {pc hh : Nat} {lim : Limits}
    (hok : pikePark stA intoNext pc hh lim = .ok stB)
    (how : Owned novec stA.rc stA.free stA.pool
      (hh :: buildLive intoNext stA ext)) :
    Owned novec stB.rc stB.free stB.pool (buildLive intoNext stB ext) := by
  obtain ⟨hstk, -⟩ := pikePark_ok hok
  obtain ⟨hT, hF⟩ := pikePark_lists hok
  obtain ⟨hrc, hfree, hpl⟩ := pikePark_pool hok
  rw [hrc, hfree, hpl]
  refine how.perm ?_
  simp only [buildLive, hstk, parkList_push hT hF, handles_push]
  exact perm_mid _ _ _ _

/-- And a drop lets it go. -/
theorem drop_owned {novec : Nat} {intoNext : Bool} {ext : List Nat}
    {stA stB : PikeSt} {hh : Nat} {lim : Limits}
    (hok : pikeDrop stA hh lim = .ok stB)
    (how : Owned novec stA.rc stA.free stA.pool
      (hh :: buildLive intoNext stA ext)) :
    Owned novec stB.rc stB.free stB.pool (buildLive intoNext stB ext) := by
  obtain ⟨hstk, -⟩ := pikeDrop_ok hok
  obtain ⟨hcl, hnl⟩ := pikeDrop_lists hok
  have hres := pikeDrop_owned hok how
  rwa [buildLive, hstk, parkList_eq hcl hnl, ← buildLive]

/-- The Save's copy-on-write swaps the handle in flight for a private
block, and what it takes is bounded by the handles already in reach. -/
theorem write_owned {intoNext : Bool} {ext : List Nat} {stA stB : PikeSt}
    {novec hh slot hOut : Nat} {value : UInt32} {lim : Limits}
    (hok : pikeWrite stA novec hh slot value lim = .ok (stB, hOut))
    (how : Owned novec stA.rc stA.free stA.pool
      (hh :: buildLive intoNext stA ext)) :
    Owned novec stB.rc stB.free stB.pool
      (hOut :: buildLive intoNext stB ext) ∧
      stB.rc.size ≤
        max stA.rc.size ((buildLive intoNext stA ext).length + 2) := by
  obtain ⟨hstk, -⟩ := pikeWrite_ok hok
  obtain ⟨hcl, hnl⟩ := pikeWrite_lists hok
  obtain ⟨h1, h2⟩ := pikeWrite_owned hok how
  refine ⟨?_, h2⟩
  rwa [buildLive, hstk, parkList_eq hcl hnl, ← buildLive]

theorem pikeDrop_rcSize {st st' : PikeSt} {h : Nat} {lim : Limits}
    (hok : pikeDrop st h lim = .ok st') :
    st'.rc.size = st.rc.size ∧ st'.pool = st.pool := by
  unfold pikeDrop at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩
  · split at hok
    · split at hok
      · simp at hok
      · injection hok with hok
        subst hok
        exact ⟨by simp, rfl⟩
    · injection hok with hok
      subst hok
      exact ⟨by simp, rfl⟩

/-! ### The closure loop, read against the pool -/

set_option maxHeartbeats 1000000 in
/-- One closure build, weighed and owned. The measure never rises — an
iteration pops one entry, and a fresh pc pays two off the unvisited count
against at most two deferrals — and the pool's reading survives every arm,
since each of them either moves the popped handle somewhere the live list
can see it or lets it go. The one arm that allocates is the Save's
copy-on-write, and what it takes is bounded by the handles in reach.

None of this needs the pcs to be real instructions. A pc outside the
program reads as the default `chr`, which parks and pushes nothing, so the
arms that push are exactly the ones whose mark is known to land. -/
theorem pikeAdd_go_owned (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (intoNext : Bool) (pos : Nat) (ext : List Nat) :
    ∀ (fuel : Nat) (st st' : PikeSt),
      pikeAdd.go re s mo lim intoNext pos fuel st = .ok st' →
      st.seen.size = re.code.size →
      Owned re.novec st.rc st.free st.pool (buildLive intoNext st ext) →
      Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
        addMeasure intoNext st' ≤ addMeasure intoNext st ∧
        st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
        st'.rc.size ≤
          max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st st' h _ _
      rw [pikeAdd.go] at h
      cases h
  | succ f ih =>
      intro st st' h hsz how
      simp only [pikeAdd.go] at h
      -- Whatever an arm hands the loop is weighed against the state this
      -- iteration began with.
      have hstep : ∀ stB : PikeSt,
          pikeAdd.go re s mo lim intoNext pos f stB = .ok st' →
          stB.seen.size = re.code.size →
          Owned re.novec stB.rc stB.free stB.pool (buildLive intoNext stB ext) →
          addMeasure intoNext stB ≤ addMeasure intoNext st →
          stB.rc.size ≤
            max st.rc.size (addMeasure intoNext st + ext.length + 1) →
          Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
            addMeasure intoNext st' ≤ addMeasure intoNext st ∧
            st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
            st'.rc.size ≤
              max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
        intro stB hgo hszB howB hmB hrcB
        obtain ⟨o1, o2, o3, o4, o5⟩ := ih stB st' hgo hszB howB
        exact ⟨o1, Nat.le_trans o2 hmB, o3, o4, by omega⟩
      split at h
      · rename_i hemp
        injection h with h
        subst h
        refine ⟨how, Nat.le_refl _, hsz, ?_, by omega⟩
        simp only [beq_iff_eq] at hemp
        exact hemp
      · rename_i hne
        have hpos : 0 < st.stk.size :=
          Nat.pos_of_ne_zero (fun hz => hne (by simp [hz]))
        have hflight := owned_pop (intoNext := intoNext) (ext := ext) hpos how
        split at h
        · -- Already visited: the pop pays for the iteration.
          split at h
          · exact absurd h (by simp)
          · rename_i stD hdr
            obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
            obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
            have hstkD : stD.stk = st.stk.pop := by rw [hkD]
            have hseenD : stD.seen = st.seen := by rw [heD]
            have hpkD : parkList intoNext stD = parkList intoNext st := by
              rw [parkList_eq hclD hnlD]
              rfl
            refine hstep stD h (by rw [hseenD]; exact hsz) (drop_owned hdr hflight)
              ?_ ?_
            · simp only [addMeasure, hstkD, hseenD, hpkD, Array.size_pop]
              omega
            · rw [(pikeDrop_rcSize hdr).1]
              exact Nat.le_max_left _ _
        · -- A fresh pc: the mark pays for what the arm pushes.
          rename_i hseenF
          have hfalse : st.seen[st.stk.back!.pc]! = false := by simpa using hseenF
          have hweak := unmarked_set_le st.seen st.stk.back!.pc
          have hstrict : re.code[st.stk.back!.pc]!.op ≠ Op.chr →
              unmarked (st.seen.set! st.stk.back!.pc true) + 1 =
                unmarked st.seen := by
            intro hno
            rcases Nat.lt_or_ge st.stk.back!.pc re.code.size with hlt | hge
            · exact unmarked_set_lt (by omega) hfalse
            · exact absurd
                (by rw [getElem!_neg re.code st.stk.back!.pc (by omega)]; rfl :
                  re.code[st.stk.back!.pc]!.op = Op.chr) hno
          -- The five shapes an arm can take, each read off the marked state
          -- through the fields the reckoning looks at.
          have harmDrop : ∀ (stA stB : PikeSt),
              pikeDrop stA st.stk.back!.h lim = .ok stB →
              pikeAdd.go re s mo lim intoNext pos f stB = .ok st' →
              stA.stk = st.stk.pop →
              stA.seen = st.seen.set! st.stk.back!.pc true →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              parkList intoNext stA = parkList intoNext st →
              Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
                addMeasure intoNext st' ≤ addMeasure intoNext st ∧
                st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
                st'.rc.size ≤
                  max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
            intro stA stB hdr hgo hstkA hseenA hrcA hfreeA hpoolA hparkA
            have hstA : Owned re.novec stA.rc stA.free stA.pool
                (st.stk.back!.h :: buildLive intoNext stA ext) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
              exact hflight
            obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
            obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
            refine hstep stB hgo
              (by rw [heD, hseenA, Array.size_set!]; exact hsz)
              (drop_owned hdr hstA) ?_ ?_
            · simp only [addMeasure, hkD, heD, parkList_eq hclD hnlD, hparkA,
                hstkA, hseenA, Array.size_pop]
              omega
            · rw [(pikeDrop_rcSize hdr).1, hrcA]
              exact Nat.le_max_left _ _
          have harmPark : ∀ (stA stB : PikeSt) (pcT : Nat),
              pikePark stA intoNext pcT st.stk.back!.h lim = .ok stB →
              pikeAdd.go re s mo lim intoNext pos f stB = .ok st' →
              stA.stk = st.stk.pop →
              stA.seen = st.seen.set! st.stk.back!.pc true →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              parkList intoNext stA = parkList intoNext st →
              Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
                addMeasure intoNext st' ≤ addMeasure intoNext st ∧
                st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
                st'.rc.size ≤
                  max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
            intro stA stB pcT hpk hgo hstkA hseenA hrcA hfreeA hpoolA hparkA
            have hstA : Owned re.novec stA.rc stA.free stA.pool
                (st.stk.back!.h :: buildLive intoNext stA ext) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
              exact hflight
            obtain ⟨hkD, heD⟩ := pikePark_ok hpk
            obtain ⟨hT, hF⟩ := pikePark_lists hpk
            obtain ⟨hrcD, hfreeD, hplD⟩ := pikePark_pool hpk
            refine hstep stB hgo
              (by rw [heD, hseenA, Array.size_set!]; exact hsz)
              (park_owned hpk hstA) ?_ ?_
            · simp only [addMeasure, hkD, heD, parkList_push hT hF, hparkA,
                hstkA, hseenA, Array.size_push, Array.size_pop]
              omega
            · rw [hrcD, hrcA]
              exact Nat.le_max_left _ _
          have harmDefer : ∀ (stA stB : PikeSt) (pcT : Nat),
              pikeDefer stA pcT st.stk.back!.h lim = .ok stB →
              pikeAdd.go re s mo lim intoNext pos f stB = .ok st' →
              stA.stk = st.stk.pop →
              stA.seen = st.seen.set! st.stk.back!.pc true →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              parkList intoNext stA = parkList intoNext st →
              Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
                addMeasure intoNext st' ≤ addMeasure intoNext st ∧
                st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
                st'.rc.size ≤
                  max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
            intro stA stB pcT hdf hgo hstkA hseenA hrcA hfreeA hpoolA hparkA
            have hstA : Owned re.novec stA.rc stA.free stA.pool
                (st.stk.back!.h :: buildLive intoNext stA ext) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
              exact hflight
            obtain ⟨hkD, heD⟩ := pikeDefer_ok hdf
            obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdf
            obtain ⟨hrcD, hfreeD, hplD⟩ := pikeDefer_pool hdf
            refine hstep stB hgo
              (by rw [heD, hseenA, Array.size_set!]; exact hsz)
              (defer_owned hdf hstA) ?_ ?_
            · simp only [addMeasure, hkD, heD, parkList_eq hclD hnlD, hparkA,
                hstkA, hseenA, Array.size_push, Array.size_pop]
              omega
            · rw [hrcD, hrcA]
              exact Nat.le_max_left _ _
          have harmFork : ∀ (stR stB stC : PikeSt) (p q : Nat),
              pikeDefer stR p st.stk.back!.h lim = .ok stB →
              pikeDefer stB q st.stk.back!.h lim = .ok stC →
              pikeAdd.go re s mo lim intoNext pos f stC = .ok st' →
              stR.stk = st.stk.pop →
              stR.seen = st.seen.set! st.stk.back!.pc true →
              stR.rc = st.rc.set! st.stk.back!.h
                (st.rc[st.stk.back!.h]! + 1) →
              stR.free = st.free → stR.pool = st.pool →
              parkList intoNext stR = parkList intoNext st →
              unmarked (st.seen.set! st.stk.back!.pc true) + 1 =
                unmarked st.seen →
              Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
                addMeasure intoNext st' ≤ addMeasure intoNext st ∧
                st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
                st'.rc.size ≤
                  max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
            intro stR stB stC p q hd1 hd2 hgo hstkR hseenR hrcR hfreeR hpoolR
              hparkR hu
            have hstR : Owned re.novec stR.rc stR.free stR.pool
                (st.stk.back!.h :: st.stk.back!.h ::
                  buildLive intoNext stR ext) := by
              rw [hrcR, hfreeR, hpoolR, buildLive, hstkR, hparkR]
              exact owned_share hflight
            obtain ⟨hk1, he1⟩ := pikeDefer_ok hd1
            obtain ⟨hcl1, hnl1⟩ := pikeDefer_lists hd1
            obtain ⟨hrc1, hfree1, hpl1⟩ := pikeDefer_pool hd1
            obtain ⟨hk2, he2⟩ := pikeDefer_ok hd2
            obtain ⟨hcl2, hnl2⟩ := pikeDefer_lists hd2
            obtain ⟨hrc2, hfree2, hpl2⟩ := pikeDefer_pool hd2
            refine hstep stC hgo
              (by rw [he2, he1, hseenR, Array.size_set!]; exact hsz)
              (defer_owned hd2 (defer_owned_two hd1 hstR)) ?_ ?_
            · simp only [addMeasure, hk2, he2, hk1, he1,
                parkList_eq hcl2 hnl2, parkList_eq hcl1 hnl1, hparkR, hstkR,
                hseenR, Array.size_push, Array.size_pop]
              omega
            · rw [hrc2, hrc1, hrcR, Array.size_set!]
              exact Nat.le_max_left _ _
          have harmSave : ∀ (stA stW stB : PikeSt) (slotT hOut pcT : Nat)
              (value : UInt32),
              pikeWrite stA re.novec st.stk.back!.h slotT value lim
                = .ok (stW, hOut) →
              pikeDefer stW pcT hOut lim = .ok stB →
              pikeAdd.go re s mo lim intoNext pos f stB = .ok st' →
              stA.stk = st.stk.pop →
              stA.seen = st.seen.set! st.stk.back!.pc true →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              parkList intoNext stA = parkList intoNext st →
              Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
                addMeasure intoNext st' ≤ addMeasure intoNext st ∧
                st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
                st'.rc.size ≤
                  max st.rc.size (addMeasure intoNext st + ext.length + 1) := by
            intro stA stW stB slotT hOut pcT value hw hdf hgo hstkA hseenA
              hrcA hfreeA hpoolA hparkA
            have hstA : Owned re.novec stA.rc stA.free stA.pool
                (st.stk.back!.h :: buildLive intoNext stA ext) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
              exact hflight
            obtain ⟨hwo, hws⟩ := write_owned hw hstA
            obtain ⟨hkW, heW⟩ := pikeWrite_ok hw
            obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hw
            obtain ⟨hkD, heD⟩ := pikeDefer_ok hdf
            obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdf
            obtain ⟨hrcD, hfreeD, hplD⟩ := pikeDefer_pool hdf
            have hlen := buildLive_length intoNext stA ext
            have hmA : addMeasure intoNext stA + 1 ≤ addMeasure intoNext st := by
              simp only [addMeasure, hstkA, hseenA, hparkA, Array.size_pop]
              omega
            rw [hrcA] at hws
            refine hstep stB hgo
              (by rw [heD, heW, hseenA, Array.size_set!]; exact hsz)
              (defer_owned hdf hwo) ?_ ?_
            · simp only [addMeasure, hkD, heD, hkW, heW, parkList_eq hclD hnlD,
                parkList_eq hclW hnlW, hparkA, hstkA, hseenA, Array.size_push,
                Array.size_pop]
              omega
            · rw [hrcD]
              omega
          split at h
          · exact absurd h (by simp)
          · repeat' split at h
            all_goals first
              | (rename_i _stA hA _x _stB hB
                 exact harmFork _ _ _ _ _ hA hB h rfl rfl rfl rfl rfl rfl
                   (hstrict (by rw [‹re.code[st.stk.back!.pc]!.op = _›]; decide)))
              | (rename_i _stW _hOut hW _x _stD hD
                 exact harmSave _ _ _ _ _ _ _ hW hD h rfl rfl rfl rfl rfl rfl)
              | (rename_i _stD hD
                 exact harmDefer _ _ _ hD h rfl rfl rfl rfl rfl rfl)
              | (rename_i _stD hD
                 exact harmDrop _ _ hD h rfl rfl rfl rfl rfl rfl)
              | (rename_i _stD hD
                 exact harmPark _ _ _ hD h rfl rfl rfl rfl rfl rfl)
              -- what is left is a refusal, which never reaches the loop again
              | cases h


/-- `pikeAdd` itself: the entry it seeds the worklist with is the handle its
caller was holding, so the build's reckoning covers the whole call. -/
theorem pikeAdd_owned (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (intoNext : Bool) (pos pc0 h0 : Nat) (ext : List Nat) {st st' : PikeSt}
    (hok : pikeAdd re s mo lim intoNext pos pc0 h0 st = .ok st')
    (hsz : st.seen.size = re.code.size)
    (how : Owned re.novec st.rc st.free st.pool
      (h0 :: buildLive intoNext st ext)) :
    Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
      addMeasure intoNext st' ≤ addMeasure intoNext st + 1 ∧
      st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
      st'.rc.size ≤
        max st.rc.size (addMeasure intoNext st + ext.length + 2) := by
  rw [pikeAdd] at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i stD hdf
    obtain ⟨hkD, heD⟩ := pikeDefer_ok hdf
    obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdf
    obtain ⟨hrcD, hfreeD, hplD⟩ := pikeDefer_pool hdf
    have hmD : addMeasure intoNext stD = addMeasure intoNext st + 1 := by
      simp only [addMeasure, hkD, heD, parkList_eq hclD hnlD, Array.size_push]
      omega
    obtain ⟨o1, o2, o3, o4, o5⟩ :=
      pikeAdd_go_owned re s mo lim intoNext pos ext _ _ _ hok
        (by rw [heD]; exact hsz) (defer_owned hdf how)
    rw [hmD] at o2 o5
    rw [hrcD] at o5
    exact ⟨o1, o2, o3, o4, by omega⟩

/-- Seeding a position, owned. The block it takes is one the pool had room
for — either off the free list or fresh, and a fresh one only when nothing
was free, where the handles in reach are what bound the table. -/
theorem pikeSeed_owned (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start pos : Nat) (ext : List Nat) {st st' : PikeSt}
    (hok : pikeSeed re s mo lim start pos st = .ok st')
    (hsz : st.seen.size = re.code.size)
    (hstk : st.stk.size = 0)
    (how : Owned re.novec st.rc st.free st.pool (buildLive false st ext)) :
    Owned re.novec st'.rc st'.free st'.pool (buildLive false st' ext) ∧
      addMeasure false st' ≤ addMeasure false st + 1 ∧
      st'.seen.size = re.code.size ∧ st'.stk.size = 0 ∧
      st'.rc.size ≤ max st.rc.size (addMeasure false st + ext.length + 2) := by
  simp only [pikeSeed] at hok
  split at hok
  · injection hok with hok
    subst hok
    exact ⟨how, by omega, hsz, hstk, Nat.le_max_left _ _⟩
  · split at hok
    · exact absurd hok (by simp)
    · rename_i stT sh ht
      obtain ⟨hkT, heT⟩ := pikeTake_ok ht
      obtain ⟨hclT, hnlT⟩ := pikeTake_lists ht
      obtain ⟨htake, hsize⟩ := pikeTake_owned ht how
      have hlen := buildLive_length false st ext
      have hmT : addMeasure false stT = addMeasure false st := by
        simp only [addMeasure, hkT, heT, parkList_eq hclT hnlT]
      have hbl : buildLive false stT ext = buildLive false st ext := by
        simp only [buildLive, hkT, parkList_eq hclT hnlT]
      have hlive : Owned re.novec stT.rc stT.free stT.pool
          (sh :: buildLive false stT ext) := by
        rw [hbl]
        exact htake
      split at hok
      · exact absurd hok (by simp)
      · obtain ⟨o1, o2, o3, o4, o5⟩ :=
          pikeAdd_owned re s mo lim false pos 0 sh ext hok
            (by rw [heT]; exact hsz)
            (Owned.ofPool hlive (by
              rw [Array.size_set!]
              exact foldl_size _ (fun a k => Array.size_set! _ _ _) _ _))
        refine ⟨o1, ?_, o3, o4, ?_⟩
        · rw [← hmT]
          exact o2
        · have o5' : st'.rc.size ≤
              max stT.rc.size (addMeasure false st + ext.length + 2) := by
            rw [← hmT]
            exact o5
          omega

/-- The measure at the shape a position loop hands a build: the worklist is
empty and the current list has already been paid for by the marks that put
it there, so a build starts inside `2*C` and — since no iteration raises the
measure — never leaves it. That is the worklist half of the `4*C + 2` count,
the two thread lists being the other. -/
theorem LoopOk.addMeasure_le {re : Re} {st : PikeSt} (h : LoopOk re st)
    (hstk : st.stk.size = 0) : addMeasure false st ≤ re.code.size * 2 := by
  have hb := h.bounded
  have hu := unmarked_le_size st.seen
  rw [h.build.seenSize] at hu
  have hpk : parkList false st = st.clist := rfl
  simp only [addMeasure, hpk, hstk]
  omega

/-! ### The list step, read against the pool

A step consumes the current list as a snapshot: what it has already stepped
is not held any more, what it has still to step is, and so is the match it
is carrying. The closures it opens write into the next list, so that is the
list the reckoning follows. -/

/-- The recorded match handle as a list of what it holds: the sentinel is no
block, which is why the drop a step makes before it has a match is a no-op
the ownership does not have to explain. -/
def mhList (mh : Nat) : List Nat := if mh = none32 then [] else [mh]

private theorem perm_last (A : List Nat) (x : Nat) :
    (A ++ [x]).Perm (x :: A) := by
  have h := List.perm_middle (l₁ := A) (a := x) (l₂ := [])
  rwa [List.append_nil] at h

/-- Dropping the threads a recorded match outranks: each of them lets its
handle go, and nothing else moves. -/
theorem dropRest_owned {novec : Nat} {lim : Limits} :
    ∀ (rest : List Th) (st st' : PikeSt) (L : List Nat),
      dropRest lim rest st = .ok st' →
      Owned novec st.rc st.free st.pool (rest.map Th.h ++ L) →
      Owned novec st'.rc st'.free st'.pool L ∧
        st'.stk = st.stk ∧ st'.seen = st.seen ∧ st'.clist = st.clist ∧
        st'.nlist = st.nlist ∧ st'.rc.size = st.rc.size := by
  intro rest
  induction rest with
  | nil =>
      intro st st' L hok how
      rw [dropRest] at hok
      injection hok with hok
      subst hok
      exact ⟨by simpa using how, rfl, rfl, rfl, rfl, rfl⟩
  | cons th rest ih =>
      intro st st' L hok how
      rw [dropRest] at hok
      split at hok
      · exact absurd hok (by simp)
      · rename_i stD hdr
        obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
        obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
        obtain ⟨hrcD, hplD⟩ := pikeDrop_rcSize hdr
        have hmid : Owned novec st.rc st.free st.pool
            (th.h :: (rest.map Th.h ++ L)) := by simpa using how
        obtain ⟨o1, o2, o3, o4, o5, o6⟩ :=
          ih stD st' L hok (pikeDrop_owned hdr hmid)
        exact ⟨o1, o2.trans hkD, o3.trans heD, o4.trans hclD, o5.trans hnlD,
          o6.trans hrcD⟩

theorem mhList_length (mh : Nat) : (mhList mh).length ≤ 1 := by
  rw [mhList]
  split <;> simp

/-- A handle the pool has is not the sentinel, so a recorded match really
does hold a block. -/
theorem Owned.mhList_head {novec : Nat} {rc free : Array Nat}
    {pool : Array UInt32} {L : List Nat} {x : Nat}
    (h : Owned novec rc free pool (x :: L)) : mhList x = [x] := by
  have hne : x ≠ none32 := by
    have h1 := h.reach x List.mem_cons_self
    have h2 := h.capped
    simp only [maxBlocks, liveBlocks, maxCode, maxNodes, growMin,
      growFactor] at h2
    simp only [none32]
    omega
  rw [mhList, if_neg hne]

set_option maxHeartbeats 1000000 in
/-- Stepping the built list, owned. Each thread's handle comes off the
snapshot into flight and lands in the closure it opens, or is let go. The
one arm that allocates is the accept's copy-on-write; it then lets the old
match go — a no-op while the match is still the sentinel — and drops every
thread it outranks, so the step ends holding just the match it recorded.

The reckoning follows the next list, since that is what the closures write
into; the current list is the snapshot being consumed and is not in it. -/
theorem stepThreads_owned (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start pos B : Nat) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool)
      (out : StepOut),
      stepThreads re s mo lim start pos threads st mh seeding matched = .ok out →
      st.seen.size = re.code.size → st.stk.size = 0 →
      addMeasure true st + threads.length + 1 ≤ B →
      Owned re.novec st.rc st.free st.pool
        (buildLive true st (threads.map Th.h ++ mhList mh)) →
      Owned re.novec out.st.rc out.st.free out.st.pool
        (buildLive true out.st (mhList out.mh)) ∧
        addMeasure true out.st + 1 ≤ B ∧
        out.st.seen.size = re.code.size ∧ out.st.stk.size = 0 ∧
        out.st.rc.size ≤ max st.rc.size (B + 2) := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched out h hsz hstk hm how
      rw [stepThreads] at h
      injection h with h
      subst h
      refine ⟨by simpa using how, by simpa using hm, hsz, hstk,
        Nat.le_max_left _ _⟩
  | cons th rest ih =>
      intro st mh seeding matched out h hsz hstk hm how
      have hext : (mhList mh).length ≤ 1 := mhList_length mh
      -- The thread's own handle, taken into flight off the snapshot.
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)) := by
        refine how.perm ?_
        have he : (th :: rest).map Th.h ++ mhList mh =
            th.h :: (rest.map Th.h ++ mhList mh) := by simp
        rw [he, buildLive, buildLive]
        exact List.perm_middle.symm
      have hstep : ∀ stB : PikeSt,
          stepThreads re s mo lim start pos rest stB mh seeding matched = .ok out →
          stB.seen.size = re.code.size → stB.stk.size = 0 →
          addMeasure true stB + rest.length + 1 ≤ B →
          Owned re.novec stB.rc stB.free stB.pool
            (buildLive true stB (rest.map Th.h ++ mhList mh)) →
          stB.rc.size ≤ max st.rc.size (B + 2) →
          Owned re.novec out.st.rc out.st.free out.st.pool
            (buildLive true out.st (mhList out.mh)) ∧
            addMeasure true out.st + 1 ≤ B ∧
            out.st.seen.size = re.code.size ∧ out.st.stk.size = 0 ∧
            out.st.rc.size ≤ max st.rc.size (B + 2) := by
        intro stB hgo hszB hstkB hmB howB hrcB
        obtain ⟨o1, o2, o3, o4, o5⟩ :=
          ih stB mh seeding matched out hgo hszB hstkB hmB howB
        exact ⟨o1, o2, o3, o4, by omega⟩
      -- The three shapes an arm can take, read off the charged state.
      have harmAdd : ∀ (stA stB : PikeSt),
          pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h stA = .ok stB →
          stepThreads re s mo lim start pos rest stB mh seeding matched = .ok out →
          stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
          stA.seen = st.seen → stA.stk = st.stk →
          parkList true stA = parkList true st →
          Owned re.novec out.st.rc out.st.free out.st.pool
            (buildLive true out.st (mhList out.mh)) ∧
            addMeasure true out.st + 1 ≤ B ∧
            out.st.seen.size = re.code.size ∧ out.st.stk.size = 0 ∧
            out.st.rc.size ≤ max st.rc.size (B + 2) := by
        intro stA stB hadd hgo hrcA hfreeA hpoolA hseenA hstkA hparkA
        have hmA : addMeasure true stA = addMeasure true st := by
          simp only [addMeasure, hstkA, hseenA, hparkA]
        have howA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
          exact hmid
        obtain ⟨o1, o2, o3, o4, o5⟩ :=
          pikeAdd_owned re s mo lim true (pos + 1) (th.pc + 1) th.h
            (rest.map Th.h ++ mhList mh) hadd (by rw [hseenA]; exact hsz) howA
        rw [hmA] at o2 o5
        rw [hrcA] at o5
        have hlen : (rest.map Th.h ++ mhList mh).length ≤ rest.length + 1 := by
          simp only [List.length_append, List.length_map]
          omega
        refine hstep stB hgo o3 o4 (by simp only [List.length_cons] at hm; omega)
          o1 (by simp only [List.length_cons] at hm; omega)
      have harmDrop : ∀ (stA stB : PikeSt),
          pikeDrop stA th.h lim = .ok stB →
          stepThreads re s mo lim start pos rest stB mh seeding matched = .ok out →
          stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
          stA.seen = st.seen → stA.stk = st.stk →
          parkList true stA = parkList true st →
          Owned re.novec out.st.rc out.st.free out.st.pool
            (buildLive true out.st (mhList out.mh)) ∧
            addMeasure true out.st + 1 ≤ B ∧
            out.st.seen.size = re.code.size ∧ out.st.stk.size = 0 ∧
            out.st.rc.size ≤ max st.rc.size (B + 2) := by
        intro stA stB hdr hgo hrcA hfreeA hpoolA hseenA hstkA hparkA
        have howA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
          exact hmid
        obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
        obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
        obtain ⟨hrcD, hplD⟩ := pikeDrop_rcSize hdr
        have hmB : addMeasure true stB = addMeasure true st := by
          simp only [addMeasure, hkD, heD, parkList_eq hclD hnlD, hparkA,
            hstkA, hseenA]
        refine hstep stB hgo (by rw [heD, hseenA]; exact hsz)
          (by rw [hkD, hstkA]; exact hstk) ?_ (drop_owned hdr howA) ?_
        · rw [hmB]
          simp only [List.length_cons] at hm
          omega
        · rw [hrcD, hrcA]
          exact Nat.le_max_left _ _
      have harmAccept : ∀ (stA stW stD stF : PikeSt) (hv : Nat),
          pikeWrite stA re.novec th.h 1 pos.toUInt32 lim = .ok (stW, hv) →
          pikeDrop stW mh lim = .ok stD →
          dropRest lim rest stD = .ok stF →
          (Except.ok ⟨stF, hv, false, true⟩ : POut StepOut) = .ok out →
          stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
          stA.seen = st.seen → stA.stk = st.stk →
          parkList true stA = parkList true st →
          Owned re.novec out.st.rc out.st.free out.st.pool
            (buildLive true out.st (mhList out.mh)) ∧
            addMeasure true out.st + 1 ≤ B ∧
            out.st.seen.size = re.code.size ∧ out.st.stk.size = 0 ∧
            out.st.rc.size ≤ max st.rc.size (B + 2) := by
        intro stA stW stD stF hv hw hdr hrest hout hrcA hfreeA hpoolA hseenA
          hstkA hparkA
        injection hout with hout
        subst hout
        have howA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
          exact hmid
        obtain ⟨hwo, hws⟩ := write_owned hw howA
        obtain ⟨hkW, heW⟩ := pikeWrite_ok hw
        obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hw
        have hlenA := buildLive_length true stA (rest.map Th.h ++ mhList mh)
        have hmA : addMeasure true stA = addMeasure true st := by
          simp only [addMeasure, hstkA, hseenA, hparkA]
        have hlen : (rest.map Th.h ++ mhList mh).length ≤ rest.length + 1 := by
          simp only [List.length_append, List.length_map]
          omega
        -- The old match let go of: a no-op while it is still the sentinel.
        have hdrop : Owned re.novec stD.rc stD.free stD.pool
            (hv :: buildLive true stW (rest.map Th.h)) := by
          by_cases hmh : mh = none32
          · subst hmh
            have hnil : mhList none32 = [] := by rw [mhList, if_pos rfl]
            have hres := pikeDrop_none_owned hdr hwo
            rw [hnil, List.append_nil] at hres
            exact hres
          · have hmhl : mhList mh = [mh] := by rw [mhList, if_neg hmh]
            refine pikeDrop_owned hdr (how := ?_)
            refine hwo.perm ?_
            rw [hmhl]
            simp only [buildLive]
            have he : handles stW.stk ++ handles (parkList true stW) ++
                (rest.map Th.h ++ [mh]) =
                (handles stW.stk ++ handles (parkList true stW) ++
                  rest.map Th.h) ++ [mh] := by simp
            rw [he]
            exact (((perm_last _ mh).cons hv).trans
              (List.Perm.swap mh hv _)).symm
        obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
        obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
        obtain ⟨hrcD, hplD⟩ := pikeDrop_rcSize hdr
        have hblD : buildLive true stD (rest.map Th.h) =
            buildLive true stW (rest.map Th.h) := by
          simp only [buildLive, hkD, parkList_eq hclD hnlD]
        -- And the threads the match outranks.
        have hrestL : Owned re.novec stD.rc stD.free stD.pool
            (rest.map Th.h ++
              (hv :: (handles stD.stk ++ handles (parkList true stD)))) := by
          refine hdrop.perm ?_
          rw [← hblD, buildLive]
          exact List.perm_middle.trans ((List.perm_append_comm).cons hv)
        obtain ⟨r1, r2, r3, r4, r5, r6⟩ := dropRest_owned rest stD stF _ hrest hrestL
        have hone := r1.mhList_head
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show Owned re.novec stF.rc stF.free stF.pool
            (buildLive true stF (mhList hv))
          refine r1.perm ?_
          rw [hone, buildLive, r2, parkList_eq r4 r5]
          exact perm_last _ hv
        · have hmF : addMeasure true stF = addMeasure true st := by
            simp only [addMeasure, r2, r3, parkList_eq r4 r5, hkD, heD,
              parkList_eq hclD hnlD, hkW, heW, parkList_eq hclW hnlW, hstkA,
              hseenA, hparkA]
          show addMeasure true stF + 1 ≤ B
          rw [hmF]
          simp only [List.length_cons] at hm
          omega
        · show stF.seen.size = re.code.size
          rw [r3, heD, heW, hseenA]
          exact hsz
        · show stF.stk.size = 0
          rw [r2, hkD, hkW, hstkA]
          exact hstk
        · show stF.rc.size ≤ max st.rc.size (B + 2)
          rw [r6, hrcD]
          rw [hrcA] at hws
          rw [hmA] at hlenA
          simp only [List.length_cons] at hm
          omega
      simp only [stepThreads] at h
      split at h
      · cases h
      · cases hop : (re.code[th.pc]!).op <;> simp only [hop] at h
        case chr | chrCI | cls | any | anyNoNL =>
          split at h
          · split at h
            · cases h
            · rename_i stA hadd
              exact harmAdd _ _ hadd h rfl rfl rfl rfl rfl rfl
          · split at h
            · cases h
            · rename_i stA hdr
              exact harmDrop _ _ hdr h rfl rfl rfl rfl rfl rfl
        case accept =>
          split at h
          · split at h
            · cases h
            · rename_i stA hdr
              exact harmDrop _ _ hdr h rfl rfl rfl rfl rfl rfl
          · split at h
            · cases h
            · rename_i stW hv hw
              split at h
              · cases h
              · rename_i stD hdr
                split at h
                · cases h
                · rename_i stF hrest
                  exact harmAccept _ _ _ _ _ hw hdr hrest h rfl rfl rfl rfl rfl
                    rfl
        case bsr | split | jump | save | circ | circM | doll | dollE | dollM
            | sod | eod | eodn | wordB | notWordB | repZero | repLoop
            | repEnter | repNext =>
          all_goals
            split at h
            · cases h
            · rename_i stA hdr
              exact harmDrop _ _ hdr h rfl rfl rfl rfl rfl rfl

theorem handles_empty {a : Array Th} (h : a.size = 0) : handles a = [] := by
  have : a.toList = [] := List.eq_nil_of_length_eq_zero (by rwa [Array.length_toList])
  rw [handles, this, List.map_nil]

/-! ### The position loop, read against the pool -/

/-- What a position loop iteration starts inside: the dedup invariant, an
emptied worklist, the pool's reading against the current list and the match
in hand, and a block table inside BOUNDS.md section 9's `4*C + 2`. -/
structure PosOk (re : Re) (st : PikeSt) (mh : Nat) : Prop where
  loop : LoopOk re st
  stk : st.stk.size = 0
  owned : Owned re.novec st.rc st.free st.pool (buildLive false st (mhList mh))
  pool : st.rc.size ≤ re.code.size * 4 + 2

set_option maxHeartbeats 1000000 in
/-- `PosOk` is inductive, and the pool clause is where BOUNDS.md section 9's
`4*C + 2` comes out. A position seeds one block on top of what its current
list and its match already hold, and its step takes at most one more per
copy-on-write; the dedup bounds both lists by `C` and the worklist measure
bounds the closure, so the handles in reach never pass `4*C + 1` and the
block table never passes one more than that. -/
theorem pikeLoop_owned (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) (anchored : Bool) (words : Nat) (hwf : ReWf re) :
    ∀ (steps pos : Nat) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      PosOk re st mh →
      PosOk re (pikeLoop re s mo lim start anchored words steps pos st mh
          seeding matched).1
        (pikeLoop re s mo lim start anchored words steps pos st mh seeding
          matched).2.1 ∨
        (pikeLoop re s mo lim start anchored words steps pos st mh seeding
          matched).2.2 = .exceeded := by
  intro steps
  induction steps with
  | zero =>
      intro pos st mh seeding matched _
      rw [pikeLoop]
      exact Or.inr rfl
  | succ k ih =>
      intro pos st mh seeding matched hok
      have hC := hwf.sized
      have hseeded : ∀ stS : PikeSt,
          (if seeding && (!anchored || pos == start) then
            pikeSeed re s mo lim start pos st
            else (Except.ok st : POut PikeSt)) = .ok stS →
          BuildOk re stS ∧
            stS.clist.size + stS.nlist.size + unmarked stS.seen ≤ re.code.size ∧
            stS.nlist.size = 0 ∧ stS.stk.size = 0 ∧
            Owned re.novec stS.rc stS.free stS.pool
              (buildLive false stS (mhList mh)) ∧
            stS.rc.size ≤ re.code.size * 4 + 2 := by
        intro stS hs
        have hbd := hok.loop.bounded
        have hem := hok.loop.empty
        have hmeas := LoopOk.addMeasure_le hok.loop hok.stk
        have hp := hok.pool
        have hml := mhList_length mh
        split at hs
        · obtain ⟨h1, h2, h3⟩ :=
            pikeSeed_build re s mo lim hwf start pos hs hok.loop.build
          obtain ⟨p1, p2, p3, p4, p5⟩ :=
            pikeSeed_owned re s mo lim start pos (mhList mh) hs
              hok.loop.build.seenSize hok.stk hok.owned
          simp only [buildMeasure] at h2
          have h3' := congrArg Array.size h3
          exact ⟨h1, by omega, by omega, p4, p1, by omega⟩
        · injection hs with hs
          subst hs
          exact ⟨hok.loop.build, by omega, hem, hok.stk, hok.owned, hok.pool⟩
      simp only [pikeLoop]
      split
      · exact Or.inr rfl
      · rename_i stS hs
        obtain ⟨hb, hbd, hemp, hstk0, hown, hpool⟩ := hseeded stS hs
        split
        · exact Or.inr rfl
        · have hokc : BuildOk re { stS with
              m := { stS.m with cost := stS.m.cost + words }
              seen := Array.replicate re.code.size false } :=
            ⟨by simp, hb.stk, hb.clist, hb.nlist⟩
          have hfull : unmarked (Array.replicate re.code.size false) ≤
              re.code.size := by
            have := unmarked_le_size (Array.replicate re.code.size false)
            simpa using this
          have hnl : handles stS.nlist = [] := handles_empty hemp
          have hlists : buildLive true { stS with
              m := { stS.m with cost := stS.m.cost + words }
              seen := Array.replicate re.code.size false }
              (stS.clist.toList.map Th.h ++ mhList mh) =
              buildLive false stS (mhList mh) := by
            show handles stS.stk ++ handles stS.nlist ++
                (stS.clist.toList.map Th.h ++ mhList mh) =
              handles stS.stk ++ handles stS.clist ++ mhList mh
            rw [hnl]
            simp [handles]
          have hmC : addMeasure true { stS with
              m := { stS.m with cost := stS.m.cost + words }
              seen := Array.replicate re.code.size false } +
              stS.clist.toList.length + 1 ≤ re.code.size * 3 + 1 := by
            show stS.stk.size + stS.nlist.size +
              2 * unmarked (Array.replicate re.code.size false) +
              stS.clist.toList.length + 1 ≤ re.code.size * 3 + 1
            rw [Array.length_toList]
            omega
          split
          · exact Or.inr rfl
          · rename_i out hx
            obtain ⟨o1, o2, o3⟩ := stepThreads_build re s mo lim hwf start pos
              _ _ mh seeding matched out hx hb.clist hokc
            obtain ⟨q1, q2, q3, q4, q5⟩ :=
              stepThreads_owned re s mo lim start pos (re.code.size * 3 + 1)
                stS.clist.toList _ mh seeding matched out hx (by simp) hstk0
                hmC (by rw [hlists]; exact hown)
            have hrec : buildMeasure { stS with
                m := { stS.m with cost := stS.m.cost + words }
                seen := Array.replicate re.code.size false } =
                stS.clist.size + stS.nlist.size +
                  unmarked (Array.replicate re.code.size false) := rfl
            rw [hrec] at o2
            simp only [buildMeasure] at o2
            have o3' : out.st.clist.size = stS.clist.size := by rw [o3]
            have hfin : PosOk re { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } out.mh := by
              refine ⟨⟨⟨o1.seenSize, o1.stk, o1.nlist, ?_⟩, rfl, ?_⟩, ?_, q1,
                ?_⟩
              · intro y hy
                simp at hy
              · simp only []
                omega
              · show out.st.stk.size = 0
                exact q4
              · show out.st.rc.size ≤ re.code.size * 4 + 2
                have hq : out.st.rc.size ≤
                    max stS.rc.size (re.code.size * 3 + 1 + 2) := q5
                omega
            split
            · exact Or.inl hfin
            · split
              · exact Or.inl hfin
              · exact ih _ _ _ _ _ hfin

/-- A run enters the position loop inside `PosOk`: it clears both lists and
the pool, sizes the visited set to the program, and carries no match yet. So
the block table of a whole lockstep run stays inside `4*C + 2`, which is the
count BOUNDS.md section 9 reserves the pool against. -/
theorem pikeRun_posOk (re : Re) (init : PikeSt) (setup : Nat) :
    PosOk re { init with
      clist := #[], nlist := #[], stk := #[]
      pool := #[], rc := #[], free := #[]
      seen := Array.replicate re.code.size false
      m := ⟨setup, setup, setup⟩ } none32 := by
  refine ⟨pikeRun_loopOk re init setup, rfl, ?_, by simp⟩
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    simp [buildLive, handles, parkList, mhList]

/-- BOUNDS.md section 9's `4*C + 2`, at a run's own call shape: the block
pool of a lockstep scan never holds more than four blocks per instruction
and two besides — one for the recorded match, one for the seed in flight. A
run that blows its budget stops the loop where it stands, which is the other
arm. -/
theorem pikeRun_pool_le (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) (anchored : Bool) (words steps : Nat) (hwf : ReWf re)
    (init : PikeSt) (setup : Nat) :
    (pikeLoop re s mo lim start anchored words steps start
        { init with
          clist := #[], nlist := #[], stk := #[]
          pool := #[], rc := #[], free := #[]
          seen := Array.replicate re.code.size false
          m := ⟨setup, setup, setup⟩ } none32 true false).1.rc.size ≤
        re.code.size * 4 + 2 ∨
      (pikeLoop re s mo lim start anchored words steps start
        { init with
          clist := #[], nlist := #[], stk := #[]
          pool := #[], rc := #[], free := #[]
          seen := Array.replicate re.code.size false
          m := ⟨setup, setup, setup⟩ } none32 true false).2.2 = .exceeded := by
  rcases pikeLoop_owned re s mo lim start anchored words hwf steps start _
    none32 true false (pikeRun_posOk re init setup) with h | h
  · exact Or.inl h.pool
  · exact Or.inr h

/-! ## What the growth schedule costs

BOUNDS.md section 9 charges the growing arrays once across the whole call
rather than once per position: an array grown from `c` entries to at least
`2c` pays three entry widths of `c` and leaves three times its new
reservation standing behind it — that is the `3R` in the cost line — and while the copy
is in flight both buffers are resident, which is the `2R` in the memory
line.

The accounting only reads that way if the schedule is left to grow, and
`charge_grow` clamps at a declared maximum. On the backtracking side that
clamp is out of reach because no memory limit could pay for an array so
large. Here the reason is different and simpler: every array has an entry
bound read off the program — `C` for a thread list, `2*C` for the closure
stack, `4*C + 2` blocks for the pool — and the four maxima of `Pike.lean`
sit above twice the largest of those that a program of at most `maxCode`
instructions with at most `maxOvec` slots can reach. `ReWf.coded` and
`ReWf.slots` are the two clauses that say the program is one of them.

Unclamped, the schedule answers `max growMin (2 * oldcap)`, so it doubles
once the array is past its first four entries, and the amortized inequality
is stated against that rather than against a bare `2 * oldcap`. The two
generic lemmas below carry Pike-flavoured names because the backtracking
file already owns `chargeGrow_cases` and `chargeGrow_within` in this
namespace. -/

/-- A larger entry bound never reserves less. -/
theorem capFor_mono {a b : Nat} (h : a ≤ b) : capFor a ≤ capFor b := by
  simp only [capFor, growMin, growFactor]
  split <;> split <;> omega

/-- Both arms of `charge_grow` with the bindings taken out: a push the
capacity in hand already covers moves nothing, and one it does not charges
the new buffer and the old one it copies out of, holding both while it
does. -/
theorem chargeGrow_arms {oldcap len esize maxv cap : Nat} {m m' : Meter}
    {lim : Limits}
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    (len < oldcap ∧ m' = m ∧ cap = oldcap) ∨
      (oldcap ≤ len ∧ len < maxv ∧
        cap = min maxv (max growMin (oldcap * growFactor)) ∧
        m'.cost = m.cost + (cap * esize + oldcap * esize) ∧
        m'.mem = m.mem + cap * esize - oldcap * esize ∧
        m'.peak = max m.peak (m.mem + cap * esize) ∧
        cap * esize ≤ lim.mem - m.mem) := by
  simp only [chargeGrow] at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨hlt, h.1.symm, h.2.symm⟩
  · rename_i hlt
    split at h
    · cases h
    · rename_i hmax
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hm, hc⟩ := h
          subst hm
          subst hc
          exact Or.inr ⟨by omega, by omega, rfl, rfl, rfl, rfl, by omega⟩

/-- One step of the schedule weighed against the array's own entry bound.
Twice the bound is below the declared maximum, so the `min` does not clamp
and the capacity grows the way the schedule means it to: it stays inside its
answer for the bound, the charge it makes is covered by three times the
reservation it leaves standing, and the memory identity survives with both
buffers counted at the peak.

The peak line carries the old capacity on both sides. A step that found room
moves nothing at all, and one that grew doubles, so the buffer it copies out
of is paid for twice over by the one it copies into — which is what lets a
whole stretch's peak be read against the reservation it ends with rather than
against every intermediate one. -/
theorem chargeGrow_capFor {oldcap len esize maxv cap claim : Nat}
    {m m' : Meter} {lim : Limits}
    (hgm : growMin ≤ maxv) (hclaim : growFactor * claim ≤ maxv)
    (hlen : len < claim) (hroom : oldcap ≤ capFor claim)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    cap ≤ capFor claim ∧ oldcap ≤ cap ∧
      m'.cost + 3 * (oldcap * esize) ≤ m.cost + 3 * (cap * esize) ∧
      m'.mem + oldcap * esize = m.mem + cap * esize ∧
      m'.peak + 2 * (oldcap * esize) ≤
        max (m.peak + 2 * (oldcap * esize)) (m.mem + 2 * (cap * esize)) := by
  have hclaim0 : claim ≠ 0 := by omega
  simp only [capFor, if_neg hclaim0, growMin, growFactor] at hroom ⊢
  simp only [growMin, growFactor] at hgm hclaim
  rcases chargeGrow_arms h with ⟨hlt, hm, hc⟩ |
    ⟨hge, -, hcap, hcost, hmem, hpeak, -⟩
  · subst hm
    subst hc
    exact ⟨hroom, Nat.le_refl _, by omega, rfl, by omega⟩
  · -- The schedule asked for at most twice the bound, which the maximum
    -- covers, so the answer is the doubling and not the clamp.
    simp only [growMin, growFactor] at hcap
    have hdouble : cap = max 4 (oldcap * 2) := by omega
    have hstep : 2 * oldcap ≤ cap := by omega
    have hprod : 2 * (oldcap * esize) ≤ cap * esize := by
      have := Nat.mul_le_mul_right esize hstep
      rwa [Nat.mul_assoc] at this
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The four maxima of `Pike.lean`, each above twice the entry bound of the
array it guards, for every program `ReWf` admits. -/
theorem pikeSchedule {re : Re} (hwf : ReWf re) :
    (growMin ≤ maxThreads ∧ growFactor * re.code.size ≤ maxThreads) ∧
      (growMin ≤ maxClosure ∧ growFactor * (re.code.size * 2) ≤ maxClosure) ∧
      (growMin ≤ maxBlocks ∧
        growFactor * (re.code.size * 4 + 2) ≤ maxBlocks) ∧
      (growMin ≤ maxPool ∧
        growFactor * ((re.code.size * 4 + 2) * re.novec) ≤ maxPool) := by
  have hc := hwf.coded
  have hv := hwf.slots
  have hblocks : re.code.size * 4 + 2 ≤ liveBlocks := by
    simp only [liveBlocks, maxCode, maxNodes] at *
    omega
  have hpool : (re.code.size * 4 + 2) * re.novec ≤ liveBlocks * maxOvec :=
    Nat.mul_le_mul hblocks hv
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [maxThreads, growMin, growFactor, maxCode, maxNodes]
    omega
  · simp only [maxThreads, growMin, growFactor, maxCode, maxNodes] at *
    omega
  · simp only [maxClosure, growMin, growFactor, maxCode, maxNodes]
    omega
  · simp only [maxClosure, growMin, growFactor, maxCode, maxNodes] at *
    omega
  · simp only [maxBlocks, liveBlocks, growMin, growFactor, maxCode, maxNodes]
    omega
  · simp only [maxBlocks, liveBlocks, growMin, growFactor, maxCode,
      maxNodes] at *
    omega
  · simp only [maxPool, growMin]
    omega
  · calc growFactor * ((re.code.size * 4 + 2) * re.novec)
        ≤ growFactor * (liveBlocks * maxOvec) := Nat.mul_le_mul_left _ hpool
      _ ≤ maxPool := by simp only [maxPool, growMin]; omega

/-- BOUNDS.md section 9's `R`, with the counter arithmetic taken out: the
four capacities `pikeRoom` weighs, each times its entry size. Written as a
plain function of the program so that a run-level invariant can name it
without carrying `pikeRoom`'s overflow flag around; `pikeScratch_eq` is
where it meets `pikeReserved`. -/
def pikeScratch (re : Re) : Nat :=
  capFor re.code.size * (2 * thSize) + capFor (re.code.size * 2) * thSize +
    capFor (re.code.size * 4 + 2) * (2 * regSize) +
    capFor ((re.code.size * 4 + 2) * re.novec) * regSize

theorem pikeScratch_eq {re : Re} (h : (pikeRoom re false).2 = false) :
    pikeScratch re = pikeReserved re := by
  rw [pikeReserved_eq h, pikeScratch, Re.novec, Nat.mul_comm 2 (re.ncap + 1)]

/-- The scratch bytes a state holds: every growing array at the capacity it
carries, weighed by its entry size. -/
def PikeSt.reserved (st : PikeSt) : Nat :=
  (st.clistCap + st.nlistCap + st.stkCap) * thSize +
    (st.rcCap + st.freeCap + st.poolCap) * regSize

/-- Every array of a state inside the growth schedule's capacity for its own
entry bound. These are the four numbers `pikeRoom` weighs, which is why a
state satisfying this reserves no more than `R`. -/
structure Rooms (re : Re) (st : PikeSt) : Prop where
  clist : st.clistCap ≤ capFor re.code.size
  nlist : st.nlistCap ≤ capFor re.code.size
  stk : st.stkCap ≤ capFor (re.code.size * 2)
  rc : st.rcCap ≤ capFor (re.code.size * 4 + 2)
  free : st.freeCap ≤ capFor (re.code.size * 4 + 2)
  pool : st.poolCap ≤ capFor ((re.code.size * 4 + 2) * re.novec)

theorem Rooms.scratch_le {re : Re} {st : PikeSt} (h : Rooms re st) :
    st.reserved ≤ pikeScratch re := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [PikeSt.reserved, pikeScratch, thSize, regSize]
  omega

/-- A run handed nothing pre-reserved starts inside every room. -/
theorem Rooms.zero {re : Re} {st : PikeSt} (hc : st.clistCap = 0)
    (hn : st.nlistCap = 0) (hs : st.stkCap = 0) (hr : st.rcCap = 0)
    (hf : st.freeCap = 0) (hp : st.poolCap = 0) : Rooms re st :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A stretch of a run inside the prices BOUNDS.md section 9 names: it
charges at most `spent` on top of the growth its own reservation pays for,
it stays inside every room, it never gives a reservation back, its memory
reading is the setup plus what it reserves and moves only with that
reservation, and its peak is bounded by where it started and by twice what
it ends up holding.

The cost line is amortized the way section 5's is. Growth is charged once
across the call rather than once per position, and the schedule doubles, so
a stretch that grows an array from `c` entries to `2c` pays `3c` entry
widths and leaves three times the new reservation standing. Carrying the
reservation on both sides of the inequality is what lets the positions
compose without counting a growth twice.

The memory lines are carried the same way, and for the same reason. `held`
is the absolute reading a plain call needs; `moved` is the relative one, and
it is what a call through a preallocated context needs, since such a call
starts with a reservation already in hand and a meter that has not been told
about it. Read together they say a stretch that grew nothing moved nothing —
which is R-9's no-allocation clause. -/
structure Charged (re : Re) (setup spent : Nat) (st out : PikeSt) : Prop where
  charge : out.m.cost + 3 * st.reserved ≤ st.m.cost + 3 * out.reserved + spent
  rooms : Rooms re out
  grown : st.reserved ≤ out.reserved
  held : out.m.mem ≤ setup + out.reserved
  moved : out.m.mem + st.reserved = st.m.mem + out.reserved
  resident : out.m.peak + 2 * st.reserved ≤
    max (st.m.peak + 2 * st.reserved) (st.m.mem + 2 * out.reserved)

/-- Standing still is inside any price, and so is a step that writes a
buffer without growing it — the reading is about capacities and the meter,
and neither moves. -/
theorem Charged.idle {re : Re} {setup : Nat} {st st' : PikeSt}
    (hrooms : Rooms re st') (hres : st'.reserved = st.reserved)
    (hm : st'.m = st.m) (hmem : st.m.mem ≤ setup + st.reserved) :
    Charged re setup 0 st st' :=
  ⟨by rw [hm, hres]; omega, hrooms, Nat.le_of_eq hres.symm,
    by rw [hm, hres]; exact hmem, by rw [hm, hres],
    by rw [hm, hres]; exact Nat.le_max_left _ _⟩

/-- Two stretches in a row spend what the two of them spend, and the
reservation in the middle cancels — which is the point of carrying it. The
peak cancels the same way: the middle reservation is at least the first and
at most the last, so what the second stretch could reach above the first is
already covered by the reservation the pair ends with. -/
theorem Charged.trans {re : Re} {setup a b : Nat} {st mid out : PikeSt}
    (h₁ : Charged re setup a st mid) (h₂ : Charged re setup b mid out) :
    Charged re setup (a + b) st out := by
  obtain ⟨c₁, -, g₁, -, v₁, p₁⟩ := h₁
  obtain ⟨c₂, r₂, g₂, m₂, v₂, p₂⟩ := h₂
  exact ⟨by omega, r₂, by omega, m₂, by omega, by omega⟩

/-- A stretch inside one price is inside any larger one. -/
theorem Charged.mono {re : Re} {setup a b : Nat} {st out : PikeSt}
    (h : Charged re setup a st out) (hle : a ≤ b) : Charged re setup b st out :=
  ⟨by have := h.charge; omega, h.rooms, h.grown, h.held, h.moved, h.resident⟩

/-- The peak, read absolutely. A reservation the growth schedule bounds puts
the relative reading back where the plain call wants it: the setup, and twice
what the schedule reserves. -/
theorem Charged.resident_le {re : Re} {setup c : Nat} {st out : PikeSt}
    (h : Charged re setup c st out) (hmem : st.m.mem ≤ setup + st.reserved) :
    out.m.peak ≤ max st.m.peak (setup + 2 * pikeScratch re) := by
  have hle := h.rooms.scratch_le
  have hr := h.resident
  omega

/-- A charge that moves nothing else: the mark a closure pays for a fresh
pc, the unit a step pays per suspended thread, the visited set cleared. -/
theorem Charged.pay {re : Re} {setup : Nat} {st : PikeSt} (c : Nat)
    (hrooms : Rooms re st) (hmem : st.m.mem ≤ setup + st.reserved) :
    Charged re setup c st
      { st with m := { st.m with cost := st.m.cost + c } } := by
  refine ⟨?_, ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
    hrooms.pool⟩, ?_, ?_, ?_, ?_⟩
  · show st.m.cost + c + 3 * st.reserved ≤ st.m.cost + 3 * st.reserved + c
    omega
  · show st.reserved ≤ st.reserved
    exact Nat.le_refl _
  · show st.m.mem ≤ setup + st.reserved
    exact hmem
  · show st.m.mem + st.reserved = st.m.mem + st.reserved
    rfl
  · show st.m.peak + 2 * st.reserved ≤
      max (st.m.peak + 2 * st.reserved) (st.m.mem + 2 * st.reserved)
    exact Nat.le_max_left _ _

/-- One growth step read into the run's own reading. Only the array's
capacity moves, so the reservation on both sides of the schedule's
inequalities is the same up to that one term, and the lines follow from
`chargeGrow_capFor` verbatim. -/
theorem charged_of_grow {re : Re} {setup rest old new esize : Nat}
    {st st' : PikeSt} (hrooms : Rooms re st') (hold : old ≤ new)
    (hres : st.reserved = rest + old * esize)
    (hres' : st'.reserved = rest + new * esize)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hcost : st'.m.cost + 3 * (old * esize) ≤ st.m.cost + 3 * (new * esize))
    (hmem' : st'.m.mem + old * esize = st.m.mem + new * esize)
    (hpeak : st'.m.peak + 2 * (old * esize) ≤
      max (st.m.peak + 2 * (old * esize)) (st.m.mem + 2 * (new * esize))) :
    Charged re setup 0 st st' := by
  have hstep : old * esize ≤ new * esize := Nat.mul_le_mul_right esize hold
  exact ⟨by omega, hrooms, by omega, by omega, by omega, by omega⟩

/-! ## What one position costs

BOUNDS.md section 9 prices a position at `2*C + (S + 2)*B + W`, and the way
a position spends it is a sum of five things: one visited set's worth of
marks, the seed's own block, a unit per thread stepped, the accept's block,
and the visited set cleared. Only the first of those is hard, because it is
the one the closure builds draw on and a build draws on it a mark at a time.

So the account is kept against the visited set. `closureLeft` weighs what a
set still admits: a unit for every pc it has not marked, and one block more
at a `Save`, since a `Save` is the one instruction whose arm can force a
copy-on-write. Marking a pc releases exactly its weight, and the arm that
follows the mark spends exactly that much — a unit everywhere, a unit and a
block at a `Save`. `Spent` is that reading with room for the charges a run
makes outside the closure, and it is what composes.

It has to hold of a refusal too. A helper that is turned away keeps what it
had already charged, and the build stops there rather than going round
again, so every lemma below is stated over `outSt` — the state either arm
hands back — the way `Meter.within` already is in this file.

The growth charges are the other half, and they are the `Charged` reading
from the section above: a helper is weighed at `Charged`, since none of them
marks anything, and the account only appears where the marks do.

Beside every one of those readings sits the same one over the charge a
refusal was asking for, because S-10 wants both halves at once and wants them
of the same stretch. `Blown` and `Tried` are introduced below, after the
helpers and before the four inductions that carry them. -/

/-! ### The free list, counted -/

theorem countBelow_eq_length {l : List Nat} {n : Nat} (h : ∀ x ∈ l, x < n) :
    countBelow l n = l.length := by
  induction l with
  | nil => rw [countBelow_nil]; rfl
  | cons a l ih =>
      rw [countBelow_cons, if_pos (h a List.mem_cons_self),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      simp

theorem countBelow_le_of_once {l : List Nat} (h : ∀ x, l.count x ≤ 1) :
    ∀ n, countBelow l n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      have h1 := countBelow_le_of_once h n
      have h2 := h n
      rw [countBelow]
      omega

theorem countBelow_lt {l : List Nat} (h : ∀ x, l.count x ≤ 1) {y : Nat}
    (hy0 : l.count y = 0) : ∀ n, y < n → countBelow l n < n := by
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
      intro _
      by_cases hy : y = k
      · have h1 := countBelow_le_of_once h k
        have h2 : l.count k = 0 := by rw [← hy]; exact hy0
        rw [countBelow, h2]
        omega
      · have h1 := ih (by omega)
        have h2 := h k
        rw [countBelow]
        omega

/-- The free list holds no block twice, so it is no longer than the refcount
table — and strictly shorter as soon as one block is not on it. -/
theorem Owned.free_lt {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {live : List Nat} (h : Owned novec rc free pool live) {y : Nat}
    (hy : y < rc.size) (hy0 : free.toList.count y = 0) : free.size < rc.size := by
  have h1 := countBelow_eq_length (l := free.toList) (n := rc.size) h.freeRange
  have h2 := countBelow_lt h.freeOnce hy0 rc.size hy
  rw [Array.length_toList] at h1
  omega

/-! ### What a mark buys -/

/-- What marking one pc pays for: the unit the closure charges for it, and —
at a `Save` — the copy-on-write that instruction can force. -/
def markWeight (re : Re) (pc : Nat) : Nat :=
  1 + if (re.code[pc]!).op = .save then pikeBlock re else 0

/-- The weight of every pc below `k` a visited set has not marked yet. -/
def closureLeftGo (re : Re) (seen : Array Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => closureLeftGo re seen k + (if seen[k]! then 0 else markWeight re k)

/-- What the builds a visited set still admits may spend. -/
def closureLeft (re : Re) (seen : Array Bool) : Nat :=
  closureLeftGo re seen seen.size

/-- Marking outside the range already counted moves nothing. -/
theorem closureLeftGo_set_ge (re : Re) {seen : Array Bool} {pc : Nat} :
    ∀ k, k ≤ pc → closureLeftGo re (seen.set! pc true) k = closureLeftGo re seen k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ j ih =>
      intro hk
      rw [closureLeftGo, closureLeftGo, ih (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)]

/-- And marking inside it pays exactly that pc's weight. -/
theorem closureLeftGo_set_lt (re : Re) {seen : Array Bool} {pc : Nat}
    (hpc : pc < seen.size) (hf : seen[pc]! = false) :
    ∀ k, pc < k →
      closureLeftGo re (seen.set! pc true) k + markWeight re pc =
        closureLeftGo re seen k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ j ih =>
      intro _
      rcases Nat.lt_or_ge pc j with hlt | hge
      · have hrec := ih hlt
        rw [closureLeftGo, closureLeftGo,
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
      · have hk : pc = j := by omega
        subst hk
        rw [closureLeftGo, closureLeftGo,
          closureLeftGo_set_ge re pc (Nat.le_refl _),
          Array.getElem!_set!_self _ _ _ hpc, hf]
        simp

theorem closureLeft_set {re : Re} {seen : Array Bool} {pc : Nat}
    (hpc : pc < seen.size) (hf : seen[pc]! = false) :
    closureLeft re (seen.set! pc true) + markWeight re pc =
      closureLeft re seen := by
  rw [closureLeft, closureLeft, Array.size_set!]
  exact closureLeftGo_set_lt re hpc hf seen.size hpc


/-! ### A full visited set's worth -/

/-- The `Save` instructions below `k`, the count `pike_price` folds over the
whole program. -/
private def savesTake (re : Re) (k : Nat) : Nat :=
  (re.code.toList.take k).foldl
    (fun n inst => if inst.op = .save then n + 1 else n) 0

private theorem savesTake_succ {re : Re} {k : Nat} (hk : k < re.code.size) :
    savesTake re (k + 1) =
      savesTake re k + (if (re.code[k]!).op = .save then 1 else 0) := by
  have hlen : k < re.code.toList.length := by
    rw [Array.length_toList]; exact hk
  have hget : re.code.toList[k]? = some (re.code[k]!) := by
    rw [getElem!_pos re.code k hk, List.getElem?_eq_getElem hlen,
      Array.getElem_toList]
  rw [savesTake, savesTake, List.take_add_one, hget]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  split <;> rfl

private theorem savesTake_all (re : Re) :
    savesTake re re.code.size = pikeSaves re := by
  rw [savesTake, ← Array.length_toList, List.take_length, Array.foldl_toList]
  rfl

private theorem closureLeftGo_replicate (re : Re) : ∀ k, k ≤ re.code.size →
    closureLeftGo re (Array.replicate re.code.size false) k =
      k + savesTake re k * pikeBlock re := by
  intro k
  induction k with
  | zero => intro _; simp [closureLeftGo, savesTake]
  | succ j ih =>
      intro hj
      have hjs : j < re.code.size := by omega
      have hrep : (Array.replicate re.code.size false)[j]! = false := by
        rw [getElem!_pos _ j (by simp; omega)]
        simp
      rw [closureLeftGo, ih (by omega), hrep, savesTake_succ hjs, markWeight]
      simp only [Bool.false_eq_true, if_false]
      by_cases hsv : (re.code[j]!).op = .save
      · rw [if_pos hsv, if_pos hsv, Nat.add_mul, Nat.one_mul]
        omega
      · rw [if_neg hsv, if_neg hsv]
        simp only [Nat.add_zero]
        omega

/-- The most one visited set's worth of builds can spend: a unit per
instruction marked, and a copy-on-write per `Save` among them. -/
def closureLeftFull (re : Re) : Nat := re.code.size + pikeSaves re * pikeBlock re

theorem closureLeft_replicate (re : Re) :
    closureLeft re (Array.replicate re.code.size false) = closureLeftFull re := by
  rw [closureLeft, Array.size_replicate,
    closureLeftGo_replicate re _ (Nat.le_refl _), savesTake_all, closureLeftFull]

/-- BOUNDS.md section 9's per-position price, split the way a position spends
it: one visited set's worth of marks, the seed's block, a unit per thread
stepped, the accept's block, and the visited set cleared. -/
theorem position_split (re : Re) :
    closureLeftFull re + pikeBlock re + re.code.size + pikeBlock re +
        pikeWords re = pikePosition re := by
  rw [closureLeftFull, pikePosition, Nat.add_mul]
  omega

/-! ### The charge account -/

/-- What a stretch of a run spent, weighed against the marks its visited set
had left to make. `extra` is what it spends outside that account: the unit a
list step pays per thread, the block a seed fills, the visited set cleared. -/
def Spent (re : Re) (setup extra : Nat) (st out : PikeSt) : Prop :=
  ∃ spent, Charged re setup spent st out ∧
    closureLeft re out.seen + spent ≤ closureLeft re st.seen + extra

theorem Spent.rooms {re : Re} {setup extra : Nat} {st out : PikeSt}
    (h : Spent re setup extra st out) : Rooms re out := by
  obtain ⟨spent, hc, hle⟩ := h
  exact hc.rooms

theorem Spent.held {re : Re} {setup extra : Nat} {st out : PikeSt}
    (h : Spent re setup extra st out) : out.m.mem ≤ setup + out.reserved := by
  obtain ⟨spent, hc, hle⟩ := h
  exact hc.held

/-- Cashing the account out: a stretch whose visited set had at most `k` to
give spends at most that and its extras. -/
theorem Spent.charged {re : Re} {setup extra k : Nat} {st out : PikeSt}
    (h : Spent re setup extra st out) (hleft : closureLeft re st.seen ≤ k) :
    Charged re setup (k + extra) st out := by
  obtain ⟨spent, hc, hle⟩ := h
  exact hc.mono (by omega)

theorem Spent.refl {re : Re} {setup : Nat} {st : PikeSt} (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved) : Spent re setup 0 st st :=
  ⟨0, Charged.idle hrooms rfl rfl hmem, by omega⟩

theorem Spent.trans {re : Re} {setup a b : Nat} {st mid out : PikeSt}
    (h₁ : Spent re setup a st mid) (h₂ : Spent re setup b mid out) :
    Spent re setup (a + b) st out := by
  obtain ⟨s₁, c₁, l₁⟩ := h₁
  obtain ⟨s₂, c₂, l₂⟩ := h₂
  exact ⟨s₁ + s₂, (c₁.trans c₂), by omega⟩

theorem Spent.mono {re : Re} {setup a b : Nat} {st out : PikeSt}
    (h : Spent re setup a st out) (hle : a ≤ b) : Spent re setup b st out := by
  obtain ⟨s, c, l⟩ := h
  exact ⟨s, c, by omega⟩

/-- A charge a helper made without touching the visited set. -/
theorem Spent.ofCharged {re : Re} {setup c : Nat} {st out : PikeSt}
    (h : Charged re setup c st out) (hseen : out.seen = st.seen) :
    Spent re setup c st out :=
  ⟨c, h, by rw [hseen]; omega⟩


/-! ### Reading the account off either arm -/

/-- Reading a stretch off a refusal. -/
theorem charged_of_error {α : Type} {get : α → PikeSt} {x : POut α}
    {stE : PikeSt} {re : Re} {setup c : Nat} {st : PikeSt} (he : x = .error stE)
    (h : Charged re setup c st (outSt get x)) : Charged re setup c st stE := by
  rw [he] at h
  exact h

/-- And off a success, for a step that answers a state. -/
theorem charged_ok_id {x : POut PikeSt} {a : PikeSt} {re : Re} {setup c : Nat}
    {st : PikeSt} (he : x = .ok a) (h : Charged re setup c st (outSt id x)) :
    Charged re setup c st a := by
  rw [he] at h
  exact h

/-- For one that answers a state and a handle. -/
theorem charged_ok_fst {x : POut (PikeSt × Nat)} {a : PikeSt × Nat} {re : Re}
    {setup c : Nat} {st : PikeSt} (he : x = .ok a)
    (h : Charged re setup c st (outSt Prod.fst x)) :
    Charged re setup c st a.1 := by
  rw [he] at h
  exact h

/-- The reading only looks at the meter and the capacities, so a state that
agrees on both is the same starting point. -/
theorem Charged.ofState {re : Re} {setup c : Nat} {st st' out : PikeSt}
    (h : Charged re setup c st' out) (hm : st'.m = st.m)
    (hres : st'.reserved = st.reserved) : Charged re setup c st out :=
  ⟨by rw [← hm, ← hres]; exact h.charge, h.rooms, by rw [← hres]; exact h.grown,
    h.held, by rw [← hm, ← hres]; exact h.moved,
    by rw [← hm, ← hres]; exact h.resident⟩

/-- A helper that answered, at the shape a `split` leaves behind, so that
what follows never has to see through `outSt`. -/
theorem Charged.ofOk {re : Re} {setup c : Nat} {st out : PikeSt}
    (h : Charged re setup c st out) :
    Charged re setup c st (outSt id (Except.ok out)) := h

theorem spent_of_error {α : Type} {get : α → PikeSt} {x : POut α}
    {stE : PikeSt} {re : Re} {setup c : Nat} {st : PikeSt} (he : x = .error stE)
    (h : Spent re setup c st (outSt get x)) : Spent re setup c st stE := by
  rw [he] at h
  exact h

theorem spent_ok_id {x : POut PikeSt} {a : PikeSt} {re : Re} {setup c : Nat}
    {st : PikeSt} (he : x = .ok a) (h : Spent re setup c st (outSt id x)) :
    Spent re setup c st a := by
  rw [he] at h
  exact h

theorem spent_ok_step {x : POut StepOut} {a : StepOut} {re : Re} {setup c : Nat}
    {st : PikeSt} (he : x = .ok a)
    (h : Spent re setup c st (outSt StepOut.st x)) :
    Spent re setup c st a.st := by
  rw [he] at h
  exact h

/-- One iteration of a closure build, weighed against the pc it marked: the
mark pays for the unit the loop charges and, at a `Save`, for the copy the
arm makes, so all the rest of the build spends is what the visited set still
had. -/
theorem spent_of_mark {re : Re} {setup c : Nat} {st mid out : PikeSt} {pc : Nat}
    (hpc : pc < st.seen.size) (hf : st.seen[pc]! = false)
    (hseen : mid.seen = st.seen.set! pc true)
    (h : Charged re setup c st mid) (hc : c ≤ markWeight re pc)
    (htail : Spent re setup 0 mid out) : Spent re setup 0 st out := by
  obtain ⟨s', hc', hle⟩ := htail
  refine ⟨c + s', h.trans hc', ?_⟩
  rw [hseen] at hle
  have hset := closureLeft_set (re := re) hpc hf
  omega

/-- And an iteration that marked nothing: the pop it made is what paid for
it, and the account is untouched. -/
theorem spent_of_idle {re : Re} {setup : Nat} {st mid out : PikeSt}
    (h : Charged re setup 0 st mid) (hseen : mid.seen = st.seen)
    (htail : Spent re setup 0 mid out) : Spent re setup 0 st out :=
  Spent.mono ((Spent.ofCharged h hseen).trans htail) (by omega)

/-! ### What each helper's growth costs

A refused helper keeps whatever it had already charged, so the reading has to
hold of the state it hands back as well as of the one it answers. `outSt` is
that state either way, which is the shape `Meter.within` already uses here.
None of these touches the visited set, so they are read at the `Charged`
level and the account only enters at the loops. -/

theorem pikeDefer_charged {re : Re} {st : PikeSt} {pc h setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hsize : st.stk.size < re.code.size * 2) :
    Charged re setup 0 st (outSt id (pikeDefer st pc h lim)) := by
  obtain ⟨-, ⟨hgm, hcl⟩, -, -⟩ := pikeSchedule hwf
  simp only [pikeDefer]
  split
  · exact Charged.idle hrooms rfl rfl hmem
  · rename_i mm cap hg
    obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
      chargeGrow_capFor hgm hcl hsize hrooms.stk hg
    refine Charged.ofOk (charged_of_grow (esize := thSize)
      (rest := (st.clistCap + st.nlistCap) * thSize +
        (st.rcCap + st.freeCap + st.poolCap) * regSize)
      ⟨hrooms.clist, hrooms.nlist, hcap, hrooms.rc, hrooms.free, hrooms.pool⟩
      hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
      (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost hmem'
      hpeak)

theorem pikePark_charged {re : Re} {st : PikeSt} {intoNext : Bool}
    {pc h setup : Nat} {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hsize : (parkList intoNext st).size < re.code.size) :
    Charged re setup 0 st (outSt id (pikePark st intoNext pc h lim)) := by
  obtain ⟨⟨hgm, hcl⟩, -, -, -⟩ := pikeSchedule hwf
  simp only [parkList] at hsize
  simp only [pikePark]
  split
  · rename_i hin
    rw [if_pos hin] at hsize
    split
    · exact Charged.idle hrooms rfl rfl hmem
    · rename_i mm cap hg
      obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
        chargeGrow_capFor hgm hcl hsize hrooms.nlist hg
      refine Charged.ofOk (charged_of_grow (esize := thSize)
        (rest := (st.clistCap + st.stkCap) * thSize +
          (st.rcCap + st.freeCap + st.poolCap) * regSize)
        ⟨hrooms.clist, hcap, hrooms.stk, hrooms.rc, hrooms.free, hrooms.pool⟩
        hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
        (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
        hmem' hpeak)
  · rename_i hin
    rw [if_neg hin] at hsize
    split
    · exact Charged.idle hrooms rfl rfl hmem
    · rename_i mm cap hg
      obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
        chargeGrow_capFor hgm hcl hsize hrooms.clist hg
      refine Charged.ofOk (charged_of_grow (esize := thSize)
        (rest := (st.nlistCap + st.stkCap) * thSize +
          (st.rcCap + st.freeCap + st.poolCap) * regSize)
        ⟨hcap, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free, hrooms.pool⟩
        hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
        (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
        hmem' hpeak)

theorem pikeDrop_charged {re : Re} {st : PikeSt} {h setup : Nat} {lim : Limits}
    (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hsize : st.rc[h]! ≤ 1 → st.free.size < re.code.size * 4 + 2) :
    Charged re setup 0 st (outSt id (pikeDrop st h lim)) := by
  obtain ⟨-, -, ⟨hgm, hcl⟩, -⟩ := pikeSchedule hwf
  simp only [pikeDrop]
  split
  · exact Charged.idle hrooms rfl rfl hmem
  · split
    · rename_i hzero
      split
      · exact Charged.idle ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc,
          hrooms.free, hrooms.pool⟩ rfl rfl hmem
      · rename_i mm cap hg
        obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
          chargeGrow_capFor hgm hcl
            (hsize (by simp only [beq_iff_eq] at hzero; omega)) hrooms.free hg
        refine Charged.ofOk (charged_of_grow (esize := regSize)
          (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
            (st.rcCap + st.poolCap) * regSize)
          ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hcap,
            hrooms.pool⟩
          hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
          (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
          hmem' hpeak)
    · exact Charged.idle ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc,
        hrooms.free, hrooms.pool⟩ rfl rfl hmem

/-- The block fill of `pike_take`: one pool push per slot, each inside the
pool's own entry bound because the block it is filling is one the pool has
room for. -/
theorem pikeTake_fill_charged {re : Re} {setup : Nat} {lim : Limits}
    (hwf : ReWf re) : ∀ (k : Nat) (st : PikeSt), Rooms re st →
      st.m.mem ≤ setup + st.reserved →
      st.pool.size + k ≤ (re.code.size * 4 + 2) * re.novec →
      Charged re setup 0 st (outSt id (pikeTake.fill lim k st)) := by
  obtain ⟨-, -, -, ⟨hgm, hcl⟩⟩ := pikeSchedule hwf
  intro k
  induction k with
  | zero =>
      intro st hrooms hmem _
      rw [pikeTake.fill]
      exact Charged.idle hrooms rfl rfl hmem
  | succ n ih =>
      intro st hrooms hmem hpool
      rw [pikeTake.fill]
      split
      · exact Charged.idle hrooms rfl rfl hmem
      · rename_i mm cap hg
        obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
          chargeGrow_capFor hgm hcl (by omega) hrooms.pool hg
        have hstep : Charged re setup 0 st
            { st with
              m := mm, poolCap := cap, pool := st.pool.push unset32 } :=
          charged_of_grow (esize := regSize)
            (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
              (st.rcCap + st.freeCap) * regSize)
            ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
              hcap⟩
            hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
            (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
            hmem' hpeak
        exact Charged.mono
          (hstep.trans (ih _ hstep.rooms hstep.held (by simp; omega)))
          (by omega)

theorem pikeTake_charged {re : Re} {st : PikeSt} {novec setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hrc : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2)
    (hpool : st.free.size = 0 →
      st.pool.size + novec ≤ (re.code.size * 4 + 2) * re.novec) :
    Charged re setup 0 st (outSt Prod.fst (pikeTake st novec lim)) := by
  obtain ⟨-, -, ⟨hgm, hcl⟩, -⟩ := pikeSchedule hwf
  simp only [pikeTake]
  split
  · refine Charged.idle ?_ rfl rfl hmem
    exact ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
      hrooms.pool⟩
  · rename_i hempty
    have hzero : st.free.size = 0 := by
      rcases Nat.eq_zero_or_pos st.free.size with hz | hp
      · exact hz
      · exact absurd (by simpa using hp) hempty
    split
    · exact Charged.idle hrooms rfl rfl hmem
    · split
      · exact Charged.idle hrooms rfl rfl hmem
      · rename_i mm cap hg
        obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
          chargeGrow_capFor hgm hcl (hrc hzero) hrooms.rc hg
        have hstep : Charged re setup 0 st
            { st with m := mm, rcCap := cap, rc := st.rc.push 1 } :=
          charged_of_grow (esize := regSize)
            (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
              (st.freeCap + st.poolCap) * regSize)
            ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hcap, hrooms.free,
              hrooms.pool⟩
            hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
            (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
            hmem' hpeak
        have hfill := pikeTake_fill_charged (setup := setup) (lim := lim) hwf
          novec _ hstep.rooms hstep.held (by simpa using hpool hzero)
        split
        · rename_i he
          exact Charged.mono (hstep.trans (charged_of_error he hfill)) (by omega)
        · rename_i he
          exact Charged.mono (hstep.trans (charged_ok_id he hfill)) (by omega)

/-- The copy-on-write of `pike_write`: one block copied out at a cost unit
per byte, and the fresh block it copies into. -/
theorem pikeWrite_charged {re : Re} {st : PikeSt} {novec h slot setup : Nat}
    {value : UInt32} {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hrc : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2)
    (hpool : st.free.size = 0 →
      st.pool.size + novec ≤ (re.code.size * 4 + 2) * re.novec) :
    Charged re setup (novec * regSize) st
      (outSt Prod.fst (pikeWrite st novec h slot value lim)) := by
  simp only [pikeWrite]
  split
  · split
    · exact Charged.mono (Charged.idle hrooms rfl rfl hmem) (Nat.zero_le _)
    · have hpaid := Charged.pay (re := re) (setup := setup) (novec * regSize)
        hrooms hmem
      have htake := pikeTake_charged (novec := novec) (lim := lim) hwf
        hpaid.rooms hpaid.held hrc hpool
      split
      · rename_i he
        exact Charged.mono (hpaid.trans (charged_of_error he htake)) (by omega)
      · rename_i he
        refine Charged.mono ((hpaid.trans (charged_ok_fst he htake)).trans
          (Charged.idle ?_ rfl rfl (charged_ok_fst he htake).held)) ?_
        · have hr := (charged_ok_fst he htake).rooms
          exact ⟨hr.clist, hr.nlist, hr.stk, hr.rc, hr.free, hr.pool⟩
        · omega
  · refine Charged.mono (Charged.idle ?_ rfl rfl hmem) (by omega)
    exact ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
      hrooms.pool⟩


/-! ### The visited set the helpers leave alone

None of the charging helpers marks anything, on either arm, which is what
lets the account be read off the closure's own marks. -/

theorem seen_of_error {α : Type} {get : α → PikeSt} {x : POut α}
    {stE st : PikeSt} (he : x = .error stE)
    (h : (outSt get x).seen = st.seen) : stE.seen = st.seen := by
  rw [he] at h
  exact h

theorem seen_ok_id {x : POut PikeSt} {a st : PikeSt} (he : x = .ok a)
    (h : (outSt id x).seen = st.seen) : a.seen = st.seen := by
  rw [he] at h
  exact h

theorem seen_ok_fst {x : POut (PikeSt × Nat)} {a : PikeSt × Nat} {st : PikeSt}
    (he : x = .ok a) (h : (outSt Prod.fst x).seen = st.seen) :
    a.1.seen = st.seen := by
  rw [he] at h
  exact h

theorem pikeDefer_seen {st : PikeSt} {pc h : Nat} {lim : Limits} :
    (outSt id (pikeDefer st pc h lim)).seen = st.seen := by
  simp only [pikeDefer]
  split <;> rfl

theorem pikePark_seen {st : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} : (outSt id (pikePark st intoNext pc h lim)).seen = st.seen := by
  simp only [pikePark]
  split <;> split <;> rfl

theorem pikeDrop_seen {st : PikeSt} {h : Nat} {lim : Limits} :
    (outSt id (pikeDrop st h lim)).seen = st.seen := by
  simp only [pikeDrop]
  repeat' split
  all_goals rfl

theorem pikeTake_fill_seen {lim : Limits} : ∀ (k : Nat) (st : PikeSt),
    (outSt id (pikeTake.fill lim k st)).seen = st.seen := by
  intro k
  induction k with
  | zero =>
      intro st
      rw [pikeTake.fill]
      rfl
  | succ n ih =>
      intro st
      rw [pikeTake.fill]
      split
      · rfl
      · exact ih _

theorem pikeTake_seen {st : PikeSt} {novec : Nat} {lim : Limits} :
    (outSt Prod.fst (pikeTake st novec lim)).seen = st.seen := by
  simp only [pikeTake]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rename_i he
          exact seen_of_error he (pikeTake_fill_seen (lim := lim) novec _)
        · rename_i he
          exact seen_ok_id he (pikeTake_fill_seen (lim := lim) novec _)

theorem pikeWrite_seen {st : PikeSt} {novec h slot : Nat} {value : UInt32}
    {lim : Limits} :
    (outSt Prod.fst (pikeWrite st novec h slot value lim)).seen = st.seen := by
  simp only [pikeWrite]
  split
  · split
    · rfl
    · split
      · rename_i he
        have h1 := seen_of_error he (pikeTake_seen (novec := novec) (lim := lim))
        exact h1
      · rename_i he
        have h1 := seen_ok_fst he (pikeTake_seen (novec := novec) (lim := lim))
        exact h1
  · rfl


/-! ### The charge a refusal was asking for

Every refusal on this path is a pre-charge test failing, so the charge that
was refused is one the meter would have made had the budget had room. `Blown`
puts it back on: some state the account already covers has passed a limit.
Against a certificate the limits dominate that is a contradiction, which is
what turns a certified budget into the absence of a refusal. -/

/-- A limit already passed. -/
def Meter.past (m : Meter) (lim : Limits) : Prop :=
  lim.cost < m.cost ∨ lim.mem < m.peak

/-- What a refused stretch would have reached. -/
def Blown (re : Re) (setup extra : Nat) (lim : Limits) (st : PikeSt) : Prop :=
  ∃ st', Spent re setup extra st st' ∧ st'.m.past lim

theorem Blown.mono {re : Re} {setup a b : Nat} {lim : Limits} {st : PikeSt}
    (h : Blown re setup a lim st) (hle : a ≤ b) : Blown re setup b lim st := by
  obtain ⟨st', hsp, hp⟩ := h
  exact ⟨st', hsp.mono hle, hp⟩

/-- A stretch that ran and then one that was refused. -/
theorem Blown.after {re : Re} {setup a b : Nat} {lim : Limits}
    {st mid : PikeSt} (h : Spent re setup a st mid)
    (hb : Blown re setup b lim mid) : Blown re setup (a + b) lim st := by
  obtain ⟨st', hsp, hp⟩ := hb
  exact ⟨st', h.trans hsp, hp⟩

theorem Blown.ofCharged {re : Re} {setup c : Nat} {lim : Limits}
    {st st' : PikeSt} (h : Charged re setup c st st') (hs : st'.seen = st.seen)
    (hp : st'.m.past lim) : Blown re setup c lim st :=
  ⟨st', Spent.ofCharged h hs, hp⟩

/-- A charge the cost test turned away. In `Nat` the test says exactly that
the meter with the charge on it is past the limit, whether or not the meter
was inside it to begin with. -/
theorem Blown.ofCost {re : Re} {setup : Nat} {lim : Limits} {st : PikeSt}
    (k : Nat) (hrooms : Rooms re st) (hmem : st.m.mem ≤ setup + st.reserved)
    (htest : k > lim.cost - st.m.cost) : Blown re setup k lim st :=
  Blown.ofCharged (Charged.pay k hrooms hmem) rfl (Or.inl (by
    show lim.cost < st.m.cost + k
    omega))

/-- The same reading for a stretch that marked nothing: what it was refused
is pure charge, and the visited set it stands at is the one it started from.
Every charging helper reads this way, and so does a list step at the last
position, which opens no closure — which is what lets the set cleared there
stay unspent. -/
def BlownFlat (re : Re) (setup extra : Nat) (lim : Limits) (st : PikeSt) :
    Prop :=
  ∃ st', Charged re setup extra st st' ∧ st'.seen = st.seen ∧ st'.m.past lim

theorem BlownFlat.blown {re : Re} {setup e : Nat} {lim : Limits} {st : PikeSt}
    (h : BlownFlat re setup e lim st) : Blown re setup e lim st := by
  obtain ⟨st', hc, hs, hp⟩ := h
  exact ⟨st', Spent.ofCharged hc hs, hp⟩

theorem BlownFlat.mono {re : Re} {setup a b : Nat} {lim : Limits} {st : PikeSt}
    (h : BlownFlat re setup a lim st) (hle : a ≤ b) :
    BlownFlat re setup b lim st := by
  obtain ⟨st', hc, hs, hp⟩ := h
  exact ⟨st', hc.mono hle, hs, hp⟩

theorem BlownFlat.after {re : Re} {setup a b : Nat} {lim : Limits}
    {st mid : PikeSt} (h : Charged re setup a st mid) (hs : mid.seen = st.seen)
    (hb : BlownFlat re setup b lim mid) : BlownFlat re setup (a + b) lim st := by
  obtain ⟨st', hc, hs', hp⟩ := hb
  exact ⟨st', h.trans hc, hs'.trans hs, hp⟩

theorem BlownFlat.ofCharged {re : Re} {setup c : Nat} {lim : Limits}
    {st st' : PikeSt} (h : Charged re setup c st st') (hs : st'.seen = st.seen)
    (hp : st'.m.past lim) : BlownFlat re setup c lim st :=
  ⟨st', h, hs, hp⟩

theorem BlownFlat.ofCost {re : Re} {setup : Nat} {lim : Limits} {st : PikeSt}
    (k : Nat) (hrooms : Rooms re st) (hmem : st.m.mem ≤ setup + st.reserved)
    (htest : k > lim.cost - st.m.cost) : BlownFlat re setup k lim st :=
  BlownFlat.ofCharged (Charged.pay k hrooms hmem) rfl (Or.inl (by
    show lim.cost < st.m.cost + k
    omega))

/-- The growth schedule's step, refused. Neither test can be blamed on the
clamp — the array is inside its own entry bound, and the declared maximum is
above twice that — so what was asked for is the capacity the schedule means
to take, weighed by the same three inequalities a step that ran satisfies. -/
theorem chargeGrow_refused {oldcap len esize maxv claim : Nat} {m : Meter}
    {lim : Limits} (hgm : growMin ≤ maxv) (hclaim : growFactor * claim ≤ maxv)
    (hlen : len < claim)
    (h : chargeGrow oldcap len esize maxv m lim = none) :
    ∃ (m' : Meter) (cap : Nat), cap ≤ capFor claim ∧ oldcap ≤ cap ∧
      m'.cost + 3 * (oldcap * esize) ≤ m.cost + 3 * (cap * esize) ∧
      m'.mem + oldcap * esize = m.mem + cap * esize ∧
      m'.peak + 2 * (oldcap * esize) ≤
        max (m.peak + 2 * (oldcap * esize)) (m.mem + 2 * (cap * esize)) ∧
      (lim.cost < m'.cost ∨ lim.mem < m'.peak) := by
  have hclaim0 : claim ≠ 0 := by omega
  simp only [capFor, if_neg hclaim0, growMin, growFactor]
  simp only [growMin, growFactor] at hgm hclaim
  simp only [chargeGrow, growMin, growFactor] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlt
    split at h
    · omega
    · rename_i hmax
      have hdouble : min maxv (max 4 (oldcap * 2)) = max 4 (oldcap * 2) := by
        omega
      have hstep : 2 * oldcap ≤ max 4 (oldcap * 2) := by omega
      have hprod : 2 * (oldcap * esize) ≤ max 4 (oldcap * 2) * esize := by
        have := Nat.mul_le_mul_right esize hstep
        rwa [Nat.mul_assoc] at this
      have hwidth : min maxv (max 4 (oldcap * 2)) * esize =
          max 4 (oldcap * 2) * esize := by rw [hdouble]
      refine ⟨⟨m.cost + (min maxv (max 4 (oldcap * 2)) * esize + oldcap * esize),
        m.mem + min maxv (max 4 (oldcap * 2)) * esize - oldcap * esize,
        max m.peak (m.mem + min maxv (max 4 (oldcap * 2)) * esize)⟩,
        min maxv (max 4 (oldcap * 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hdouble]; omega
      · rw [hdouble]; omega
      · show m.cost + _ + _ ≤ _
        rw [hdouble]
        omega
      · show m.mem + _ - _ + _ = _
        rw [hdouble]
        omega
      · show max m.peak _ + _ ≤ _
        omega
      · split at h
        · rename_i hmemtest
          refine Or.inr ?_
          show lim.mem < max m.peak (m.mem + min maxv (max 4 (oldcap * 2)) * esize)
          omega
        · rename_i hmemtest
          split at h
          · rename_i hcosttest
            refine Or.inl ?_
            show lim.cost < m.cost +
              (min maxv (max 4 (oldcap * 2)) * esize + oldcap * esize)
            omega
          · exact absurd h (by simp)


/-! ### What each helper's refusal was asking for -/

/-- The block table stays well below the declared maximum, so `pike_take`'s
own ceiling is never what turns a run away. -/
theorem table_lt_maxBlocks {re : Re} (hwf : ReWf re) :
    re.code.size * 4 + 2 < maxBlocks := by
  have hc := hwf.coded
  simp only [maxBlocks, liveBlocks, growMin, growFactor, maxCode,
    maxNodes] at *
  omega

theorem pikeDefer_refused {re : Re} {st stE : PikeSt} {pc h setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hsize : st.stk.size < re.code.size * 2)
    (he : pikeDefer st pc h lim = .error stE) : BlownFlat re setup 0 lim st := by
  obtain ⟨-, ⟨hgm, hcl⟩, -, -⟩ := pikeSchedule hwf
  simp only [pikeDefer] at he
  split at he
  · rename_i hg
    obtain ⟨m', cap, hcap, hold, hcost, hmem', hpeak, hpast⟩ :=
      chargeGrow_refused hgm hcl hsize hg
    refine BlownFlat.ofCharged (st' := { st with
        m := m'
        stkCap := cap
        stk := st.stk.push ⟨pc, h⟩ }) (charged_of_grow (esize := thSize)
      (rest := (st.clistCap + st.nlistCap) * thSize +
        (st.rcCap + st.freeCap + st.poolCap) * regSize)
      ⟨hrooms.clist, hrooms.nlist, hcap, hrooms.rc, hrooms.free, hrooms.pool⟩
      hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
      (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost hmem'
      hpeak) rfl hpast
  · exact absurd he (by simp)

theorem pikePark_refused {re : Re} {st stE : PikeSt} {intoNext : Bool}
    {pc h setup : Nat} {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hsize : (parkList intoNext st).size < re.code.size)
    (he : pikePark st intoNext pc h lim = .error stE) :
    BlownFlat re setup 0 lim st := by
  obtain ⟨⟨hgm, hcl⟩, -, -, -⟩ := pikeSchedule hwf
  simp only [parkList] at hsize
  simp only [pikePark] at he
  split at he
  · rename_i hin
    rw [if_pos hin] at hsize
    split at he
    · rename_i hg
      obtain ⟨m', cap, hcap, hold, hcost, hmem', hpeak, hpast⟩ :=
        chargeGrow_refused hgm hcl hsize hg
      refine BlownFlat.ofCharged (st' := { st with
          m := m'
          nlistCap := cap
          nlist := st.nlist.push ⟨pc, h⟩ }) (charged_of_grow (esize := thSize)
        (rest := (st.clistCap + st.stkCap) * thSize +
          (st.rcCap + st.freeCap + st.poolCap) * regSize)
        ⟨hrooms.clist, hcap, hrooms.stk, hrooms.rc, hrooms.free, hrooms.pool⟩
        hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
        (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
        hmem' hpeak) rfl hpast
    · exact absurd he (by simp)
  · rename_i hin
    rw [if_neg hin] at hsize
    split at he
    · rename_i hg
      obtain ⟨m', cap, hcap, hold, hcost, hmem', hpeak, hpast⟩ :=
        chargeGrow_refused hgm hcl hsize hg
      refine BlownFlat.ofCharged (st' := { st with
          m := m'
          clistCap := cap
          clist := st.clist.push ⟨pc, h⟩ }) (charged_of_grow (esize := thSize)
        (rest := (st.nlistCap + st.stkCap) * thSize +
          (st.rcCap + st.freeCap + st.poolCap) * regSize)
        ⟨hcap, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free, hrooms.pool⟩
        hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
        (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
        hmem' hpeak) rfl hpast
    · exact absurd he (by simp)

theorem pikeDrop_refused {re : Re} {st stE : PikeSt} {h setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hsize : st.rc[h]! ≤ 1 → st.free.size < re.code.size * 4 + 2)
    (he : pikeDrop st h lim = .error stE) : BlownFlat re setup 0 lim st := by
  obtain ⟨-, -, ⟨hgm, hcl⟩, -⟩ := pikeSchedule hwf
  simp only [pikeDrop] at he
  split at he
  · exact absurd he (by simp)
  · split at he
    · rename_i hzero
      split at he
      · rename_i hg
        obtain ⟨m', cap, hcap, hold, hcost, hmem', hpeak, hpast⟩ :=
          chargeGrow_refused hgm hcl
            (hsize (by simp only [beq_iff_eq] at hzero; omega)) hg
        refine BlownFlat.ofCharged (st' := { st with
            m := m'
            freeCap := cap
            rc := st.rc.set! h (st.rc[h]! - 1)
            free := st.free.push h }) (charged_of_grow (esize := regSize)
          (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
            (st.rcCap + st.poolCap) * regSize)
          ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hcap,
            hrooms.pool⟩
          hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
          (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
          hmem' hpeak) rfl hpast
      · exact absurd he (by simp)
    · exact absurd he (by simp)

theorem pikeTake_fill_refused {re : Re} {setup : Nat} {lim : Limits}
    (hwf : ReWf re) : ∀ (k : Nat) (st stE : PikeSt), Rooms re st →
      st.m.mem ≤ setup + st.reserved →
      st.pool.size + k ≤ (re.code.size * 4 + 2) * re.novec →
      pikeTake.fill lim k st = .error stE → BlownFlat re setup 0 lim st := by
  obtain ⟨-, -, -, ⟨hgm, hcl⟩⟩ := pikeSchedule hwf
  intro k
  induction k with
  | zero =>
      intro st stE _ _ _ he
      rw [pikeTake.fill] at he
      exact absurd he (by simp)
  | succ n ih =>
      intro st stE hrooms hmem hpool he
      rw [pikeTake.fill] at he
      split at he
      · rename_i hg
        obtain ⟨m', cap, hcap, hold, hcost, hmem', hpeak, hpast⟩ :=
          chargeGrow_refused hgm hcl (by omega) hg
        refine BlownFlat.ofCharged (st' := { st with
            m := m'
            poolCap := cap
            pool := st.pool.push unset32 }) (charged_of_grow (esize := regSize)
          (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
            (st.rcCap + st.freeCap) * regSize)
          ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
            hcap⟩
          hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
          (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
          hmem' hpeak) rfl hpast
      · rename_i mm cap hg
        obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
          chargeGrow_capFor hgm hcl (by omega) hrooms.pool hg
        have hstep : Charged re setup 0 st
            { st with
              m := mm, poolCap := cap, pool := st.pool.push unset32 } :=
          charged_of_grow (esize := regSize)
            (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
              (st.rcCap + st.freeCap) * regSize)
            ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
              hcap⟩
            hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
            (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
            hmem' hpeak
        exact BlownFlat.mono
          (BlownFlat.after hstep rfl
            (ih _ _ hstep.rooms hstep.held (by simp; omega) he)) (by omega)

theorem pikeTake_refused {re : Re} {st stE : PikeSt} {novec setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hrc : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2)
    (hpool : st.free.size = 0 →
      st.pool.size + novec ≤ (re.code.size * 4 + 2) * re.novec)
    (he : pikeTake st novec lim = .error stE) : BlownFlat re setup 0 lim st := by
  obtain ⟨-, -, ⟨hgm, hcl⟩, -⟩ := pikeSchedule hwf
  have hmb := table_lt_maxBlocks hwf
  simp only [pikeTake] at he
  split at he
  · exact absurd he (by simp)
  · rename_i hempty
    have hzero : st.free.size = 0 := by
      rcases Nat.eq_zero_or_pos st.free.size with hz | hp
      · exact hz
      · exact absurd (by simpa using hp) hempty
    split at he
    · rename_i hcapfull
      have := hrc hzero
      omega
    · split at he
      · rename_i hg
        obtain ⟨m', cap, hcap, hold, hcost, hmem', hpeak, hpast⟩ :=
          chargeGrow_refused hgm hcl (hrc hzero) hg
        refine BlownFlat.ofCharged (st' := { st with
            m := m'
            rcCap := cap
            rc := st.rc.push 1 }) (charged_of_grow (esize := regSize)
          (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
            (st.freeCap + st.poolCap) * regSize)
          ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hcap, hrooms.free,
            hrooms.pool⟩
          hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
          (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
          hmem' hpeak) rfl hpast
      · rename_i mm cap hg
        obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
          chargeGrow_capFor hgm hcl (hrc hzero) hrooms.rc hg
        have hstep : Charged re setup 0 st
            { st with m := mm, rcCap := cap, rc := st.rc.push 1 } :=
          charged_of_grow (esize := regSize)
            (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
              (st.freeCap + st.poolCap) * regSize)
            ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hcap, hrooms.free,
              hrooms.pool⟩
            hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
            (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
            hmem' hpeak
        split at he
        · rename_i hf
          exact BlownFlat.mono
            (BlownFlat.after hstep rfl
              (pikeTake_fill_refused hwf novec _ _ hstep.rooms hstep.held
                (by simpa using hpool hzero) hf)) (by omega)
        · exact absurd he (by simp)

theorem pikeWrite_refused {re : Re} {st stE : PikeSt}
    {novec h slot setup : Nat} {value : UInt32} {lim : Limits} (hwf : ReWf re)
    (hrooms : Rooms re st) (hmem : st.m.mem ≤ setup + st.reserved)
    (hrc : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2)
    (hpool : st.free.size = 0 →
      st.pool.size + novec ≤ (re.code.size * 4 + 2) * re.novec)
    (he : pikeWrite st novec h slot value lim = .error stE) :
    BlownFlat re setup (novec * regSize) lim st := by
  simp only [pikeWrite] at he
  split at he
  · split at he
    · rename_i htest
      exact BlownFlat.ofCost _ hrooms hmem htest
    · have hpaid := Charged.pay (re := re) (setup := setup) (novec * regSize)
        hrooms hmem
      split at he
      · rename_i hf
        exact BlownFlat.mono
          (BlownFlat.after hpaid rfl
            (pikeTake_refused hwf hpaid.rooms hpaid.held hrc hpool hf))
          (by omega)
      · exact absurd he (by simp)
  · exact absurd he (by simp)


/-! ### Carrying the attempt through a stretch -/

theorem Spent.ofState {re : Re} {setup c : Nat} {st st' out : PikeSt}
    (h : Spent re setup c st' out) (hm : st'.m = st.m)
    (hres : st'.reserved = st.reserved) (hseen : st'.seen = st.seen) :
    Spent re setup c st out := by
  obtain ⟨sp, hc, hle⟩ := h
  exact ⟨sp, Charged.ofState hc hm hres, by rw [← hseen]; exact hle⟩

theorem Blown.ofState {re : Re} {setup c : Nat} {lim : Limits}
    {st st' : PikeSt} (h : Blown re setup c lim st') (hm : st'.m = st.m)
    (hres : st'.reserved = st.reserved) (hseen : st'.seen = st.seen) :
    Blown re setup c lim st := by
  obtain ⟨out, hsp, hp⟩ := h
  exact ⟨out, hsp.ofState hm hres hseen, hp⟩

/-- The account through a mark, for a stretch that was refused. -/
theorem blown_of_mark {re : Re} {setup c e : Nat} {lim : Limits}
    {st mid : PikeSt} {pc : Nat} (hpc : pc < st.seen.size)
    (hf : st.seen[pc]! = false) (hseen : mid.seen = st.seen.set! pc true)
    (h : Charged re setup c st mid) (hc : c + e ≤ markWeight re pc)
    (hb : Blown re setup e lim mid) : Blown re setup 0 lim st := by
  obtain ⟨st', ⟨s', hc', hle⟩, hpast⟩ := hb
  refine ⟨st', ⟨c + s', h.trans hc', ?_⟩, hpast⟩
  rw [hseen] at hle
  have hset := closureLeft_set (re := re) hpc hf
  omega

/-- What a stretch attempted, whichever way it ended: the state it hands back
is inside the account, and if it was refused the charge it was refused is
inside it too. -/
def Tried (re : Re) (setup extra : Nat) (lim : Limits) (st : PikeSt)
    {α : Type} (get : α → PikeSt) (x : POut α) : Prop :=
  Spent re setup extra st (outSt get x) ∧
    (∀ stE, x = .error stE → Blown re setup extra lim st)

theorem Tried.mono {re : Re} {setup a b : Nat} {lim : Limits} {st : PikeSt}
    {α : Type} {get : α → PikeSt} {x : POut α}
    (h : Tried re setup a lim st get x) (hle : a ≤ b) :
    Tried re setup b lim st get x :=
  ⟨h.1.mono hle, fun stE he => (h.2 stE he).mono hle⟩

/-- A stretch that ran, and then one that may not have. -/
theorem Tried.after {re : Re} {setup a b : Nat} {lim : Limits}
    {st mid : PikeSt} {α : Type} {get : α → PikeSt} {x : POut α}
    (h : Spent re setup a st mid) (ht : Tried re setup b lim mid get x) :
    Tried re setup (a + b) lim st get x :=
  ⟨h.trans ht.1, fun stE he => Blown.after h (ht.2 stE he)⟩

theorem Tried.ofOk {α : Type} {get : α → PikeSt} {a : α} {re : Re}
    {setup c : Nat} {lim : Limits} {st : PikeSt}
    (hsp : Spent re setup c st (get a)) :
    Tried re setup c lim st get (Except.ok a) :=
  ⟨hsp, fun stE he => absurd he (by simp)⟩

theorem Tried.error {α : Type} {get : α → PikeSt} {re : Re} {setup c : Nat}
    {lim : Limits} {st stE : PikeSt} (hsp : Spent re setup c st stE)
    (hb : Blown re setup c lim st) :
    Tried re setup c lim st get (Except.error stE) :=
  ⟨hsp, fun stE' he => by
    simp only [Except.error.injEq] at he
    subst he
    exact hb⟩

/-- The account through a mark, carried over a stretch either way. -/
theorem tried_of_mark {re : Re} {setup c : Nat} {lim : Limits}
    {st mid : PikeSt} {pc : Nat} {α : Type} {get : α → PikeSt} {x : POut α}
    (hpc : pc < st.seen.size) (hf : st.seen[pc]! = false)
    (hseen : mid.seen = st.seen.set! pc true)
    (h : Charged re setup c st mid) (hc : c ≤ markWeight re pc)
    (ht : Tried re setup 0 lim mid get x) : Tried re setup 0 lim st get x :=
  ⟨spent_of_mark hpc hf hseen h hc ht.1,
    fun stE he => blown_of_mark hpc hf hseen h (by omega) (ht.2 stE he)⟩

/-- And an iteration that marked nothing. -/
theorem tried_of_idle {re : Re} {setup : Nat} {lim : Limits} {st mid : PikeSt}
    {α : Type} {get : α → PikeSt} {x : POut α}
    (h : Charged re setup 0 st mid) (hseen : mid.seen = st.seen)
    (ht : Tried re setup 0 lim mid get x) : Tried re setup 0 lim st get x :=
  Tried.mono (Tried.after (Spent.ofCharged h hseen) ht) (by omega)


/-! ### What a closure build spends -/

/-- A block someone is holding is not on the free list, so the free list has
room for one more — which is all a drop about to free a block needs. -/
theorem free_room {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {h bound : Nat} {rest : List Nat}
    (how : Owned novec rc free pool (h :: rest)) (hb : rc.size ≤ bound) :
    free.size < bound := by
  have hlt : h < rc.size := how.reach h List.mem_cons_self
  have hc := how.count h hlt
  have hcnt : 1 ≤ (h :: rest).count h := by
    rw [List.count_cons]
    simp
  have hne : rc[h]! ≠ 0 := by omega
  have hz : free.toList.count h = 0 := by
    rcases Nat.eq_zero_or_pos (free.toList.count h) with hz | hp
    · exact hz
    · exact absurd ((how.onFree h hlt).mpr hp) hne
  have hfl := how.free_lt hlt hz
  omega

/-- And the pool has room for one more block, when the handles in reach are
what the table is bounded by: the table's length is the pool's layout. -/
theorem take_room {novec : Nat} {rc free : Array Nat} {pool : Array UInt32}
    {live : List Nat} {bound : Nat} (how : Owned novec rc free pool live)
    (hlen : live.length ≤ bound) (hz : free.size = 0) :
    rc.size ≤ bound ∧ pool.size + novec ≤ (bound + 1) * novec := by
  have h1 := how.size_le
  rw [hz] at h1
  refine ⟨by omega, ?_⟩
  rw [how.blocks, ← Nat.succ_mul]
  exact Nat.mul_le_mul_right novec (by omega)

/-- What a closure build must know about the state it stands on for its
charges to sit inside BOUNDS.md section 9's per-position price. The dedup
facts are there so the mark lands, the ownership so a growth is weighed
against the handles in reach, and the three counts so no array is ever asked
for more than the schedule's answer at its own entry bound. -/
structure AddOk (re : Re) (intoNext : Bool) (ext : List Nat) (setup : Nat)
    (st : PikeSt) : Prop where
  seenSize : st.seen.size = re.code.size
  inRange : listInRange re st.stk
  rooms : Rooms re st
  held : st.m.mem ≤ setup + st.reserved
  owned : Owned re.novec st.rc st.free st.pool (buildLive intoNext st ext)
  stack : st.stk.size + 2 * unmarked st.seen ≤ re.code.size * 2 + 1
  parked : (parkList intoNext st).size + unmarked st.seen ≤ re.code.size
  reach : addMeasure intoNext st + ext.length ≤ re.code.size * 4
  table : st.rc.size ≤ re.code.size * 4 + 2


set_option maxHeartbeats 4000000 in
/-- One closure build, attempted. Every iteration either pops a pc the visited
set has already admitted — which charges nothing — or marks a fresh one, and
the weight of that mark is exactly what the iteration then spends: the unit
the loop charges for the instruction, and at a `Save` the copy-on-write it
can force. So a build never spends more than the pcs it marked were worth, a
refusal spends less, and the charge that refusal was asking for fits inside
the same weight.

The fuel premise is what keeps the second reading honest. `pike_add`'s loop
answers `error` on an exhausted fuel as well as on a refused charge, and the
budget has nothing to say about the first; the premise is the termination
measure of `PikeTermination.lean`, which falls by at least one per iteration
against a fuel that falls by one, and which `pike_add`'s own seed clears. -/
theorem pikeAdd_go_tried (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (intoNext : Bool) (pos setup : Nat) (ext : List Nat) :
    ∀ (fuel : Nat) (st : PikeSt), AddOk re intoNext ext setup st →
      st.stk.size + 2 * unmarked st.seen < fuel →
      Tried re setup 0 lim st id
        (pikeAdd.go re s mo lim intoNext pos fuel st) := by
  intro fuel
  induction fuel with
  | zero =>
      intro st _ hfuel
      exact absurd hfuel (Nat.not_lt_zero _)
  | succ f ih =>
      intro st hok hfuel
      have hC := hwf.sized
      have hstep : ∀ stB : PikeSt, AddOk re intoNext ext setup stB →
          stB.stk.size + 2 * unmarked stB.seen < f →
          Spent re setup 0 st stB →
          Tried re setup 0 lim st id
            (pikeAdd.go re s mo lim intoNext pos f stB) :=
        fun stB hokB hfB hsp =>
          Tried.mono (Tried.after hsp (ih stB hokB hfB)) (by omega)
      simp only [pikeAdd.go]
      split
      · exact Tried.ofOk (Spent.refl hok.rooms hok.held)
      · rename_i hne
        have hpos : 0 < st.stk.size :=
          Nat.pos_of_ne_zero (fun hz => hne (by simp [hz]))
        have hpcv : st.stk.back!.pc < re.code.size :=
          listInRange_back hok.inRange (by omega)
        have hpop : listInRange re st.stk.pop := listInRange_pop hok.inRange
        have htgt := hwf.targets _ hpcv
        have hflight := owned_pop (intoNext := intoNext) (ext := ext) hpos hok.owned
        have hroomsP : Rooms re { st with stk := st.stk.pop } :=
          ⟨hok.rooms.clist, hok.rooms.nlist, hok.rooms.stk, hok.rooms.rc,
            hok.rooms.free, hok.rooms.pool⟩
        split
        · -- Already visited: the pop pays for the iteration and nothing is
          -- charged, so the account does not move.
          have hownP : Owned re.novec ({ st with stk := st.stk.pop } : PikeSt).rc
              ({ st with stk := st.stk.pop } : PikeSt).free
              ({ st with stk := st.stk.pop } : PikeSt).pool
              (st.stk.back!.h ::
                buildLive intoNext { st with stk := st.stk.pop } ext) := hflight
          have hdropP : Charged re setup 0 st
              (outSt id (pikeDrop { st with stk := st.stk.pop }
                st.stk.back!.h lim)) :=
            Charged.ofState (pikeDrop_charged (setup := setup)
              (h := st.stk.back!.h) (lim := lim) hwf hroomsP hok.held
              (fun _ => free_room hownP hok.table)) rfl rfl
          have hsnP := pikeDrop_seen (st := { st with stk := st.stk.pop })
            (h := st.stk.back!.h) (lim := lim)
          split
          · rename_i stE he
            have hchE : Charged re setup 0 st stE := charged_of_error he hdropP
            refine Tried.error (spent_of_idle hchE (seen_of_error he hsnP)
              (Spent.refl hchE.rooms hchE.held)) ?_
            exact Blown.ofState (pikeDrop_refused (setup := setup)
              (h := st.stk.back!.h) (lim := lim) hwf hroomsP hok.held
              (fun _ => free_room hownP hok.table) he).blown rfl rfl rfl
          · rename_i stB hb
            have hchB : Charged re setup 0 st stB := charged_ok_id hb hdropP
            have hsnB : stB.seen = st.seen := seen_ok_id hb hsnP
            obtain ⟨hstkB, -⟩ := pikeDrop_ok hb
            obtain ⟨hclB, hnlB⟩ := pikeDrop_lists hb
            obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hb
            have hparkB : parkList intoNext stB = parkList intoNext st := by
              rw [parkList_eq hclB hnlB]
              rfl
            have hstkB' : stB.stk = st.stk.pop := hstkB
            refine hstep stB ⟨?_, ?_, hchB.rooms, hchB.held, ?_, ?_, ?_, ?_, ?_⟩
              ?_ (spent_of_idle hchB hsnB (Spent.refl hchB.rooms hchB.held))
            · rw [hsnB]; exact hok.seenSize
            · rw [hstkB']; exact hpop
            · exact drop_owned hb hownP
            · rw [hstkB', hsnB, Array.size_pop]
              have h1 := hok.stack
              omega
            · rw [hparkB, hsnB]
              exact hok.parked
            · simp only [addMeasure]
              rw [hstkB', hsnB, hparkB, Array.size_pop]
              have h1 := hok.reach
              simp only [addMeasure] at h1
              omega
            · rw [hrcB]; exact hok.table
            · rw [hstkB', hsnB, Array.size_pop]
              omega
        · -- A fresh pc: the mark pays for what the arm charges.
          rename_i hseenF
          have hfalse : st.seen[st.stk.back!.pc]! = false := by simpa using hseenF
          have hpcs : st.stk.back!.pc < st.seen.size := by
            rw [hok.seenSize]; exact hpcv
          have hu1 : unmarked (st.seen.set! st.stk.back!.pc true) + 1 =
              unmarked st.seen := unmarked_set_lt hpcs hfalse
          have hw1 : 1 ≤ markWeight re st.stk.back!.pc := by
            simp only [markWeight]; omega
          have hstop : ∀ (stE : PikeSt) (c : Nat),
              stE.seen = st.seen.set! st.stk.back!.pc true →
              Charged re setup c st stE → c ≤ markWeight re st.stk.back!.pc →
              Spent re setup 0 st stE :=
            fun stE c hse hce hcw =>
              spent_of_mark hpcs hfalse hse hce hcw
                (Spent.refl hce.rooms hce.held)
          have hfinish : ∀ (stB : PikeSt) (c : Nat),
              AddOk re intoNext ext setup stB →
              stB.stk.size + 2 * unmarked stB.seen < f →
              stB.seen = st.seen.set! st.stk.back!.pc true →
              Charged re setup c st stB → c ≤ markWeight re st.stk.back!.pc →
              Tried re setup 0 lim st id
                (pikeAdd.go re s mo lim intoNext pos f stB) :=
            fun stB c hokB hfB hse hce hcw =>
              hstep stB hokB hfB (spent_of_mark hpcs hfalse hse hce hcw
                (Spent.refl hce.rooms hce.held))
          split
          · -- The mark landed, and then the unit it costs was refused.
            rename_i htest
            have hrefused : ∀ stM : PikeSt, stM.m = st.m →
                stM.reserved = st.reserved →
                stM.seen = st.seen.set! st.stk.back!.pc true → Rooms re stM →
                1 > lim.cost - stM.m.cost →
                Tried re setup 0 lim st id (Except.error stM) := by
              intro stM hm hres hse hrM hcost
              have hchM : Charged re setup 0 st stM :=
                Charged.idle hrM hres hm hok.held
              refine Tried.error (hstop stM 0 hse hchM (Nat.zero_le _)) ?_
              exact blown_of_mark hpcs hfalse hse hchM (by omega)
                (Blown.ofCost 1 hrM (by rw [hm, hres]; exact hok.held) hcost)
            refine hrefused _ rfl rfl rfl ?_ htest
            exact ⟨hok.rooms.clist, hok.rooms.nlist, hok.rooms.stk,
              hok.rooms.rc, hok.rooms.free, hok.rooms.pool⟩
          · -- The mark's own unit, charged against the weight the mark has
            -- just released.
            have hmarkC : Charged re setup 1 st
                { st with
                  stk := st.stk.pop
                  seen := st.seen.set! st.stk.back!.pc true
                  m := { st.m with cost := st.m.cost + 1 } } := by
              refine ⟨?_, ⟨hok.rooms.clist, hok.rooms.nlist, hok.rooms.stk,
                hok.rooms.rc, hok.rooms.free, hok.rooms.pool⟩, Nat.le_refl _,
                hok.held, rfl, Nat.le_max_left _ _⟩
              show st.m.cost + 1 + 3 * st.reserved ≤
                st.m.cost + 3 * st.reserved + 1
              omega
            have hmarkR : Charged re setup 1 st
                { st with
                  stk := st.stk.pop
                  seen := st.seen.set! st.stk.back!.pc true
                  m := { st.m with cost := st.m.cost + 1 }
                  rc := st.rc.set! st.stk.back!.h
                    (st.rc[st.stk.back!.h]! + 1) } := by
              refine ⟨?_, ⟨hok.rooms.clist, hok.rooms.nlist, hok.rooms.stk,
                hok.rooms.rc, hok.rooms.free, hok.rooms.pool⟩, Nat.le_refl _,
                hok.held, rfl, Nat.le_max_left _ _⟩
              show st.m.cost + 1 + 3 * st.reserved ≤
                st.m.cost + 3 * st.reserved + 1
              omega
            -- The five shapes an arm can take, each read off the marked state
            -- through the fields the reckoning looks at.
            have harmDrop : ∀ (stA : PikeSt) (hh c : Nat),
                Charged re setup c st stA →
                c ≤ markWeight re st.stk.back!.pc →
                stA.stk.size ≤ st.stk.size → listInRange re stA.stk →
                stA.seen = st.seen.set! st.stk.back!.pc true →
                parkList intoNext stA = parkList intoNext st →
                Owned re.novec stA.rc stA.free stA.pool
                  (hh :: buildLive intoNext stA ext) →
                stA.rc.size ≤ re.code.size * 4 + 2 →
                stA.stk.size + 2 * unmarked stA.seen < f →
                (∀ stE, pikeDrop stA hh lim = .error stE →
                  Tried re setup 0 lim st id (Except.error stE)) ∧
                (∀ stB, pikeDrop stA hh lim = .ok stB →
                  Tried re setup 0 lim st id
                    (pikeAdd.go re s mo lim intoNext pos f stB)) := by
              intro stA hh c hchA hcw hstkA hrangeA hseenA hparkA hownA htabA hfA
              have hch := pikeDrop_charged (setup := setup) (h := hh) (lim := lim)
                hwf hchA.rooms hchA.held (fun _ => free_room hownA htabA)
              have hsn := pikeDrop_seen (st := stA) (h := hh) (lim := lim)
              refine ⟨?_, ?_⟩
              · intro stE he
                refine Tried.error ?_ ?_
                · refine hstop stE (c + 0) ?_
                    (hchA.trans (charged_of_error he hch)) (by omega)
                  rw [seen_of_error he hsn]
                  exact hseenA
                · exact blown_of_mark hpcs hfalse hseenA hchA (by omega)
                    (pikeDrop_refused (setup := setup) (h := hh) (lim := lim) hwf
                      hchA.rooms hchA.held
                      (fun _ => free_room hownA htabA) he).blown
              · intro stB hb
                have hchB : Charged re setup (c + 0) st stB :=
                  hchA.trans (charged_ok_id hb hch)
                have hsnB : stB.seen = stA.seen := seen_ok_id hb hsn
                obtain ⟨hstkB, -⟩ := pikeDrop_ok hb
                obtain ⟨hclB, hnlB⟩ := pikeDrop_lists hb
                obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hb
                have hparkB : parkList intoNext stB = parkList intoNext st := by
                  rw [parkList_eq hclB hnlB]; exact hparkA
                refine hfinish stB (c + 0)
                  ⟨?_, ?_, hchB.rooms, hchB.held, ?_, ?_, ?_, ?_, ?_⟩ ?_
                  (by rw [hsnB]; exact hseenA) hchB (by omega)
                · rw [hsnB, hseenA, Array.size_set!]; exact hok.seenSize
                · rw [hstkB]; exact hrangeA
                · exact drop_owned hb hownA
                · rw [hstkB, hsnB, hseenA]
                  have h1 := hok.stack
                  omega
                · rw [hparkB, hsnB, hseenA]
                  have h1 := hok.parked
                  omega
                · simp only [addMeasure]
                  rw [hstkB, hsnB, hseenA, hparkB]
                  have h1 := hok.reach
                  simp only [addMeasure] at h1
                  omega
                · rw [hrcB]; exact htabA
                · rw [hstkB, hsnB]; exact hfA
            have harmPark : ∀ (stA : PikeSt) (pcT hh c : Nat),
                Charged re setup c st stA →
                c ≤ markWeight re st.stk.back!.pc →
                stA.stk.size ≤ st.stk.size → listInRange re stA.stk →
                stA.seen = st.seen.set! st.stk.back!.pc true →
                parkList intoNext stA = parkList intoNext st →
                Owned re.novec stA.rc stA.free stA.pool
                  (hh :: buildLive intoNext stA ext) →
                stA.rc.size ≤ re.code.size * 4 + 2 →
                pcT < re.code.size →
                stA.stk.size + 2 * unmarked stA.seen < f →
                (∀ stE, pikePark stA intoNext pcT hh lim = .error stE →
                  Tried re setup 0 lim st id (Except.error stE)) ∧
                (∀ stB, pikePark stA intoNext pcT hh lim = .ok stB →
                  Tried re setup 0 lim st id
                    (pikeAdd.go re s mo lim intoNext pos f stB)) := by
              intro stA pcT hh c hchA hcw hstkA hrangeA hseenA hparkA hownA htabA
                hpcT hfA
              have hsz : (parkList intoNext stA).size < re.code.size := by
                have h1 := hok.parked
                rw [hparkA]
                omega
              have hch := pikePark_charged (setup := setup) (pc := pcT)
                (h := hh) (lim := lim) hwf hchA.rooms hchA.held hsz
              have hsn := pikePark_seen (st := stA) (intoNext := intoNext)
                (pc := pcT) (h := hh) (lim := lim)
              refine ⟨?_, ?_⟩
              · intro stE he
                refine Tried.error ?_ ?_
                · refine hstop stE (c + 0) ?_
                    (hchA.trans (charged_of_error he hch)) (by omega)
                  rw [seen_of_error he hsn]
                  exact hseenA
                · exact blown_of_mark hpcs hfalse hseenA hchA (by omega)
                    (pikePark_refused (setup := setup) (pc := pcT) (h := hh)
                      (lim := lim) hwf hchA.rooms hchA.held hsz he).blown
              · intro stB hb
                have hchB : Charged re setup (c + 0) st stB :=
                  hchA.trans (charged_ok_id hb hch)
                have hsnB : stB.seen = stA.seen := seen_ok_id hb hsn
                obtain ⟨hstkB, -⟩ := pikePark_ok hb
                obtain ⟨hT, hF⟩ := pikePark_lists hb
                obtain ⟨hrcB, -, -⟩ := pikePark_pool hb
                have hparkB : parkList intoNext stB =
                    (parkList intoNext stA).push ⟨pcT, hh⟩ := parkList_push hT hF
                refine hfinish stB (c + 0)
                  ⟨?_, ?_, hchB.rooms, hchB.held, ?_, ?_, ?_, ?_, ?_⟩ ?_
                  (by rw [hsnB]; exact hseenA) hchB (by omega)
                · rw [hsnB, hseenA, Array.size_set!]; exact hok.seenSize
                · rw [hstkB]; exact hrangeA
                · exact park_owned hb hownA
                · rw [hstkB, hsnB, hseenA]
                  have h1 := hok.stack
                  omega
                · rw [hparkB, hsnB, hseenA, Array.size_push, hparkA]
                  have h1 := hok.parked
                  omega
                · simp only [addMeasure]
                  rw [hstkB, hsnB, hseenA, hparkB, Array.size_push, hparkA]
                  have h1 := hok.reach
                  simp only [addMeasure] at h1
                  omega
                · rw [hrcB]; exact htabA
                · rw [hstkB, hsnB]; exact hfA
            have harmDefer : ∀ (stA : PikeSt) (pcT hh c : Nat),
                Charged re setup c st stA →
                c ≤ markWeight re st.stk.back!.pc →
                stA.stk.size ≤ st.stk.size → listInRange re stA.stk →
                stA.seen = st.seen.set! st.stk.back!.pc true →
                parkList intoNext stA = parkList intoNext st →
                Owned re.novec stA.rc stA.free stA.pool
                  (hh :: buildLive intoNext stA ext) →
                stA.rc.size ≤ re.code.size * 4 + 2 →
                pcT < re.code.size →
                stA.stk.size + 1 + 2 * unmarked stA.seen < f →
                (∀ stE, pikeDefer stA pcT hh lim = .error stE →
                  Tried re setup 0 lim st id (Except.error stE)) ∧
                (∀ stB, pikeDefer stA pcT hh lim = .ok stB →
                  Tried re setup 0 lim st id
                    (pikeAdd.go re s mo lim intoNext pos f stB)) := by
              intro stA pcT hh c hchA hcw hstkA hrangeA hseenA hparkA hownA htabA
                hpcT hfA
              have hsz : stA.stk.size < re.code.size * 2 := by
                have h1 := hok.stack
                omega
              have hch := pikeDefer_charged (setup := setup) (pc := pcT)
                (h := hh) (lim := lim) hwf hchA.rooms hchA.held hsz
              have hsn := pikeDefer_seen (st := stA) (pc := pcT) (h := hh)
                (lim := lim)
              refine ⟨?_, ?_⟩
              · intro stE he
                refine Tried.error ?_ ?_
                · refine hstop stE (c + 0) ?_
                    (hchA.trans (charged_of_error he hch)) (by omega)
                  rw [seen_of_error he hsn]
                  exact hseenA
                · exact blown_of_mark hpcs hfalse hseenA hchA (by omega)
                    (pikeDefer_refused (setup := setup) (pc := pcT) (h := hh)
                      (lim := lim) hwf hchA.rooms hchA.held hsz he).blown
              · intro stB hb
                have hchB : Charged re setup (c + 0) st stB :=
                  hchA.trans (charged_ok_id hb hch)
                have hsnB : stB.seen = stA.seen := seen_ok_id hb hsn
                obtain ⟨hstkB, -⟩ := pikeDefer_ok hb
                obtain ⟨hclB, hnlB⟩ := pikeDefer_lists hb
                obtain ⟨hrcB, -, -⟩ := pikeDefer_pool hb
                have hparkB : parkList intoNext stB = parkList intoNext st := by
                  rw [parkList_eq hclB hnlB]; exact hparkA
                refine hfinish stB (c + 0)
                  ⟨?_, ?_, hchB.rooms, hchB.held, ?_, ?_, ?_, ?_, ?_⟩ ?_
                  (by rw [hsnB]; exact hseenA) hchB (by omega)
                · rw [hsnB, hseenA, Array.size_set!]; exact hok.seenSize
                · rw [hstkB]; exact listInRange_push hrangeA hpcT
                · exact defer_owned hb hownA
                · rw [hstkB, hsnB, hseenA, Array.size_push]
                  have h1 := hok.stack
                  omega
                · rw [hparkB, hsnB, hseenA]
                  have h1 := hok.parked
                  omega
                · simp only [addMeasure]
                  rw [hstkB, hsnB, hseenA, hparkB, Array.size_push]
                  have h1 := hok.reach
                  simp only [addMeasure] at h1
                  omega
                · rw [hrcB]; exact htabA
                · rw [hstkB, hsnB, Array.size_push]; omega
            have harmFork : ∀ (stR : PikeSt) (q hh c : Nat),
                Charged re setup c st stR →
                c ≤ markWeight re st.stk.back!.pc →
                stR.stk.size + 1 ≤ st.stk.size → listInRange re stR.stk →
                stR.seen = st.seen.set! st.stk.back!.pc true →
                parkList intoNext stR = parkList intoNext st →
                Owned re.novec stR.rc stR.free stR.pool
                  (hh :: hh :: buildLive intoNext stR ext) →
                stR.rc.size ≤ re.code.size * 4 + 2 →
                q < re.code.size →
                stR.stk.size + 2 + 2 * unmarked stR.seen < f →
                (∀ stE, pikeDefer stR q hh lim = .error stE →
                  Tried re setup 0 lim st id (Except.error stE)) ∧
                (∀ stB, pikeDefer stR q hh lim = .ok stB → ∀ p, p < re.code.size →
                  (∀ stE, pikeDefer stB p hh lim = .error stE →
                    Tried re setup 0 lim st id (Except.error stE)) ∧
                  (∀ stD, pikeDefer stB p hh lim = .ok stD →
                    Tried re setup 0 lim st id
                      (pikeAdd.go re s mo lim intoNext pos f stD))) := by
              intro stR q hh c hchR hcw hstkR hrangeR hseenR hparkR hownR htabR
                hq hfR
              have hsz : stR.stk.size < re.code.size * 2 := by
                have h1 := hok.stack
                omega
              have hch := pikeDefer_charged (setup := setup) (pc := q) (h := hh)
                (lim := lim) hwf hchR.rooms hchR.held hsz
              have hsn := pikeDefer_seen (st := stR) (pc := q) (h := hh)
                (lim := lim)
              refine ⟨?_, ?_⟩
              · intro stE he
                refine Tried.error ?_ ?_
                · refine hstop stE (c + 0) ?_
                    (hchR.trans (charged_of_error he hch)) (by omega)
                  rw [seen_of_error he hsn]
                  exact hseenR
                · exact blown_of_mark hpcs hfalse hseenR hchR (by omega)
                    (pikeDefer_refused (setup := setup) (pc := q) (h := hh)
                      (lim := lim) hwf hchR.rooms hchR.held hsz he).blown
              · intro stB hb p hp
                have hchB : Charged re setup (c + 0) st stB :=
                  hchR.trans (charged_ok_id hb hch)
                have hsnB : stB.seen = stR.seen := seen_ok_id hb hsn
                obtain ⟨hstkB, -⟩ := pikeDefer_ok hb
                obtain ⟨hclB, hnlB⟩ := pikeDefer_lists hb
                obtain ⟨hrcB, -, -⟩ := pikeDefer_pool hb
                refine harmDefer stB p hh (c + 0) hchB (by omega) ?_ ?_ ?_ ?_
                  (defer_owned_two hb hownR) ?_ hp ?_
                · rw [hstkB, Array.size_push]; omega
                · rw [hstkB]; exact listInRange_push hrangeR hq
                · rw [hsnB]; exact hseenR
                · rw [parkList_eq hclB hnlB]; exact hparkR
                · rw [hrcB]; exact htabR
                · rw [hstkB, hsnB, Array.size_push]; omega
            have harmSave : ∀ (stA : PikeSt) (slotT hh : Nat) (value : UInt32),
                (re.code[st.stk.back!.pc]!).op = .save →
                Charged re setup 1 st stA →
                stA.stk.size ≤ st.stk.size → listInRange re stA.stk →
                stA.seen = st.seen.set! st.stk.back!.pc true →
                parkList intoNext stA = parkList intoNext st →
                Owned re.novec stA.rc stA.free stA.pool
                  (hh :: buildLive intoNext stA ext) →
                stA.rc.size ≤ re.code.size * 4 + 2 →
                stA.stk.size + 1 + 2 * unmarked stA.seen < f →
                (∀ stE, pikeWrite stA re.novec hh slotT value lim = .error stE →
                  Tried re setup 0 lim st id (Except.error stE)) ∧
                (∀ stW hOut, pikeWrite stA re.novec hh slotT value lim
                    = .ok (stW, hOut) →
                  (∀ stE, pikeDefer stW (st.stk.back!.pc + 1) hOut lim
                      = .error stE →
                    Tried re setup 0 lim st id (Except.error stE)) ∧
                  (∀ stD, pikeDefer stW (st.stk.back!.pc + 1) hOut lim = .ok stD →
                    Tried re setup 0 lim st id
                      (pikeAdd.go re s mo lim intoNext pos f stD))) := by
              intro stA slotT hh value hsave hchA hstkA hrangeA hseenA hparkA hownA
                htabA hfA
              have hmeas : addMeasure intoNext stA + ext.length ≤
                  re.code.size * 4 := by
                have h1 := hok.reach
                simp only [addMeasure] at h1 ⊢
                rw [hparkA, hseenA]
                omega
              have hlenA := buildLive_length intoNext stA ext
              have hlen : (hh :: buildLive intoNext stA ext).length ≤
                  re.code.size * 4 + 1 := by
                simp only [List.length_cons]
                omega
              have hrc : stA.free.size = 0 →
                  stA.rc.size < re.code.size * 4 + 2 := fun hz => by
                have h2 := (take_room hownA hlen hz).1
                omega
              have hpool : stA.free.size = 0 →
                  stA.pool.size + re.novec ≤
                    (re.code.size * 4 + 2) * re.novec := fun hz => by
                have h2 := (take_room hownA hlen hz).2
                have hb : re.code.size * 4 + 1 + 1 = re.code.size * 4 + 2 := by
                  omega
                rwa [hb] at h2
              have hcw : 1 + re.novec * regSize ≤
                  markWeight re st.stk.back!.pc := by
                rw [markWeight, if_pos hsave, pikeBlock]
                omega
              have hch := pikeWrite_charged (setup := setup) (novec := re.novec)
                (h := hh) (slot := slotT) (value := value) (lim := lim) hwf
                hchA.rooms hchA.held hrc hpool
              have hsn := pikeWrite_seen (st := stA) (novec := re.novec) (h := hh)
                (slot := slotT) (value := value) (lim := lim)
              refine ⟨?_, ?_⟩
              · intro stE he
                refine Tried.error ?_ ?_
                · refine hstop stE (1 + re.novec * regSize) ?_
                    (hchA.trans (charged_of_error he hch)) hcw
                  rw [seen_of_error he hsn]
                  exact hseenA
                · exact blown_of_mark hpcs hfalse hseenA hchA hcw
                    (pikeWrite_refused (setup := setup) (novec := re.novec)
                      (h := hh) (slot := slotT) (value := value) (lim := lim) hwf
                      hchA.rooms hchA.held hrc hpool he).blown
              · intro stW hOut hb
                have hchW : Charged re setup (1 + re.novec * regSize) st stW :=
                  hchA.trans (charged_ok_fst hb hch)
                have hsnW : stW.seen = stA.seen := seen_ok_fst hb hsn
                obtain ⟨hstkW, -⟩ := pikeWrite_ok hb
                obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hb
                obtain ⟨hownW, hszW⟩ := pikeWrite_owned hb hownA
                refine harmDefer stW (st.stk.back!.pc + 1) hOut
                  (1 + re.novec * regSize) hchW hcw ?_ ?_ ?_ ?_ ?_ ?_
                  (htgt _ (by simp [pikeTargets, hsave])) ?_
                · rw [hstkW]; exact hstkA
                · rw [hstkW]; exact hrangeA
                · rw [hsnW]; exact hseenA
                · rw [parkList_eq hclW hnlW]; exact hparkA
                · have hbl : buildLive intoNext stW ext =
                      buildLive intoNext stA ext := by
                    simp only [buildLive, hstkW, parkList_eq hclW hnlW]
                  rw [hbl]
                  exact hownW
                · omega
                · rw [hstkW, hsnW]; exact hfA
            -- Every arm starts from the marked state, whose reading the mark
            -- itself paid for.
            cases hop : (re.code[(st.stk.back!).pc]!).op <;> dsimp only
            case chr | chrCI | cls | any | anyNoNL | accept =>
              split
              · rename_i he
                exact (harmPark _ _ _ 1 hmarkC hw1 (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table hpcv
                  (by simp only [Array.size_pop]; omega)).1 _ he
              · rename_i he
                exact (harmPark _ _ _ 1 hmarkC hw1 (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table hpcv
                  (by simp only [Array.size_pop]; omega)).2 _ he
            case bsr =>
              split
              · rename_i he
                exact (harmDrop _ _ 1 hmarkC hw1 (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table
                  (by simp only [Array.size_pop]; omega)).1 _ he
              · rename_i he
                exact (harmDrop _ _ 1 hmarkC hw1 (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table
                  (by simp only [Array.size_pop]; omega)).2 _ he
            case jump | repZero | repEnter =>
              split
              · rename_i he
                exact (harmDefer _ _ _ 1 hmarkC hw1 (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table
                  (htgt _ (by simp [pikeTargets, hop]))
                  (by simp only [Array.size_pop]; omega)).1 _ he
              · rename_i he
                exact (harmDefer _ _ _ 1 hmarkC hw1 (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table
                  (htgt _ (by simp [pikeTargets, hop]))
                  (by simp only [Array.size_pop]; omega)).2 _ he
            case circ | doll | dollE | sod | eod | eodn | wordB | notWordB
                | circM | dollM =>
              repeat' split
              all_goals first
                | (rename_i he
                   exact (harmDefer _ _ _ 1 hmarkC hw1
                     (by simp only [Array.size_pop]; omega) hpop rfl rfl hflight
                     hok.table (htgt _ (by simp [pikeTargets, hop]))
                     (by simp only [Array.size_pop]; omega)).1 _ he)
                | (rename_i he
                   exact (harmDefer _ _ _ 1 hmarkC hw1
                     (by simp only [Array.size_pop]; omega) hpop rfl rfl hflight
                     hok.table (htgt _ (by simp [pikeTargets, hop]))
                     (by simp only [Array.size_pop]; omega)).2 _ he)
                | (rename_i he
                   exact (harmDrop _ _ 1 hmarkC hw1
                     (by simp only [Array.size_pop]; omega) hpop rfl rfl hflight
                     hok.table (by simp only [Array.size_pop]; omega)).1 _ he)
                | (rename_i he
                   exact (harmDrop _ _ 1 hmarkC hw1
                     (by simp only [Array.size_pop]; omega) hpop rfl rfl hflight
                     hok.table (by simp only [Array.size_pop]; omega)).2 _ he)
            case save =>
              split
              · rename_i he
                exact (harmSave _ _ _ _ hop hmarkC (by simp only [Array.size_pop]; omega)
                  hpop rfl rfl hflight hok.table
                  (by simp only [Array.size_pop]; omega)).1 _ he
              · rename_i he
                split
                · rename_i hd
                  exact ((harmSave _ _ _ _ hop hmarkC (by simp only [Array.size_pop]; omega)
                    hpop rfl rfl hflight hok.table
                    (by simp only [Array.size_pop]; omega)).2 _ _ he).1 _ hd
                · rename_i hd
                  exact ((harmSave _ _ _ _ hop hmarkC (by simp only [Array.size_pop]; omega)
                    hpop rfl rfl hflight hok.table
                    (by simp only [Array.size_pop]; omega)).2 _ _ he).2 _ hd
            case split =>
              split
              · rename_i he
                refine (harmFork _ _ _ 1 hmarkR hw1 ?_ hpop rfl rfl
                  (owned_share hflight) ?_ ?_ ?_).1 _ he
                · simp only [Array.size_pop]; omega
                · simp only [Array.size_set!]; exact hok.table
                · exact htgt _ (by simp [pikeTargets, hop])
                · simp only [Array.size_pop]; omega
              · rename_i he
                split
                · rename_i hd
                  refine ((harmFork _ _ _ 1 hmarkR hw1 ?_ hpop rfl rfl
                    (owned_share hflight) ?_ ?_ ?_).2 _ he _ ?_).1 _ hd
                  · simp only [Array.size_pop]; omega
                  · simp only [Array.size_set!]; exact hok.table
                  · exact htgt _ (by simp [pikeTargets, hop])
                  · simp only [Array.size_pop]; omega
                  · exact htgt _ (by simp [pikeTargets, hop])
                · rename_i hd
                  refine ((harmFork _ _ _ 1 hmarkR hw1 ?_ hpop rfl rfl
                    (owned_share hflight) ?_ ?_ ?_).2 _ he _ ?_).2 _ hd
                  · simp only [Array.size_pop]; omega
                  · simp only [Array.size_set!]; exact hok.table
                  · exact htgt _ (by simp [pikeTargets, hop])
                  · simp only [Array.size_pop]; omega
                  · exact htgt _ (by simp [pikeTargets, hop])
            case repLoop | repNext =>
              split
              all_goals
                split
                · rename_i he
                  refine (harmFork _ _ _ 1 hmarkR hw1 ?_ hpop rfl rfl
                    (owned_share hflight) ?_ ?_ ?_).1 _ he
                  · simp only [Array.size_pop]; omega
                  · simp only [Array.size_set!]; exact hok.table
                  · exact htgt _ (by simp [pikeTargets, hop])
                  · simp only [Array.size_pop]; omega
                · rename_i he
                  split
                  · rename_i hd
                    refine ((harmFork _ _ _ 1 hmarkR hw1 ?_ hpop rfl rfl
                      (owned_share hflight) ?_ ?_ ?_).2 _ he _ ?_).1 _ hd
                    · simp only [Array.size_pop]; omega
                    · simp only [Array.size_set!]; exact hok.table
                    · exact htgt _ (by simp [pikeTargets, hop])
                    · simp only [Array.size_pop]; omega
                    · exact htgt _ (by simp [pikeTargets, hop])
                  · rename_i hd
                    refine ((harmFork _ _ _ 1 hmarkR hw1 ?_ hpop rfl rfl
                      (owned_share hflight) ?_ ?_ ?_).2 _ he _ ?_).2 _ hd
                    · simp only [Array.size_pop]; omega
                    · simp only [Array.size_set!]; exact hok.table
                    · exact htgt _ (by simp [pikeTargets, hop])
                    · simp only [Array.size_pop]; omega
                    · exact htgt _ (by simp [pikeTargets, hop])


/-- `pikeAdd` itself: the entry it seeds the worklist with is the handle its
caller was holding, and seeding it charges only growth, so the build's own
account covers the whole call. The fuel the definition passes its loop,
`2*C + 2`, clears the measure the seeded worklist of one leaves behind. -/
theorem pikeAdd_tried (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (intoNext : Bool) (pos pc0 h0 setup : Nat) (ext : List Nat)
    {st : PikeSt}
    (hsz : st.seen.size = re.code.size) (hrange : listInRange re st.stk)
    (hrooms : Rooms re st) (hmem : st.m.mem ≤ setup + st.reserved)
    (hown : Owned re.novec st.rc st.free st.pool
      (h0 :: buildLive intoNext st ext))
    (hstk0 : st.stk.size = 0)
    (hparked : (parkList intoNext st).size + unmarked st.seen ≤ re.code.size)
    (hreach : addMeasure intoNext st + 1 + ext.length ≤ re.code.size * 4)
    (htable : st.rc.size ≤ re.code.size * 4 + 2) (hpc : pc0 < re.code.size) :
    Tried re setup 0 lim st id (pikeAdd re s mo lim intoNext pos pc0 h0 st) := by
  have hC := hwf.sized
  have hum : unmarked st.seen ≤ re.code.size := by
    have h1 := unmarked_le_size st.seen
    rw [hsz] at h1
    exact h1
  have hch := pikeDefer_charged (setup := setup) (pc := pc0) (h := h0)
    (lim := lim) hwf hrooms hmem (by omega)
  have hsn := pikeDefer_seen (st := st) (pc := pc0) (h := h0) (lim := lim)
  rw [pikeAdd]
  split
  · rename_i stE he
    refine Tried.error
      (Spent.ofCharged (charged_of_error he hch) (seen_of_error he hsn)) ?_
    exact (pikeDefer_refused (setup := setup) (pc := pc0) (h := h0)
      (lim := lim) hwf hrooms hmem (by omega) he).blown
  · rename_i stD hd
    have hchD : Charged re setup 0 st stD := charged_ok_id hd hch
    have hsnD : stD.seen = st.seen := seen_ok_id hd hsn
    obtain ⟨hstkD, -⟩ := pikeDefer_ok hd
    obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hd
    obtain ⟨hrcD, -, -⟩ := pikeDefer_pool hd
    have hparkD : parkList intoNext stD = parkList intoNext st :=
      parkList_eq hclD hnlD
    refine Tried.mono
      (Tried.after (Spent.ofCharged hchD hsnD)
        (pikeAdd_go_tried re s mo lim hwf intoNext pos setup ext _ stD
          ⟨?_, ?_, hchD.rooms, hchD.held, defer_owned hd hown, ?_, ?_, ?_, ?_⟩
          ?_))
      (by omega)
    · rw [hsnD]; exact hsz
    · rw [hstkD]; exact listInRange_push hrange hpc
    · rw [hstkD, hsnD, Array.size_push]; omega
    · rw [hparkD, hsnD]; exact hparked
    · simp only [addMeasure]
      rw [hstkD, hsnD, hparkD, Array.size_push]
      simp only [addMeasure] at hreach
      omega
    · rw [hrcD]; exact htable
    · rw [hstkD, hsnD, Array.size_push]; omega

/-! ### What the list step spends -/

theorem listInRange_of_empty {re : Re} {a : Array Th} (h : a.size = 0) :
    listInRange re a := by
  have hnil : a.toList = [] :=
    List.eq_nil_of_length_eq_zero (by rwa [Array.length_toList])
  intro y hy
  rw [hnil] at hy
  simp at hy

theorem seen_ok_step {x : POut StepOut} {a : StepOut} {st : PikeSt}
    (he : x = .ok a) (h : (outSt StepOut.st x).seen = st.seen) :
    a.st.seen = st.seen := by
  rw [he] at h
  exact h

theorem dropRest_seen {lim : Limits} : ∀ (rest : List Th) (st : PikeSt),
    (outSt id (dropRest lim rest st)).seen = st.seen := by
  intro rest
  induction rest with
  | nil =>
      intro st
      rw [dropRest]
      rfl
  | cons th rest ih =>
      intro st
      rw [dropRest]
      split
      · rename_i he
        exact seen_of_error he pikeDrop_seen
      · rename_i he
        rw [ih]
        exact seen_ok_id he pikeDrop_seen

/-- Dropping the threads a recorded match outranks charges only growth, and
each block it frees has room on the free list because someone was holding
it. -/
theorem dropRest_charged {re : Re} {setup : Nat} {lim : Limits} (hwf : ReWf re) :
    ∀ (rest : List Th) (st : PikeSt) (L : List Nat), Rooms re st →
      st.m.mem ≤ setup + st.reserved →
      Owned re.novec st.rc st.free st.pool (rest.map Th.h ++ L) →
      st.rc.size ≤ re.code.size * 4 + 2 →
      Charged re setup 0 st (outSt id (dropRest lim rest st)) := by
  intro rest
  induction rest with
  | nil =>
      intro st L hrooms hmem _ _
      rw [dropRest]
      exact Charged.idle hrooms rfl rfl hmem
  | cons th rest ih =>
      intro st L hrooms hmem hown htab
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: (rest.map Th.h ++ L)) := by simpa using hown
      have hch := pikeDrop_charged (setup := setup) (h := th.h) (lim := lim) hwf
        hrooms hmem (fun _ => free_room hmid htab)
      rw [dropRest]
      split
      · rename_i he
        exact charged_of_error he hch
      · rename_i stB hb
        have hchB : Charged re setup 0 st stB := charged_ok_id hb hch
        obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hb
        exact Charged.mono (hchB.trans (ih stB L hchB.rooms hchB.held
          (pikeDrop_owned hb hmid) (by rw [hrcB]; exact htab))) (by omega)

theorem dropRest_refused {re : Re} {setup : Nat} {lim : Limits} (hwf : ReWf re) :
    ∀ (rest : List Th) (st stE : PikeSt) (L : List Nat), Rooms re st →
      st.m.mem ≤ setup + st.reserved →
      Owned re.novec st.rc st.free st.pool (rest.map Th.h ++ L) →
      st.rc.size ≤ re.code.size * 4 + 2 →
      dropRest lim rest st = .error stE → BlownFlat re setup 0 lim st := by
  intro rest
  induction rest with
  | nil =>
      intro st stE L _ _ _ _ he
      rw [dropRest] at he
      exact absurd he (by simp)
  | cons th rest ih =>
      intro st stE L hrooms hmem hown htab he
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: (rest.map Th.h ++ L)) := by simpa using hown
      have hsize := fun (_ : st.rc[th.h]! ≤ 1) => free_room hmid htab
      rw [dropRest] at he
      split at he
      · rename_i hd
        exact pikeDrop_refused hwf hrooms hmem hsize hd
      · rename_i stB hd
        have hchB : Charged re setup 0 st stB :=
          charged_ok_id hd (pikeDrop_charged hwf hrooms hmem hsize)
        obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hd
        exact BlownFlat.mono
          (BlownFlat.after hchB (seen_ok_id hd pikeDrop_seen)
            (ih stB stE L hchB.rooms hchB.held (pikeDrop_owned hd hmid)
              (by rw [hrcB]; exact htab) he)) (by omega)

/-- At the last position the step opens no closure at all: a consuming
thread there fails the `pos < n` test and lets its handle go instead of
closing over. So the visited set the position cleared is charged and never
drawn on, which is what keeps a whole scan inside `n + 1` positions' worth
of marks rather than one set more. -/
theorem stepThreads_seen (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start pos : Nat) (hpos : s.size ≤ pos) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      (outSt StepOut.st (stepThreads re s mo lim start pos threads st mh
        seeding matched)).seen = st.seen := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched
      rw [stepThreads]
      rfl
  | cons th rest ih =>
      intro st mh seeding matched
      have hstep : ∀ stB : PikeSt, stB.seen = st.seen →
          (outSt StepOut.st (stepThreads re s mo lim start pos rest stB mh
            seeding matched)).seen = st.seen := by
        intro stB hb
        rw [ih stB mh seeding matched]
        exact hb
      simp only [stepThreads]
      split
      · rfl
      · cases hop : (re.code[th.pc]!).op <;> dsimp only
        case chr | chrCI | cls | any | anyNoNL =>
          split
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            omega
          · split
            · rename_i he
              exact seen_of_error he pikeDrop_seen
            · rename_i he
              exact hstep _ (seen_ok_id he pikeDrop_seen)
        case accept =>
          split
          · split
            · rename_i he
              exact seen_of_error he pikeDrop_seen
            · rename_i he
              exact hstep _ (seen_ok_id he pikeDrop_seen)
          · split
            · rename_i he
              exact seen_of_error he pikeWrite_seen
            · rename_i stW hv he
              have h1 : stW.seen = st.seen := seen_ok_fst he pikeWrite_seen
              split
              · rename_i hd
                exact (seen_of_error hd pikeDrop_seen).trans h1
              · rename_i stD hd
                have h2 : stD.seen = st.seen :=
                  (seen_ok_id hd pikeDrop_seen).trans h1
                split
                · rename_i hr
                  exact (seen_of_error hr (dropRest_seen rest stD)).trans h2
                · rename_i hr
                  exact (seen_ok_id hr (dropRest_seen rest stD)).trans h2
        case bsr | split | jump | save | circ | circM | doll | dollE | dollM
            | sod | eod | eodn | wordB | notWordB | repZero | repLoop
            | repEnter | repNext =>
          all_goals
            split
            · rename_i he
              exact seen_of_error he pikeDrop_seen
            · rename_i he
              exact hstep _ (seen_ok_id he pikeDrop_seen)

set_option maxHeartbeats 4000000 in
/-- Stepping the built list, weighed. Each thread costs the one unit the loop
tests for before it charges it, and the closure it opens spends only what its
own marks release; the accept's copy-on-write is the one block a step pays
besides. So a step is inside a unit per thread and one block, whatever the
list does, a refusal is inside it too, and so is the charge that refusal was
asking for. -/
theorem stepThreads_tried (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos setup : Nat) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      BuildOk re st → st.stk.size = 0 →
      (∀ th ∈ threads, th.pc < re.code.size) →
      Rooms re st → st.m.mem ≤ setup + st.reserved →
      Owned re.novec st.rc st.free st.pool
        (buildLive true st (threads.map Th.h ++ mhList mh)) →
      st.nlist.size + unmarked st.seen ≤ re.code.size →
      addMeasure true st + threads.length + 1 ≤ re.code.size * 3 + 1 →
      st.rc.size ≤ re.code.size * 4 + 2 →
      Tried re setup (threads.length + pikeBlock re) lim st StepOut.st
        (stepThreads re s mo lim start pos threads st mh seeding matched) := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched _ _ _ hrooms hmem _ _ _ _
      rw [stepThreads]
      exact Tried.ofOk (Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _))
  | cons th rest ih =>
      intro st mh seeding matched hb hstk0 hpcs hrooms hmem hown hparked hreach
        htab
      have hC := hwf.sized
      have hthpc : th.pc < re.code.size := hpcs th List.mem_cons_self
      have hrest : ∀ t ∈ rest, t.pc < re.code.size :=
        fun t htm => hpcs t (List.mem_cons_of_mem _ htm)
      have hml : (mhList mh).length ≤ 1 := mhList_length mh
      -- The thread's own handle, taken into flight off the snapshot.
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)) := by
        refine hown.perm ?_
        have he : (th :: rest).map Th.h ++ mhList mh =
            th.h :: (rest.map Th.h ++ mhList mh) := by simp
        rw [he, buildLive, buildLive]
        exact List.perm_middle.symm
      have hlenA := buildLive_length true st (rest.map Th.h ++ mhList mh)
      have hlen : (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)).length
          ≤ re.code.size * 4 + 1 := by
        simp only [List.length_cons, List.length_append, List.length_map] at *
        omega
      have hmark : Charged re setup 1 st
          { st with m := { st.m with cost := st.m.cost + 1 } } :=
        Charged.pay 1 hrooms hmem
      have hstep : ∀ (stB : PikeSt) (c : Nat),
          BuildOk re stB → stB.stk.size = 0 →
          Rooms re stB → stB.m.mem ≤ setup + stB.reserved →
          Owned re.novec stB.rc stB.free stB.pool
            (buildLive true stB (rest.map Th.h ++ mhList mh)) →
          stB.nlist.size + unmarked stB.seen ≤ re.code.size →
          addMeasure true stB + rest.length + 1 ≤ re.code.size * 3 + 1 →
          stB.rc.size ≤ re.code.size * 4 + 2 →
          Spent re setup c st stB → c ≤ 1 →
          Tried re setup ((th :: rest).length + pikeBlock re) lim st StepOut.st
            (stepThreads re s mo lim start pos rest stB mh seeding matched) := by
        intro stB c h1 h2 h3 h4 h5 h6 h7 h8 hsp hc
        refine Tried.mono (Tried.after hsp (ih stB mh seeding matched h1 h2 hrest
          h3 h4 h5 h6 h7 h8)) ?_
        simp only [List.length_cons]
        omega
      -- The three shapes an arm can take, read off the charged state.
      have harmAdd : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          th.pc + 1 < re.code.size →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h stA
              = .error stE →
            Tried re setup ((th :: rest).length + pikeBlock re) lim st
              StepOut.st (Except.error stE)) ∧
          (∀ stB, pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h stA
              = .ok stB →
            Tried re setup ((th :: rest).length + pikeBlock re) lim st
              StepOut.st
              (stepThreads re s mo lim start pos rest stB mh seeding matched)) := by
        intro stA hchA hnext hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hbA : BuildOk re stA :=
          ⟨by rw [hseenA]; exact hb.seenSize, by rw [hstkA]; exact hb.stk,
            by rw [hclA]; exact hb.clist, by rw [hnlA]; exact hb.nlist⟩
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hmA : addMeasure true stA = addMeasure true st := by
          simp only [addMeasure, hstkA, hseenA, hpkA]
        have hadd := pikeAdd_tried re s mo lim hwf true (pos + 1) (th.pc + 1)
          th.h setup (rest.map Th.h ++ mhList mh) hbA.seenSize hbA.stk
          hchA.rooms hchA.held hownA (by rw [hstkA]; exact hstk0)
          (by rw [hpkA, hseenA]; exact hparked)
          (by
            simp only [List.length_append, List.length_map]
            simp only [List.length_cons] at hreach
            omega)
          (by rw [hrcA]; exact htab) hnext
        refine ⟨?_, ?_⟩
        · intro stE he
          refine Tried.error ?_ ?_
          · refine Spent.mono
              ((Spent.ofCharged hchA hseenA).trans (spent_of_error he hadd.1)) ?_
            simp only [List.length_cons]
            omega
          · refine Blown.mono
              (Blown.after (Spent.ofCharged hchA hseenA) (hadd.2 stE he)) ?_
            simp only [List.length_cons]
            omega
        · intro stB hok
          obtain ⟨b1, b2, b3, -⟩ := pikeAdd_build re s mo lim hwf true (pos + 1)
            (th.pc + 1) th.h hok hnext hbA
          obtain ⟨o1, o2, o3, o4, o5⟩ := pikeAdd_owned re s mo lim true (pos + 1)
            (th.pc + 1) th.h (rest.map Th.h ++ mhList mh) hok hbA.seenSize hownA
          have hspB : Spent re setup (1 + 0) st stB :=
            (Spent.ofCharged hchA hseenA).trans (spent_ok_id hok hadd.1)
          have hclB : stB.clist = stA.clist := b3 rfl
          have hnlB : stB.nlist.size + unmarked stB.seen ≤ re.code.size := by
            simp only [buildMeasure] at b2
            have hc := congrArg Array.size hclB
            have hn := congrArg Array.size hnlA
            rw [hseenA] at b2
            omega
          refine hstep stB (1 + 0) b1 o4 hspB.rooms hspB.held o1 hnlB ?_ ?_ hspB
            (by omega)
          · simp only [List.length_cons] at hreach
            omega
          · simp only [List.length_append, List.length_map] at o5
            simp only [List.length_cons] at hreach
            have hr := congrArg Array.size hrcA
            omega
      have harmDrop : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeDrop stA th.h lim = .error stE →
            Tried re setup ((th :: rest).length + pikeBlock re) lim st
              StepOut.st (Except.error stE)) ∧
          (∀ stB, pikeDrop stA th.h lim = .ok stB →
            Tried re setup ((th :: rest).length + pikeBlock re) lim st
              StepOut.st
              (stepThreads re s mo lim start pos rest stB mh seeding matched)) := by
        intro stA hchA hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hbA : BuildOk re stA :=
          ⟨by rw [hseenA]; exact hb.seenSize, by rw [hstkA]; exact hb.stk,
            by rw [hclA]; exact hb.clist, by rw [hnlA]; exact hb.nlist⟩
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hch := pikeDrop_charged (setup := setup) (h := th.h) (lim := lim)
          hwf hchA.rooms hchA.held
          (fun _ => free_room hownA (by rw [hrcA]; exact htab))
        have hsn := pikeDrop_seen (st := stA) (h := th.h) (lim := lim)
        refine ⟨?_, ?_⟩
        · intro stE he
          refine Tried.error ?_ ?_
          · refine Spent.mono
              ((Spent.ofCharged hchA hseenA).trans
                (Spent.ofCharged (charged_of_error he hch)
                  (seen_of_error he hsn))) ?_
            simp only [List.length_cons]
            omega
          · refine Blown.mono
              (Blown.after (Spent.ofCharged hchA hseenA)
                (pikeDrop_refused (setup := setup) (h := th.h) (lim := lim) hwf
                  hchA.rooms hchA.held
                  (fun _ => free_room hownA
                    (by rw [hrcA]; exact htab)) he).blown) ?_
            simp only [List.length_cons]
            omega
        · intro stB hok
          have hchB : Charged re setup 0 stA stB := charged_ok_id hok hch
          have hsnB : stB.seen = st.seen := (seen_ok_id hok hsn).trans hseenA
          obtain ⟨hstkB, hseB⟩ := pikeDrop_ok hok
          obtain ⟨hclB, hnlB⟩ := pikeDrop_lists hok
          obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hok
          have hpkB : parkList true stB = parkList true st :=
            (parkList_eq hclB hnlB).trans hpkA
          have hspB : Spent re setup (1 + 0) st stB :=
            (Spent.ofCharged hchA hseenA).trans
              (Spent.ofCharged hchB ((seen_ok_id hok hsn)))
          refine hstep stB (1 + 0)
            ⟨by rw [hsnB]; exact hb.seenSize,
              by rw [hstkB, hstkA]; exact hb.stk,
              by rw [hclB, hclA]; exact hb.clist,
              by rw [hnlB, hnlA]; exact hb.nlist⟩
            (by rw [hstkB, hstkA]; exact hstk0) hspB.rooms hspB.held ?_ ?_ ?_ ?_
            hspB (by omega)
          · exact drop_owned hok hownA
          · have hnB : (parkList true stB).size = stB.nlist.size := rfl
            have hnS : (parkList true st).size = st.nlist.size := rfl
            have hsame := congrArg Array.size hpkB
            rw [hnB, hnS] at hsame
            rw [hsnB, hsame]
            exact hparked
          · simp only [addMeasure, hstkB, hstkA, hsnB, hpkB]
            simp only [addMeasure, List.length_cons] at hreach
            omega
          · rw [hrcB, hrcA]
            exact htab
      have harmAccept : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeWrite stA re.novec th.h 1 pos.toUInt32 lim = .error stE →
            Tried re setup ((th :: rest).length + pikeBlock re) lim st
              StepOut.st (Except.error stE)) ∧
          (∀ stW hv, pikeWrite stA re.novec th.h 1 pos.toUInt32 lim
              = .ok (stW, hv) →
            (∀ stE, pikeDrop stW mh lim = .error stE →
              Tried re setup ((th :: rest).length + pikeBlock re) lim st
                StepOut.st (Except.error stE)) ∧
            (∀ stD, pikeDrop stW mh lim = .ok stD →
              (∀ stE, dropRest lim rest stD = .error stE →
                Tried re setup ((th :: rest).length + pikeBlock re) lim st
                  StepOut.st (Except.error stE)) ∧
              (∀ stF, dropRest lim rest stD = .ok stF →
                Spent re setup ((th :: rest).length + pikeBlock re) st stF))) := by
        intro stA hchA hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hlenA' : (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)).length
            ≤ re.code.size * 4 + 1 := by
          rw [hblA]; exact hlen
        have hchW := pikeWrite_charged (setup := setup) (novec := re.novec)
          (h := th.h) (slot := 1) (value := pos.toUInt32) (lim := lim) hwf
          hchA.rooms hchA.held
          (fun hz => by have h2 := (take_room hownA hlenA' hz).1; omega)
          (fun hz => by
            have h2 := (take_room hownA hlenA' hz).2
            have hbb : re.code.size * 4 + 1 + 1 = re.code.size * 4 + 2 := by omega
            rwa [hbb] at h2)
        have hsnW := pikeWrite_seen (st := stA) (novec := re.novec) (h := th.h)
          (slot := 1) (value := pos.toUInt32) (lim := lim)
        have hbk : pikeBlock re = re.novec * regSize := rfl
        refine ⟨?_, ?_⟩
        · intro stE he
          refine Tried.error ?_ ?_
          · refine Spent.mono
              ((Spent.ofCharged hchA hseenA).trans
                (Spent.ofCharged (charged_of_error he hchW)
                  (seen_of_error he hsnW))) ?_
            simp only [List.length_cons, hbk]
            omega
          · refine Blown.mono
              (Blown.after (Spent.ofCharged hchA hseenA)
                (pikeWrite_refused (setup := setup) (novec := re.novec)
                  (h := th.h) (slot := 1) (value := pos.toUInt32) (lim := lim)
                  hwf hchA.rooms hchA.held
                  (fun hz => by have h2 := (take_room hownA hlenA' hz).1; omega)
                  (fun hz => by
                    have h2 := (take_room hownA hlenA' hz).2
                    have hbb : re.code.size * 4 + 1 + 1 =
                      re.code.size * 4 + 2 := by omega
                    rwa [hbb] at h2) he).blown) ?_
            simp only [List.length_cons, hbk]
            omega
        · intro stW hv hok
          have hspW : Spent re setup (1 + re.novec * regSize) st stW :=
            (Spent.ofCharged hchA hseenA).trans
              (Spent.ofCharged (charged_ok_fst hok hchW) (seen_ok_fst hok hsnW))
          obtain ⟨hownW, hszW⟩ := pikeWrite_owned hok hownA
          obtain ⟨hstkW, hseW⟩ := pikeWrite_ok hok
          obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hok
          have hpkW : parkList true stW = parkList true stA :=
            parkList_eq hclW hnlW
          have htabW : stW.rc.size ≤ re.code.size * 4 + 2 := by
            have hr := congrArg Array.size hrcA
            simp only [List.length_cons] at hreach
            simp only [List.length_append, List.length_map] at hlenA
            have hbl := congrArg List.length hblA
            omega
          have hchD := pikeDrop_charged (setup := setup) (h := mh) (lim := lim)
            hwf hspW.rooms hspW.held (fun _ => free_room hownW htabW)
          have hsnD := pikeDrop_seen (st := stW) (h := mh) (lim := lim)
          refine ⟨?_, ?_⟩
          · intro stE he
            refine Tried.error ?_ ?_
            · refine Spent.mono
                (hspW.trans (Spent.ofCharged (charged_of_error he hchD)
                  (seen_of_error he hsnD))) ?_
              simp only [List.length_cons, hbk]
              omega
            · refine Blown.mono
                (Blown.after hspW
                  (pikeDrop_refused (setup := setup) (h := mh) (lim := lim) hwf
                    hspW.rooms hspW.held
                    (fun _ => free_room hownW htabW) he).blown) ?_
              simp only [List.length_cons, hbk]
              omega
          · intro stD hd
            have hspD : Spent re setup (1 + re.novec * regSize + 0) st stD :=
              hspW.trans (Spent.ofCharged (charged_ok_id hd hchD)
                (seen_ok_id hd hsnD))
            obtain ⟨hrcD, -⟩ := pikeDrop_rcSize hd
            -- The old match let go of: a no-op while it is still the sentinel.
            have hdrop : Owned re.novec stD.rc stD.free stD.pool
                (hv :: buildLive true stW (rest.map Th.h)) := by
              by_cases hmh : mh = none32
              · subst hmh
                have hnil : mhList none32 = [] := by rw [mhList, if_pos rfl]
                have hres := pikeDrop_none_owned hd hownW
                rw [hblA] at hres
                rw [hnil, List.append_nil] at hres
                rw [buildLive, hstkW, hpkW, hstkA, hpkA, ← buildLive]
                exact hres
              · have hmhl : mhList mh = [mh] := by rw [mhList, if_neg hmh]
                refine pikeDrop_owned hd (how := ?_)
                refine hownW.perm ?_
                rw [hblA, hmhl]
                simp only [buildLive]
                have he : handles st.stk ++ handles (parkList true st) ++
                    (rest.map Th.h ++ [mh]) =
                    (handles st.stk ++ handles (parkList true st) ++
                      rest.map Th.h) ++ [mh] := by simp
                rw [he, hstkW, hpkW, hstkA, hpkA]
                exact (((perm_last _ mh).cons hv).trans
                  (List.Perm.swap mh hv _)).symm
            have hrestL : Owned re.novec stD.rc stD.free stD.pool
                (rest.map Th.h ++
                  (hv :: (handles stW.stk ++ handles (parkList true stW)))) := by
              refine hdrop.perm ?_
              rw [buildLive]
              exact List.perm_middle.trans ((List.perm_append_comm).cons hv)
            have hchR := dropRest_charged (setup := setup) (lim := lim) hwf rest
              stD _ hspD.rooms hspD.held hrestL (by rw [hrcD]; exact htabW)
            have hsnR := dropRest_seen (lim := lim) rest stD
            refine ⟨?_, ?_⟩
            · intro stE he
              refine Tried.error ?_ ?_
              · refine Spent.mono
                  (hspD.trans (Spent.ofCharged (charged_of_error he hchR)
                    (seen_of_error he hsnR))) ?_
                simp only [List.length_cons, hbk]
                omega
              · refine Blown.mono
                  (Blown.after hspD
                    (dropRest_refused (setup := setup) (lim := lim) hwf rest stD
                      stE _ hspD.rooms hspD.held hrestL
                      (by rw [hrcD]; exact htabW) he).blown) ?_
                simp only [List.length_cons, hbk]
                omega
            · intro stF hr
              refine Spent.mono
                (hspD.trans (Spent.ofCharged (charged_ok_id hr hchR)
                  (seen_ok_id hr hsnR))) ?_
              simp only [List.length_cons, hbk]
              omega
      simp only [stepThreads]
      split
      · rename_i htest
        refine Tried.error (Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _))
          (Blown.mono (Blown.ofCost 1 hrooms hmem htest) ?_)
        simp only [List.length_cons]
        omega
      cases hop : (re.code[th.pc]!).op <;>
        first
          | dsimp only
          | simp only [hop]
          | skip
      case chr | chrCI | cls | any | anyNoNL =>
        have hnext : th.pc + 1 < re.code.size :=
          hwf.targets _ hthpc _ (by simp [pikeTargets, hop])
        split
        · split
          · rename_i he
            exact (harmAdd _ hmark hnext rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmAdd _ hmark hnext rfl rfl rfl rfl rfl rfl rfl).2 _ he
        · split
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ he
      case accept =>
        split
        · split
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ he
        · split
          · rename_i he
            exact (harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            split
            · rename_i hd
              exact ((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                he).1 _ hd
            · rename_i hd
              split
              · rename_i hr
                exact (((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                  he).2 _ hd).1 _ hr
              · rename_i hr
                exact Tried.ofOk
                  ((((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                    he).2 _ hd).2 _ hr)
      case bsr | split | jump | save | circ | circM | doll | dollE | dollM
          | sod | eod | eodn | wordB | notWordB | repZero | repLoop
          | repEnter | repNext =>
        all_goals
          split
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ he

set_option maxHeartbeats 1000000 in
/-- The same step at the last position, where it opens no closure at all: a
consuming thread fails the `pos < n` test and lets its handle go. So what a
refusal there was asking for is pure charge, a unit per thread and the
accept's block, and no part of the visited set the position cleared pays for
it. That is what the scan's account needs of its last position, since the
leftover of that clear is what pays for the seed at the very first one. -/
theorem stepThreads_last (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos setup : Nat) (hpos : s.size ≤ pos) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool)
      (stX : PikeSt),
      Rooms re st → st.m.mem ≤ setup + st.reserved →
      Owned re.novec st.rc st.free st.pool
        (buildLive true st (threads.map Th.h ++ mhList mh)) →
      addMeasure true st + threads.length + 1 ≤ re.code.size * 3 + 1 →
      st.rc.size ≤ re.code.size * 4 + 2 →
      stepThreads re s mo lim start pos threads st mh seeding matched
        = .error stX →
      BlownFlat re setup (threads.length + pikeBlock re) lim st := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched stX _ _ _ _ _ he
      rw [stepThreads] at he
      exact absurd he (by simp)
  | cons th rest ih =>
      intro st mh seeding matched stX hrooms hmem hown hreach htab he
      have hC := hwf.sized
      have hml : (mhList mh).length ≤ 1 := mhList_length mh
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)) := by
        refine hown.perm ?_
        have hq : (th :: rest).map Th.h ++ mhList mh =
            th.h :: (rest.map Th.h ++ mhList mh) := by simp
        rw [hq, buildLive, buildLive]
        exact List.perm_middle.symm
      have hlenA := buildLive_length true st (rest.map Th.h ++ mhList mh)
      have hlen : (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)).length
          ≤ re.code.size * 4 + 1 := by
        simp only [List.length_cons, List.length_append, List.length_map] at *
        omega
      have hmark : Charged re setup 1 st
          { st with m := { st.m with cost := st.m.cost + 1 } } :=
        Charged.pay 1 hrooms hmem
      have harmDrop : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeDrop stA th.h lim = .error stE →
            BlownFlat re setup ((th :: rest).length + pikeBlock re) lim st) ∧
          (∀ stB, pikeDrop stA th.h lim = .ok stB →
            stepThreads re s mo lim start pos rest stB mh seeding matched
              = .error stX →
            BlownFlat re setup ((th :: rest).length + pikeBlock re) lim st) := by
        intro stA hchA hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have htabA : stA.rc.size ≤ re.code.size * 4 + 2 := by
          rw [hrcA]; exact htab
        have hch := pikeDrop_charged (setup := setup) (h := th.h) (lim := lim)
          hwf hchA.rooms hchA.held (fun _ => free_room hownA htabA)
        have hsn := pikeDrop_seen (st := stA) (h := th.h) (lim := lim)
        refine ⟨?_, ?_⟩
        · intro stE hd
          refine BlownFlat.mono (BlownFlat.after hchA hseenA
            (pikeDrop_refused (setup := setup) (h := th.h) (lim := lim) hwf
              hchA.rooms hchA.held (fun _ => free_room hownA htabA) hd)) ?_
          simp only [List.length_cons]
          omega
        · intro stB hd hgo
          have hchB : Charged re setup (1 + 0) st stB :=
            hchA.trans (charged_ok_id hd hch)
          have hsnB : stB.seen = st.seen := (seen_ok_id hd hsn).trans hseenA
          obtain ⟨hstkB, -⟩ := pikeDrop_ok hd
          obtain ⟨hclB, hnlB⟩ := pikeDrop_lists hd
          obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hd
          have hpkB : parkList true stB = parkList true st :=
            (parkList_eq hclB hnlB).trans hpkA
          refine BlownFlat.mono (BlownFlat.after hchB hsnB
            (ih stB mh seeding matched stX hchB.rooms hchB.held
              (drop_owned hd hownA) ?_ ?_ hgo)) ?_
          · simp only [addMeasure, hstkB, hstkA, hsnB, hpkB]
            simp only [addMeasure, List.length_cons] at hreach
            omega
          · rw [hrcB, hrcA]; exact htab
          · simp only [List.length_cons]
            omega
      have harmAccept : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeWrite stA re.novec th.h 1 pos.toUInt32 lim = .error stE →
            BlownFlat re setup ((th :: rest).length + pikeBlock re) lim st) ∧
          (∀ stW hv, pikeWrite stA re.novec th.h 1 pos.toUInt32 lim
              = .ok (stW, hv) →
            (∀ stE, pikeDrop stW mh lim = .error stE →
              BlownFlat re setup ((th :: rest).length + pikeBlock re) lim st) ∧
            (∀ stD, pikeDrop stW mh lim = .ok stD →
              ∀ stE, dropRest lim rest stD = .error stE →
                BlownFlat re setup
                  ((th :: rest).length + pikeBlock re) lim st)) := by
        intro stA hchA hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hlenA' : (th.h :: buildLive true stA
            (rest.map Th.h ++ mhList mh)).length ≤ re.code.size * 4 + 1 := by
          rw [hblA]; exact hlen
        have hrc : stA.free.size = 0 →
            stA.rc.size < re.code.size * 4 + 2 := fun hz => by
          have h2 := (take_room hownA hlenA' hz).1
          omega
        have hpool : stA.free.size = 0 →
            stA.pool.size + re.novec ≤
              (re.code.size * 4 + 2) * re.novec := fun hz => by
          have h2 := (take_room hownA hlenA' hz).2
          have hbb : re.code.size * 4 + 1 + 1 = re.code.size * 4 + 2 := by omega
          rwa [hbb] at h2
        have hchW := pikeWrite_charged (setup := setup) (novec := re.novec)
          (h := th.h) (slot := 1) (value := pos.toUInt32) (lim := lim) hwf
          hchA.rooms hchA.held hrc hpool
        have hsnW := pikeWrite_seen (st := stA) (novec := re.novec) (h := th.h)
          (slot := 1) (value := pos.toUInt32) (lim := lim)
        have hbk : pikeBlock re = re.novec * regSize := rfl
        refine ⟨?_, ?_⟩
        · intro stE hw
          refine BlownFlat.mono (BlownFlat.after hchA hseenA
            (pikeWrite_refused (setup := setup) (novec := re.novec)
              (h := th.h) (slot := 1) (value := pos.toUInt32) (lim := lim) hwf
              hchA.rooms hchA.held hrc hpool hw)) ?_
          simp only [List.length_cons, hbk]
          omega
        · intro stW hv hw
          have hchWo : Charged re setup (1 + re.novec * regSize) st stW :=
            hchA.trans (charged_ok_fst hw hchW)
          have hsnWo : stW.seen = st.seen := (seen_ok_fst hw hsnW).trans hseenA
          obtain ⟨hownW, hszW⟩ := pikeWrite_owned hw hownA
          obtain ⟨hstkW, -⟩ := pikeWrite_ok hw
          obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hw
          have hpkW : parkList true stW = parkList true stA :=
            parkList_eq hclW hnlW
          have htabW : stW.rc.size ≤ re.code.size * 4 + 2 := by
            have hr := congrArg Array.size hrcA
            simp only [List.length_cons] at hreach
            simp only [List.length_append, List.length_map] at hlenA
            have hbl := congrArg List.length hblA
            omega
          have hchD := pikeDrop_charged (setup := setup) (h := mh) (lim := lim)
            hwf hchWo.rooms hchWo.held (fun _ => free_room hownW htabW)
          have hsnD := pikeDrop_seen (st := stW) (h := mh) (lim := lim)
          refine ⟨?_, ?_⟩
          · intro stE hd
            refine BlownFlat.mono (BlownFlat.after hchWo hsnWo
              (pikeDrop_refused (setup := setup) (h := mh) (lim := lim) hwf
                hchWo.rooms hchWo.held (fun _ => free_room hownW htabW) hd)) ?_
            simp only [List.length_cons, hbk]
            omega
          · intro stD hd stE hr
            have hchDo : Charged re setup (1 + re.novec * regSize + 0) st stD :=
              hchWo.trans (charged_ok_id hd hchD)
            have hsnDo : stD.seen = st.seen := (seen_ok_id hd hsnD).trans hsnWo
            obtain ⟨hrcD, -⟩ := pikeDrop_rcSize hd
            have hdrop : Owned re.novec stD.rc stD.free stD.pool
                (hv :: buildLive true stW (rest.map Th.h)) := by
              by_cases hmh : mh = none32
              · subst hmh
                have hnil : mhList none32 = [] := by rw [mhList, if_pos rfl]
                have hres := pikeDrop_none_owned hd hownW
                rw [hblA] at hres
                rw [hnil, List.append_nil] at hres
                rw [buildLive, hstkW, hpkW, hstkA, hpkA, ← buildLive]
                exact hres
              · have hmhl : mhList mh = [mh] := by rw [mhList, if_neg hmh]
                refine pikeDrop_owned hd (how := ?_)
                refine hownW.perm ?_
                rw [hblA, hmhl]
                simp only [buildLive]
                have hq : handles st.stk ++ handles (parkList true st) ++
                    (rest.map Th.h ++ [mh]) =
                    (handles st.stk ++ handles (parkList true st) ++
                      rest.map Th.h) ++ [mh] := by simp
                rw [hq, hstkW, hpkW, hstkA, hpkA]
                exact (((perm_last _ mh).cons hv).trans
                  (List.Perm.swap mh hv _)).symm
            have hrestL : Owned re.novec stD.rc stD.free stD.pool
                (rest.map Th.h ++
                  (hv :: (handles stW.stk ++ handles (parkList true stW)))) := by
              refine hdrop.perm ?_
              rw [buildLive]
              exact List.perm_middle.trans ((List.perm_append_comm).cons hv)
            refine BlownFlat.mono (BlownFlat.after hchDo hsnDo
              (dropRest_refused (setup := setup) (lim := lim) hwf rest stD stE _
                hchDo.rooms hchDo.held hrestL (by rw [hrcD]; exact htabW) hr)) ?_
            simp only [List.length_cons, hbk]
            omega
      simp only [stepThreads] at he
      split at he
      · rename_i htest
        refine BlownFlat.mono (BlownFlat.ofCost 1 hrooms hmem htest) ?_
        simp only [List.length_cons]
        omega
      · cases hop : (re.code[th.pc]!).op <;> simp only [hop] at he
        case chr | chrCI | cls | any | anyNoNL =>
          split at he
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            omega
          · split at he
            · rename_i stE hd
              exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ hd
            · rename_i stB hd
              exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ hd he
        case accept =>
          split at he
          · split at he
            · rename_i stE hd
              exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ hd
            · rename_i stB hd
              exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ hd he
          · split at he
            · rename_i stE hw
              exact (harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ hw
            · rename_i stW hv hw
              split at he
              · rename_i stE hd
                exact ((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                  hw).1 _ hd
              · rename_i stD hd
                split at he
                · rename_i stE hr
                  exact ((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                    hw).2 _ hd _ hr
                · exact absurd he (by simp)
        case bsr | split | jump | save | circ | circM | doll | dollE | dollM
            | sod | eod | eodn | wordB | notWordB | repZero | repLoop
            | repEnter | repNext =>
          all_goals
            split at he
            · rename_i stE hd
              exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ hd
            · rename_i stB hd
              exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ hd he

/-! ### What a position's seed spends -/

/-- Seeding a position: the block it takes is growth the reservation pays
for, the fill it charges is the one block BOUNDS.md section 9 names, and the
closure it opens spends only what its own marks release. Whichever of the
three a refusal lands on, the charge it was asking for is inside that same
block. -/
theorem pikeSeed_tried (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos setup : Nat) (ext : List Nat) {st : PikeSt}
    (hsz : st.seen.size = re.code.size) (hrange : listInRange re st.stk)
    (hstk0 : st.stk.size = 0) (hrooms : Rooms re st)
    (hmem : st.m.mem ≤ setup + st.reserved)
    (hown : Owned re.novec st.rc st.free st.pool (buildLive false st ext))
    (hparked : (parkList false st).size + unmarked st.seen ≤ re.code.size)
    (hreach : addMeasure false st + ext.length + 1 ≤ re.code.size * 4)
    (htable : st.rc.size ≤ re.code.size * 4 + 2) :
    Tried re setup (pikeBlock re) lim st id
      (pikeSeed re s mo lim start pos st) := by
  have hC := hwf.sized
  have hbk : pikeBlock re = re.novec * regSize := rfl
  have hlenB := buildLive_length false st ext
  have hlen : (buildLive false st ext).length ≤ re.code.size * 4 + 1 := by omega
  have hrcT : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2 :=
    fun hz => by have h2 := (take_room hown hlen hz).1; omega
  have hpoolT : st.free.size = 0 →
      st.pool.size + re.novec ≤ (re.code.size * 4 + 2) * re.novec := fun hz => by
    have h2 := (take_room hown hlen hz).2
    have hbb : re.code.size * 4 + 1 + 1 = re.code.size * 4 + 2 := by omega
    rwa [hbb] at h2
  have hch := pikeTake_charged (setup := setup) (novec := re.novec) (lim := lim)
    hwf hrooms hmem hrcT hpoolT
  have hsn := pikeTake_seen (st := st) (novec := re.novec) (lim := lim)
  simp only [pikeSeed]
  split
  · exact Tried.ofOk (Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _))
  · split
    · rename_i he
      refine Tried.error (Spent.mono (Spent.ofCharged (charged_of_error he hch)
        (seen_of_error he hsn)) (Nat.zero_le _)) ?_
      exact Blown.mono (pikeTake_refused (setup := setup) (novec := re.novec)
        (lim := lim) hwf hrooms hmem hrcT hpoolT he).blown (Nat.zero_le _)
    · rename_i stT sh ht
      have hspT : Spent re setup 0 st stT :=
        Spent.ofCharged (charged_ok_fst ht hch) (seen_ok_fst ht hsn)
      obtain ⟨htake, hsize⟩ := pikeTake_owned ht hown
      obtain ⟨hstkT, hseenT⟩ := pikeTake_ok ht
      obtain ⟨hclT, hnlT⟩ := pikeTake_lists ht
      have hpkT : parkList false stT = parkList false st := parkList_eq hclT hnlT
      have hblT : buildLive false stT ext = buildLive false st ext := by
        simp only [buildLive, hstkT, hpkT]
      split
      · rename_i htest
        refine Tried.error (Spent.mono hspT (Nat.zero_le _)) ?_
        exact Blown.mono (Blown.after hspT
          (Blown.ofCost (re.novec * regSize) hspT.rooms hspT.held htest))
          (by rw [hbk]; omega)
      · have hpay : Charged re setup (re.novec * regSize) stT
            { stT with
              m := { stT.m with cost := stT.m.cost + re.novec * regSize } } :=
          Charged.pay _ hspT.rooms hspT.held
        have hfill : Charged re setup (re.novec * regSize) stT
            { stT with
              m := { stT.m with cost := stT.m.cost + re.novec * regSize }
              pool := ((List.range re.novec).foldl
                (fun (pool : Array UInt32) k =>
                  pool.set! (sh * re.novec + k) unset32) stT.pool).set!
                (sh * re.novec) pos.toUInt32 } := by
          refine Charged.mono (hpay.trans (Charged.idle ?_ ?_ rfl hpay.held))
            (by omega)
          · exact ⟨hpay.rooms.clist, hpay.rooms.nlist, hpay.rooms.stk,
              hpay.rooms.rc, hpay.rooms.free, hpay.rooms.pool⟩
          · rfl
        have hpsize : (((List.range re.novec).foldl
              (fun (pool : Array UInt32) k =>
                pool.set! (sh * re.novec + k) unset32) stT.pool).set!
              (sh * re.novec) pos.toUInt32).size = stT.pool.size := by
          rw [Array.size_set!]
          exact foldl_size _ (fun a k => Array.size_set! _ _ _) _ _
        have hgo : ∀ stP : PikeSt, stP.clist = stT.clist →
            stP.nlist = stT.nlist → stP.stk = stT.stk → stP.seen = stT.seen →
            stP.rc = stT.rc → stP.free = stT.free →
            stP.pool.size = stT.pool.size →
            Charged re setup (re.novec * regSize) stT stP →
            Tried re setup (pikeBlock re) lim st id
              (pikeAdd re s mo lim false pos 0 sh stP) := by
          intro stP hcl hnl hstk hseen hrc hfree hpl hch
          have hpkP : parkList false stP = parkList false stT :=
            parkList_eq hcl hnl
          have hblP : buildLive false stP ext = buildLive false st ext := by
            simp only [buildLive, hstk, hstkT, hpkP, hpkT]
          refine Tried.mono
            (Tried.after (hspT.trans (Spent.ofCharged hch hseen))
              (pikeAdd_tried re s mo lim hwf false pos 0 sh setup ext
                (by rw [hseen, hseenT]; exact hsz)
                (by rw [hstk, hstkT]; exact hrange) hch.rooms hch.held ?_
                (by rw [hstk, hstkT]; exact hstk0)
                (by rw [hpkP, hpkT, hseen, hseenT]; exact hparked) ?_ ?_
                hwf.sized)) (by omega)
          · rw [hrc, hfree, hblP]
            exact Owned.ofPool htake hpl
          · simp only [addMeasure]
            rw [hstk, hstkT, hseen, hseenT, hpkP, hpkT]
            simp only [addMeasure] at hreach
            omega
          · rw [hrc]
            have hml : (buildLive false st ext).length ≤ re.code.size * 4 := by
              omega
            omega
        exact hgo _ rfl rfl rfl rfl rfl rfl hpsize hfill

/-! ### What a position costs, and a whole scan -/

theorem closureLeftFull_le_position (re : Re) :
    closureLeftFull re + pikeBlock re ≤ pikePosition re := by
  have h := position_split re
  omega

/-- What a stretch of positions may spend, weighed against the leftover the
scan has to show for the clear it made last: the charges plus a full visited
set's worth fit inside the account the stretch started from and the price of
the positions it covered. The leftover is not slack — it is what pays for the
seed of the position that follows, which draws on the set this stretch
cleared. -/
def Scanned (re : Re) (setup budget : Nat) (st out : PikeSt) : Prop :=
  ∃ spent, Charged re setup spent st out ∧
    spent + closureLeftFull re ≤ closureLeft re st.seen + budget

/-- And the same reading for a stretch that ended in a refusal: some state it
already covers has passed a limit. -/
def ScanBlown (re : Re) (setup budget : Nat) (lim : Limits) (st : PikeSt) :
    Prop :=
  ∃ out, Scanned re setup budget st out ∧ out.m.past lim

set_option maxHeartbeats 4000000 in
/-- The position loop, weighed. Each iteration seeds, clears the visited set,
and steps the list it built, and those three together are exactly BOUNDS.md
section 9's `2*C + (S + 2)*B + W`: the clear hands the step and the next
position's seed one set's worth of marks between them, the seed pays a block,
the step a unit per thread and a block for the accept.

The account carries a full set on the left because that is what the run has
to show for the clear it made last: at the last position the step opens no
closure, so the set cleared there is charged and never drawn on, and it is
that leftover which pays for the seed at the very first position — where the
set came from `pike_run` rather than from a clear.

The second reading is the same account over the charges the loop *attempts*.
It wants a step count that covers the scan, because the loop answers
`exceeded` on an exhausted one as well as on a refused charge, and the budget
has nothing to say about the first. -/
theorem pikeLoop_tried (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start : Nat) (anchored : Bool) (setup : Nat) :
    ∀ (steps pos : Nat) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      pos ≤ s.size → s.size + 1 - pos < steps → PosOk re st mh → Rooms re st →
      st.m.mem ≤ setup + st.reserved →
      Scanned re setup ((s.size + 1 - pos) * pikePosition re) st
          (pikeLoop re s mo lim start anchored (pikeWords re) steps pos st mh
            seeding matched).1 ∧
        ((pikeLoop re s mo lim start anchored (pikeWords re) steps pos st mh
            seeding matched).2.2 = .exceeded →
          ScanBlown re setup ((s.size + 1 - pos) * pikePosition re) lim st) := by
  intro steps
  induction steps with
  | zero =>
      intro pos st mh seeding matched _ hsteps _ _ _
      exact absurd hsteps (by omega)
  | succ k ih =>
      intro pos st mh seeding matched hple hsteps hok hrooms hmem
      have hC := hwf.sized
      have hFp := closureLeftFull_le_position re
      have hps := position_split re
      have hone : pikePosition re ≤ (s.size + 1 - pos) * pikePosition re :=
        Nat.le_mul_of_pos_left _ (by omega)
      have htwo : pos < s.size →
          pikePosition re + pikePosition re ≤
            (s.size + 1 - pos) * pikePosition re := by
        intro hlt
        have h2 : 2 * pikePosition re ≤ (s.size + 1 - pos) * pikePosition re :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hml := mhList_length mh
      have hmeas := LoopOk.addMeasure_le hok.loop hok.stk
      -- A refusal the price of one position still has room for.
      have hloose : ∀ e : Nat, e + closureLeftFull re ≤ pikePosition re →
          Blown re setup e lim st →
          ScanBlown re setup ((s.size + 1 - pos) * pikePosition re) lim st := by
        intro e hle hb
        obtain ⟨out, ⟨sp, hc, hsp⟩, hp⟩ := hb
        exact ⟨out, ⟨sp, hc, by omega⟩, hp⟩
      -- And one that fills a position, at a position that is not the last.
      have htight : pos < s.size → ∀ e : Nat, e ≤ pikePosition re →
          Blown re setup e lim st →
          ScanBlown re setup ((s.size + 1 - pos) * pikePosition re) lim st := by
        intro hlt e hle hb
        obtain ⟨out, ⟨sp, hc, hsp⟩, hp⟩ := hb
        have h2 := htwo hlt
        exact ⟨out, ⟨sp, hc, by omega⟩, hp⟩
      -- The seed, and what it leaves.
      have hseed : Tried re setup (pikeBlock re) lim st id
          (if seeding && (!anchored || pos == start) then
            pikeSeed re s mo lim start pos st
            else (Except.ok st : POut PikeSt)) := by
        split
        · refine pikeSeed_tried re s mo lim hwf start pos setup (mhList mh)
            hok.loop.build.seenSize hok.loop.build.stk hok.stk hrooms hmem
            hok.owned ?_ ?_ hok.pool
          · have hb := hok.loop.bounded
            have hpk : (parkList false st).size = st.clist.size := rfl
            omega
          · omega
        · exact Tried.ofOk (Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _))
      have hseeded : ∀ stS : PikeSt,
          (if seeding && (!anchored || pos == start) then
            pikeSeed re s mo lim start pos st
            else (Except.ok st : POut PikeSt)) = .ok stS →
          BuildOk re stS ∧
            stS.clist.size + stS.nlist.size + unmarked stS.seen ≤ re.code.size ∧
            stS.nlist.size = 0 ∧ stS.stk.size = 0 ∧
            Owned re.novec stS.rc stS.free stS.pool
              (buildLive false stS (mhList mh)) ∧
            stS.rc.size ≤ re.code.size * 4 + 2 := by
        intro stS hs
        have hbd := hok.loop.bounded
        have hem := hok.loop.empty
        have hp := hok.pool
        split at hs
        · obtain ⟨h1, h2, h3⟩ :=
            pikeSeed_build re s mo lim hwf start pos hs hok.loop.build
          obtain ⟨p1, p2, p3, p4, p5⟩ :=
            pikeSeed_owned re s mo lim start pos (mhList mh) hs
              hok.loop.build.seenSize hok.stk hok.owned
          simp only [buildMeasure] at h2
          have h3' := congrArg Array.size h3
          exact ⟨h1, by omega, by omega, p4, p1, by omega⟩
        · injection hs with hs
          subst hs
          exact ⟨hok.loop.build, by omega, hem, hok.stk, hok.owned, hok.pool⟩
      -- Cashing an exit out: the leftover of the last clear is what the
      -- account is missing, and a position that is not the last has a whole
      -- price still unspent.
      have hexit : ∀ stX : PikeSt, Spent re setup (pikePosition re) st stX →
          (s.size ≤ pos → closureLeft re stX.seen = closureLeftFull re) →
          Scanned re setup ((s.size + 1 - pos) * pikePosition re) st stX := by
        intro stX hsp hlast
        obtain ⟨sp, hc, hle⟩ := hsp
        refine ⟨sp, hc, ?_⟩
        rcases Nat.lt_or_ge pos s.size with hlt | hge
        · have h2 := htwo hlt
          omega
        · rw [hlast hge] at hle
          omega
      simp only [pikeLoop]
      split
      · rename_i stE hs
        refine ⟨?_, ?_⟩
        · obtain ⟨sp, hc, hle⟩ := spent_of_error hs hseed.1
          exact ⟨sp, hc, by omega⟩
        · intro _
          exact hloose _ (by omega) (hseed.2 stE hs)
      · rename_i stS hs
        have hspS : Spent re setup (pikeBlock re) st stS :=
          spent_ok_id hs hseed.1
        obtain ⟨hb, hbd, hemp, hstk0, hown, hpool⟩ := hseeded stS hs
        have hroomsS := hspS.rooms
        have hmemS := hspS.held
        have hcl : stS.clist.toList.length ≤ re.code.size := by
          rw [Array.length_toList]
          omega
        split
        · rename_i htest
          refine ⟨?_, ?_⟩
          · obtain ⟨sp, hc, hle⟩ := hspS
            exact ⟨sp, hc, by omega⟩
          · intro _
            refine hloose (pikeBlock re + pikeWords re) (by omega) ?_
            exact Blown.after hspS
              (Blown.ofCost (pikeWords re) hroomsS hmemS htest)
        · have hfull : unmarked (Array.replicate re.code.size false) ≤
              re.code.size := by
            have := unmarked_le_size (Array.replicate re.code.size false)
            simpa using this
          have hpayW : Charged re setup (pikeWords re) stS
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re } } :=
            Charged.pay _ hroomsS hmemS
          have hchW : Charged re setup (pikeWords re + 0) stS
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } :=
            hpayW.trans (Charged.idle
              ⟨hpayW.rooms.clist, hpayW.rooms.nlist, hpayW.rooms.stk,
                hpayW.rooms.rc, hpayW.rooms.free, hpayW.rooms.pool⟩ rfl rfl
              hpayW.held)
          have hclear : Spent re setup (closureLeftFull re + pikeWords re) stS
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } := by
            refine ⟨pikeWords re + 0, hchW, ?_⟩
            show closureLeft re (Array.replicate re.code.size false) +
              (pikeWords re + 0) ≤ closureLeft re stS.seen +
                (closureLeftFull re + pikeWords re)
            rw [closureLeft_replicate]
            omega
          have hmC : addMeasure true { stS with
              m := { stS.m with cost := stS.m.cost + pikeWords re }
              seen := Array.replicate re.code.size false } +
              stS.clist.toList.length + 1 ≤ re.code.size * 3 + 1 := by
            show stS.stk.size + stS.nlist.size +
              2 * unmarked (Array.replicate re.code.size false) +
              stS.clist.toList.length + 1 ≤ re.code.size * 3 + 1
            rw [Array.length_toList]
            omega
          have hlists : buildLive true { stS with
              m := { stS.m with cost := stS.m.cost + pikeWords re }
              seen := Array.replicate re.code.size false }
              (stS.clist.toList.map Th.h ++ mhList mh) =
              buildLive false stS (mhList mh) := by
            show handles stS.stk ++ handles stS.nlist ++
                (stS.clist.toList.map Th.h ++ mhList mh) =
              handles stS.stk ++ handles stS.clist ++ mhList mh
            rw [handles_empty hemp]
            simp [handles]
          have hstepSp := stepThreads_tried re s mo lim hwf start pos setup
            stS.clist.toList
            { stS with
              m := { stS.m with cost := stS.m.cost + pikeWords re }
              seen := Array.replicate re.code.size false }
            mh seeding matched
            ⟨by simp, hb.stk, hb.clist, hb.nlist⟩ hstk0 hb.clist
            hchW.rooms hchW.held (by rw [hlists]; exact hown)
            (by
              show stS.nlist.size + unmarked (Array.replicate re.code.size false)
                ≤ re.code.size
              omega) hmC hpool
          have hpospr : ∀ stX : PikeSt,
              Spent re setup (stS.clist.toList.length + pikeBlock re)
                { stS with
                  m := { stS.m with cost := stS.m.cost + pikeWords re }
                  seen := Array.replicate re.code.size false } stX →
              Spent re setup (pikePosition re) st stX := by
            intro stX h
            refine Spent.mono ((hspS.trans hclear).trans h) ?_
            omega
          have hposbl : Blown re setup
                (stS.clist.toList.length + pikeBlock re) lim
                { stS with
                  m := { stS.m with cost := stS.m.cost + pikeWords re }
                  seen := Array.replicate re.code.size false } →
              Blown re setup (pikePosition re) lim st := by
            intro h
            refine Blown.mono (Blown.after (hspS.trans hclear) h) ?_
            omega
          -- At the last position the step marks nothing, so the set the
          -- position cleared is charged and never drawn on.
          have hposlast : s.size ≤ pos → ∀ stX : PikeSt,
              stepThreads re s mo lim start pos stS.clist.toList
                  { stS with
                    m := { stS.m with cost := stS.m.cost + pikeWords re }
                    seen := Array.replicate re.code.size false }
                  mh seeding matched = .error stX →
              ScanBlown re setup
                ((s.size + 1 - pos) * pikePosition re) lim st := by
            intro hge stX hx
            obtain ⟨out, hcOut, -, hpast⟩ :=
              stepThreads_last re s mo lim hwf start pos setup hge
                stS.clist.toList _ mh seeding matched stX hchW.rooms hchW.held
                (by rw [hlists]; exact hown) hmC hpool hx
            obtain ⟨sp₁, hc₁, hle₁⟩ := hspS
            refine ⟨out, ⟨sp₁ + (pikeWords re + 0) +
              (stS.clist.toList.length + pikeBlock re),
              (hc₁.trans hchW).trans hcOut, ?_⟩, hpast⟩
            omega
          have hseenW := fun (hge : s.size ≤ pos) =>
            stepThreads_seen re s mo lim start pos hge stS.clist.toList
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } mh seeding matched
          split
          · rename_i stE hx
            refine ⟨hexit stE (hpospr _ (spent_of_error hx hstepSp.1)) ?_, ?_⟩
            · intro hge
              rw [seen_of_error hx (hseenW hge)]
              exact closureLeft_replicate re
            · intro _
              rcases Nat.lt_or_ge pos s.size with hlt | hge
              · exact htight hlt _ (Nat.le_refl _)
                  (hposbl (hstepSp.2 stE hx))
              · exact hposlast hge stE hx
          · rename_i out hx
            have hspO : Spent re setup (pikePosition re) st out.st :=
              hpospr _ (spent_ok_step hx hstepSp.1)
            have hseenO := fun (hge : s.size ≤ pos) =>
              seen_ok_step hx (hseenW hge)
            obtain ⟨o1, o2, o3⟩ := stepThreads_build re s mo lim hwf start pos
              stS.clist.toList _ mh seeding matched out hx hb.clist
              ⟨by simp, hb.stk, hb.clist, hb.nlist⟩
            obtain ⟨q1, q2, q3, q4, q5⟩ :=
              stepThreads_owned re s mo lim start pos (re.code.size * 3 + 1)
                stS.clist.toList _ mh seeding matched out hx (by simp) hstk0
                hmC (by rw [hlists]; exact hown)
            have hrec : buildMeasure { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } =
                stS.clist.size + stS.nlist.size +
                  unmarked (Array.replicate re.code.size false) := rfl
            rw [hrec] at o2
            simp only [buildMeasure] at o2
            have o3' : out.st.clist.size = stS.clist.size := by rw [o3]
            have hroomsO := hspO.rooms
            have hroomsN : Rooms re { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } :=
              ⟨hroomsO.nlist, hroomsO.clist, hroomsO.stk, hroomsO.rc,
                hroomsO.free, hroomsO.pool⟩
            have hresN : ({ out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } : PikeSt).reserved =
                out.st.reserved := by
              simp only [PikeSt.reserved, thSize, regSize]
              omega
            have hspN : Spent re setup (pikePosition re) st { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } :=
              Spent.mono (hspO.trans (Spent.ofCharged
                (Charged.idle hroomsN hresN rfl hspO.held) rfl)) (by omega)
            have hfin : PosOk re { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } out.mh := by
              refine ⟨⟨⟨o1.seenSize, o1.stk, o1.nlist, ?_⟩, rfl, ?_⟩, ?_, q1, ?_⟩
              · intro y hy
                simp at hy
              · simp only []
                omega
              · show out.st.stk.size = 0
                exact q4
              · show out.st.rc.size ≤ re.code.size * 4 + 2
                have hq : out.st.rc.size ≤
                    max stS.rc.size (re.code.size * 3 + 1 + 2) := q5
                omega
            have hsettled : ∀ stY : PikeSt, ∀ mY : Nat,
                (stY, mY, if out.matched then PikeEnd.matched
                  else PikeEnd.noMatch).2.2 = PikeEnd.exceeded →
                ScanBlown re setup
                  ((s.size + 1 - pos) * pikePosition re) lim st := by
              intro stY mY hexc
              simp only [] at hexc
              split at hexc <;> exact absurd hexc (by decide)
            split
            · refine ⟨hexit _ hspN ?_, hsettled _ _⟩
              intro hge
              show closureLeft re out.st.seen = closureLeftFull re
              rw [hseenO hge]
              exact closureLeft_replicate re
            · split
              · refine ⟨hexit _ hspN ?_, hsettled _ _⟩
                intro hge
                show closureLeft re out.st.seen = closureLeftFull re
                rw [hseenO hge]
                exact closureLeft_replicate re
              · rename_i hnot
                have hlt : pos < s.size := by
                  rename_i hge
                  simp only [Nat.not_le] at hge
                  omega
                obtain ⟨hrest, hrestB⟩ := ih (pos + 1) _ out.mh out.seeding
                  out.matched (by omega) (by omega) hfin hroomsN
                  (by rw [hresN]; exact hspO.held)
                have hsplit : (s.size + 1 - pos) * pikePosition re =
                    pikePosition re +
                      (s.size + 1 - (pos + 1)) * pikePosition re := by
                  have he : s.size + 1 - pos = (s.size + 1 - (pos + 1)) + 1 := by
                    omega
                  rw [he, Nat.succ_mul]
                  omega
                refine ⟨?_, ?_⟩
                · obtain ⟨sp', hc', hle'⟩ := hrest
                  obtain ⟨sp, hc, hle⟩ := hspN
                  exact ⟨sp + sp', hc.trans hc', by omega⟩
                · intro hexc
                  obtain ⟨outB, ⟨sp', hc', hle'⟩, hpast⟩ := hrestB hexc
                  obtain ⟨sp, hc, hle⟩ := hspN
                  exact ⟨outB, ⟨sp + sp', hc.trans hc', by omega⟩, hpast⟩

/-! ### What a whole call spends, against its certificate

R-6 and R-8 for this configuration, at the shape a caller reads them: the
cost a lockstep run reports and the memory it peaks at are inside the closed
form of BOUNDS.md section 9, and so inside anything the checker accepted. The
run is taken at its own call shape — a context handed over with nothing
pre-reserved, which is what `{}` says — because the `3R` in the cost line is
amortized against a reservation that starts at nothing. -/

/-- R-6 for `CfgPike`: a run's cost is the setup, the delivered answer, three
times the reservation, and one position's price per starting position. -/
theorem pikeRun_cost_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} (hwf : ReWf re) (hflag : (pikeRoom re false).2 = false) :
    (pikeRun re s start mo lim {}).usage.cost ≤
      pikeSetup re + pikeBlock re + 3 * pikeReserved re +
        pikePosition re * (s.size + 1) := by
  have hscr := pikeScratch_eq hflag
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i hstart
      simp only [Nat.not_lt] at hstart
      split
      · exact Nat.zero_le _
      · have hgo : ∀ st0 : PikeSt, Rooms re st0 → PosOk re st0 none32 →
            st0.reserved = 0 → st0.m.cost = pikeSetup re →
            st0.m.mem = pikeSetup re →
            closureLeft re st0.seen = closureLeftFull re →
            (pikeLoop re s mo lim start (re.anchored || mo.anchored)
                (re.code.size / 8 + 1) (s.size + 2) start st0 none32 true
                false).1.m.cost + re.novec * regSize ≤
              pikeSetup re + pikeBlock re + 3 * pikeReserved re +
                pikePosition re * (s.size + 1) := by
          intro st0 hr hp hres0 hcost0 hmem0 hseen0
          obtain ⟨spent, hch, hle⟩ := (pikeLoop_tried re s mo lim hwf start
            (re.anchored || mo.anchored) (pikeSetup re) (s.size + 2) start st0
            none32 true false hstart (by omega) hp hr
            (by rw [hmem0, hres0]; omega)).1
          have hres := hch.rooms.scratch_le
          have hcharge := hch.charge
          rw [hres0, hcost0] at hcharge
          rw [hseen0] at hle
          have hmul : (s.size + 1 - start) * pikePosition re ≤
              pikePosition re * (s.size + 1) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left _ (by omega)
          have hbk : pikeBlock re = re.novec * regSize := rfl
          show (pikeLoop re s mo lim start (re.anchored || mo.anchored)
              (pikeWords re) (s.size + 2) start st0 none32 true false).1.m.cost +
            re.novec * regSize ≤ _
          omega
        have hweak : ∀ st0 : PikeSt, Rooms re st0 → PosOk re st0 none32 →
            st0.reserved = 0 → st0.m.cost = pikeSetup re →
            st0.m.mem = pikeSetup re →
            closureLeft re st0.seen = closureLeftFull re →
            (pikeLoop re s mo lim start (re.anchored || mo.anchored)
                (re.code.size / 8 + 1) (s.size + 2) start st0 none32 true
                false).1.m.cost ≤
              pikeSetup re + pikeBlock re + 3 * pikeReserved re +
                pikePosition re * (s.size + 1) := by
          intro st0 h1 h2 h3 h4 h5 h6
          have := hgo st0 h1 h2 h3 h4 h5 h6
          omega
        split
        · exact hweak _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
            (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
            (closureLeft_replicate re)
        · exact hweak _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
            (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
            (closureLeft_replicate re)
        · split
          · exact hweak _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
              (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
              (closureLeft_replicate re)
          · exact hgo _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
              (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
              (closureLeft_replicate re)

/-- R-8 for `CfgPike`: the memory a run peaks at is the setup and twice the
reservation, whatever the scan does — a number that does not move with the
subject, which is what lets a context be sized once. -/
theorem pikeRun_mem_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} (hwf : ReWf re) (hflag : (pikeRoom re false).2 = false) :
    (pikeRun re s start mo lim {}).usage.mem ≤
      pikeSetup re + pikeBlock re + 2 * pikeReserved re := by
  have hscr := pikeScratch_eq hflag
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i hstart
      simp only [Nat.not_lt] at hstart
      split
      · exact Nat.zero_le _
      · have hgo : ∀ st0 : PikeSt, Rooms re st0 → PosOk re st0 none32 →
            st0.reserved = 0 → st0.m.peak = pikeSetup re →
            st0.m.mem = pikeSetup re →
            (pikeLoop re s mo lim start (re.anchored || mo.anchored)
                (re.code.size / 8 + 1) (s.size + 2) start st0 none32 true
                false).1.m.peak ≤
              pikeSetup re + pikeBlock re + 2 * pikeReserved re := by
          intro st0 hr hp hres0 hpeak0 hmem0
          obtain ⟨spent, hch, hle⟩ := (pikeLoop_tried re s mo lim hwf start
            (re.anchored || mo.anchored) (pikeSetup re) (s.size + 2) start st0
            none32 true false hstart (by omega) hp hr
            (by rw [hmem0, hres0]; omega)).1
          have hpeak := hch.resident_le (by rw [hmem0, hres0]; omega)
          rw [hpeak0] at hpeak
          show (pikeLoop re s mo lim start (re.anchored || mo.anchored)
              (pikeWords re) (s.size + 2) start st0 none32 true false).1.m.peak ≤ _
          omega
        split
        · exact hgo _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
            (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
        · exact hgo _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
            (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
        · split
          · exact hgo _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
              (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl
          · exact hgo _ (Rooms.zero rfl rfl rfl rfl rfl rfl)
              (pikeRun_posOk re {} _) (by simp [PikeSt.reserved]) rfl rfl

/-- The same against the price the analyzer computes. -/
theorem pikeRun_cost_le_price {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hwf : ReWf re)
    (h : pikePrice re = some cert) :
    (pikeRun re s start mo lim {}).usage.cost ≤ cert.cost.val s.size := by
  obtain ⟨hflag, -⟩ := pikePrice_eq h
  rw [pikePrice_cost_val h]
  exact pikeRun_cost_le hwf hflag

theorem pikeRun_mem_le_price {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hwf : ReWf re)
    (h : pikePrice re = some cert) :
    (pikeRun re s start mo lim {}).usage.mem ≤ cert.mem.val s.size := by
  obtain ⟨hflag, -⟩ := pikePrice_eq h
  rw [pikePrice_mem_val h]
  exact pikeRun_mem_le hwf hflag

/-- And against any certificate the checker accepted, which is the form R-6
is stated in: an accepted claim dominates the price, and the price bounds the
run. -/
theorem pikeRun_cost_le_check {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hwf : ReWf re)
    (h : pikeCheck re cert = .crOk) :
    (pikeRun re s start mo lim {}).usage.cost ≤ cert.cost.val s.size := by
  obtain ⟨-, -, -, -, need, hneed, -, -, -, -⟩ := pikeCheck_spec h
  obtain ⟨hflag, -⟩ := pikePrice_eq hneed
  exact Nat.le_trans (pikeRun_cost_le hwf hflag) (pikeCheck_cost_dom h s.size)

/-- R-8, the same way. -/
theorem pikeRun_mem_le_check {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hwf : ReWf re)
    (h : pikeCheck re cert = .crOk) :
    (pikeRun re s start mo lim {}).usage.mem ≤ cert.mem.val s.size := by
  obtain ⟨-, -, -, -, need, hneed, -, -, -, -⟩ := pikeCheck_spec h
  obtain ⟨hflag, -⟩ := pikePrice_eq hneed
  exact Nat.le_trans (pikeRun_mem_le hwf hflag) (pikeCheck_mem_dom h s.size)

/-! ### The two, as the accessors report them

R-7's accessor form is `pikeRun_stack_le` above, which needs nothing of the
certificate at all. -/

/-- R-6 as a caller reads it: the cost accessor's own number bounds the run.
An accessor that answered a number answered the bound's value at that length,
since the ceiling test only ever turns a number into a refusal. -/
theorem pikeRun_cost_le_bound {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start v : Nat} {cert : Cert} (hwf : ReWf re)
    (h : pikeCheck re cert = .crOk)
    (hb : certBound cert .cost s.size = ⟨true, v⟩) :
    (pikeRun re s start mo lim {}).usage.cost ≤ v := by
  have hv : v = cert.cost.val s.size := by
    simp only [certBound] at hb
    split at hb
    · exact absurd hb (by simp [Bound.exceeds])
    · exact polyValue_ok hb
  rw [hv]
  exact pikeRun_cost_le_check hwf h

/-- And R-8. -/
theorem pikeRun_mem_le_bound {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start v : Nat} {cert : Cert} (hwf : ReWf re)
    (h : pikeCheck re cert = .crOk)
    (hb : certBound cert .mem s.size = ⟨true, v⟩) :
    (pikeRun re s start mo lim {}).usage.mem ≤ v := by
  have hv : v = cert.mem.val s.size := by
    simp only [certBound] at hb
    split at hb
    · exact absurd hb (by simp [Bound.exceeds])
    · exact polyValue_ok hb
  rw [hv]
  exact pikeRun_mem_le_check hwf h

/-! ### A sufficient budget, and the absence of a refusal

S-10 for this configuration. A refusal on this path is a pre-charge test
failing, and the attempt reading above says what every one of those tests was
asking for. Against limits that dominate an accepted certificate no such
charge fits above the ceiling, so no test can fail: the setup guard is the
certificate's own two dominations, the loop's `exceeded` is the attempt
reading cashed out, and the delivered block is what `pikeRun_cost_le` already
leaves room for. -/

/-- S-10 for `CfgPike`, at any call shape the growth schedule admits: a
caller whose cost and memory limits sit at or above what an accepted
certificate names never sees ResourceExceeded, whether it starts on empty
scratch or on a context's reservation. The stack limit does not appear,
because nothing on this path is ever pushed, and neither does the eligibility
flag, because a run that fails that test answers BadInput rather than a
refusal. The start offset is here for the account rather than for the guard:
the price covers `n + 1` starting positions and the scan is entered at one of
them.

`Rooms re init` is what the handed-over scratch has to satisfy, and it is
what a context creation leaves behind: every capacity inside the growth
schedule's own answer at its array's entry bound. It is doing real work. The
`3R` and `2R` of BOUNDS.md section 9 are read against that schedule, so a
caller who arrived with more reserved than the schedule ever asks for would
be running under a price that was never computed for it.

Nothing else changes with the reservation. `pike_run` resets every array and
puts the meter back at the setup, so the only difference between this call
and a plain one is the six capacities it did not have to buy.

`ReWf` is here for the same reason it is everywhere else in this file: the
per-position count rests on the closure marking each instruction once, and
that needs the program's successors to stay inside the program. -/
theorem pikeRun_inBudget_ctx {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {init : PikeSt} {cert : Cert} (hwf : ReWf re)
    (hinit : Rooms re init) (hstart : start ≤ s.size)
    (h : pikeCheck re cert = .crOk)
    (hcost : cert.cost.val s.size ≤ lim.cost)
    (hmem : cert.mem.val s.size ≤ lim.mem) :
    (pikeRun re s start mo lim init).outcome ≠ .resourceExceeded := by
  have hdomc := pikeCheck_cost_dom h s.size
  have hdomm := pikeCheck_mem_dom h s.size
  obtain ⟨-, -, -, -, need, hneed, -, -, -, -⟩ := pikeCheck_spec h
  obtain ⟨hflag, -⟩ := pikePrice_eq hneed
  have hscr := pikeScratch_eq hflag
  have hbk : pikeBlock re = re.novec * regSize := rfl
  have hwd : pikeWords re = re.code.size / 8 + 1 := rfl
  have hsu : pikeSetup re = pikeBlock re + pikeWords re := rfl
  -- The loop, once its budget is read against the certificate: it cannot end
  -- exceeded, and it leaves room for the block the answer is copied into.
  have hgo : ∀ st0 : PikeSt, Rooms re st0 → PosOk re st0 none32 →
      st0.m.cost = pikeSetup re →
      st0.m.mem = pikeSetup re → st0.m.peak = pikeSetup re →
      closureLeft re st0.seen = closureLeftFull re →
      (pikeLoop re s mo lim start (re.anchored || mo.anchored)
          (pikeWords re) (s.size + 2) start st0 none32 true false).2.2 ≠
        .exceeded ∧
      ¬ re.novec * regSize >
        lim.cost - (pikeLoop re s mo lim start (re.anchored || mo.anchored)
          (pikeWords re) (s.size + 2) start st0 none32 true false).1.m.cost := by
    intro st0 hr hp hcost0 hmem0 hpeak0 hseen0
    obtain ⟨hsp, hbl⟩ := pikeLoop_tried re s mo lim hwf start
      (re.anchored || mo.anchored) (pikeSetup re) (s.size + 2) start st0
      none32 true false hstart (by omega) hp hr (by rw [hmem0]; omega)
    have hmul : (s.size + 1 - start) * pikePosition re ≤
        pikePosition re * (s.size + 1) := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    refine ⟨?_, ?_⟩
    · intro hexc
      obtain ⟨out, ⟨spB, hcB, hleB⟩, hpast⟩ := hbl hexc
      have hresB := hcB.rooms.scratch_le
      have hchB := hcB.charge
      have hpk := hcB.resident_le (by rw [hmem0]; omega)
      rw [hcost0] at hchB
      rw [hpeak0] at hpk
      rw [hseen0] at hleB
      rcases hpast with hc | hm
      · omega
      · omega
    · obtain ⟨spent, hc, hle⟩ := hsp
      have hres := hc.rooms.scratch_le
      have hcharge := hc.charge
      rw [hcost0] at hcharge
      rw [hseen0] at hle
      omega
  have hrooms0 : ∀ setup : Nat, Rooms re { init with
      clist := #[], nlist := #[], stk := #[]
      pool := #[], rc := #[], free := #[]
      seen := Array.replicate re.code.size false
      m := ⟨setup, setup, setup⟩ } :=
    fun _ => ⟨hinit.clist, hinit.nlist, hinit.stk, hinit.rc, hinit.free,
      hinit.pool⟩
  simp only [pikeRun]
  split
  · simp
  · split
    · simp
    · split
      · rename_i hguard
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hguard
        rcases hguard with hg | hg <;> omega
      · split
        · rename_i hend
          exact absurd hend (hgo _ (hrooms0 _)
            (pikeRun_posOk re init _) rfl rfl rfl
            (closureLeft_replicate re)).1
        · simp
        · split
          · rename_i hblock
            exact absurd hblock (hgo _ (hrooms0 _)
              (pikeRun_posOk re init _) rfl rfl rfl
              (closureLeft_replicate re)).2
          · simp

/-- S-10 at the plain call shape, which is what a caller with no context
reaches for. -/
theorem pikeRun_inBudget {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert} (hwf : ReWf re)
    (hstart : start ≤ s.size) (h : pikeCheck re cert = .crOk)
    (hcost : cert.cost.val s.size ≤ lim.cost)
    (hmem : cert.mem.val s.size ≤ lim.mem) :
    (pikeRun re s start mo lim {}).outcome ≠ .resourceExceeded :=
  pikeRun_inBudget_ctx hwf (Rooms.zero rfl rfl rfl rfl rfl rfl) hstart h hcost
    hmem

/-! ## R-9's no-allocation clause for a lockstep call

`btRun_no_growth_forward` says a backtracking call whose two scratch arrays
already hold the claims never grows either of them. A lockstep call has six
arrays rather than two, and what stands in for the claims is the growth
schedule's own answer at each array's entry bound — the four numbers
`pikeRoom` weighs, which is what creation reserves and what `ctx_match` hands
over.

The argument is the account above, read the other way round. `Charged` says a
stretch never reserves more than the schedule allows; it also says a stretch
never gives a reservation back, and that the resident reading moves with the
reservation and with nothing else. A call that arrives at the schedule's
ceiling is therefore pinned to it, and being pinned is what leaves the meter
alone.

Nothing here mentions the caller's limits, for the same reason nothing does
on the backtracking side: a run that never grows never reaches a growth test,
and the tests that remain can refuse without allocating. -/

/-- Every array of a state at the growth schedule's final capacity for its own
entry bound. These are the four numbers `pikeRoom` weighs, at the shape
`ctx_match` hands them over in: the two thread lists share a capacity, and the
refcount table shares one with the free list. -/
structure Reserved (re : Re) (st : PikeSt) : Prop where
  clist : st.clistCap = capFor re.code.size
  nlist : st.nlistCap = capFor re.code.size
  stk : st.stkCap = capFor (re.code.size * 2)
  rc : st.rcCap = capFor (re.code.size * 4 + 2)
  free : st.freeCap = capFor (re.code.size * 4 + 2)
  pool : st.poolCap = capFor ((re.code.size * 4 + 2) * re.novec)

/-- Such a state is inside every room, with nothing to spare. -/
theorem Reserved.rooms {re : Re} {st : PikeSt} (h : Reserved re st) :
    Rooms re st :=
  ⟨Nat.le_of_eq h.clist, Nat.le_of_eq h.nlist, Nat.le_of_eq h.stk,
    Nat.le_of_eq h.rc, Nat.le_of_eq h.free, Nat.le_of_eq h.pool⟩

/-- And it holds exactly BOUNDS.md section 9's `R`. -/
theorem Reserved.scratch {re : Re} {st : PikeSt} (h : Reserved re st) :
    st.reserved = pikeScratch re := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [PikeSt.reserved, pikeScratch, h1, h2, h3, h4, h5, h6, thSize,
    regSize]
  omega

/-- And the capacities `pike_room` weighs are exactly that ceiling, which is
what a context creation reserves — `ctx_create` takes its four numbers off
this same call, and `ctx_match` hands them down in this shape. -/
theorem Reserved.ofRoom {re : Re} {room : Room} {over : Bool}
    (h : pikeRoom re over = (room, false)) :
    Reserved re
      { clistCap := room.lists
        nlistCap := room.lists
        stkCap := room.stk
        poolCap := room.pool
        rcCap := room.tables
        freeCap := room.tables } := by
  obtain ⟨-, hl, hs, ht, hp, -⟩ := pikeRoom_spec h
  exact ⟨hl, hl, hs, ht, ht,
    by rw [hp, Re.novec, Nat.mul_comm 2 (re.ncap + 1)]⟩

/-- A stretch that started at the ceiling ends there. The schedule bounds
every capacity from above and a stretch never gives one back, so the two
readings leave no room for a capacity to have moved. -/
theorem Charged.reserved {re : Re} {setup c : Nat} {st out : PikeSt}
    (h : Charged re setup c st out) (hst : Reserved re st) :
    Reserved re out := by
  have hfull : out.reserved = pikeScratch re := by
    have hle := h.rooms.scratch_le
    have hg := h.grown
    rw [hst.scratch] at hg
    omega
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h.rooms
  simp only [PikeSt.reserved, pikeScratch, thSize, regSize] at hfull
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The scan itself, at a call that had nothing left to buy: every capacity
comes out where it went in, the resident reading does not move, and the peak
does not rise. -/
theorem pikeLoop_no_growth {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {anchored : Bool} {setup steps pos mh : Nat}
    {st : PikeSt} {seeding matched : Bool} (hwf : ReWf re)
    (hres : Reserved re st) (hok : PosOk re st mh) (hpos : pos ≤ s.size)
    (hsteps : s.size + 1 - pos < steps) (hmem : st.m.mem = setup)
    (hpeak : st.m.peak = setup) :
    Reserved re (pikeLoop re s mo lim start anchored (pikeWords re) steps pos
        st mh seeding matched).1 ∧
      (pikeLoop re s mo lim start anchored (pikeWords re) steps pos st mh
          seeding matched).1.m.mem = setup ∧
      (pikeLoop re s mo lim start anchored (pikeWords re) steps pos st mh
          seeding matched).1.m.peak ≤ setup := by
  obtain ⟨spent, hch, -⟩ := (pikeLoop_tried re s mo lim hwf start anchored setup
    steps pos st mh seeding matched hpos hsteps hok hres.rooms
    (by rw [hmem]; omega)).1
  have hout := hch.reserved hres
  have hin := hres.scratch
  have hfin := hout.scratch
  have hmv := hch.moved
  have hrs := hch.resident
  exact ⟨hout, by omega, by omega⟩

/-- R-9's no-allocation clause for `CfgPike`: a call handed six scratch
arrays already reserved at the growth schedule's final capacities allocates
nothing, so the resident bytes it reports are the ovector and the visited set
it was given and nothing else.

The statement is about capacities and asks nothing of the caller's limits,
which is what makes it the lockstep twin of `btRun_no_growth_forward`. What
it does ask for is the program, through `ReWf`: the reading that pins the
capacities is the growth account of this file, and that account is kept
against entry bounds read off the program. -/
theorem pikeRun_no_growth {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {init : PikeSt} (hwf : ReWf re) (hinit : Reserved re init) :
    (pikeRun re s start mo lim init).usage.mem ≤ pikeSetup re := by
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i hstart
      simp only [Nat.not_lt] at hstart
      split
      · exact Nat.zero_le _
      · have hgo : ∀ st0 : PikeSt, Reserved re st0 → PosOk re st0 none32 →
            st0.m.mem = pikeSetup re → st0.m.peak = pikeSetup re →
            (pikeLoop re s mo lim start (re.anchored || mo.anchored)
                (re.code.size / 8 + 1) (s.size + 2) start st0 none32 true
                false).1.m.peak ≤ pikeSetup re := by
          intro st0 hr hp hmem0 hpeak0
          exact (pikeLoop_no_growth (lim := lim) (start := start)
            (anchored := re.anchored || mo.anchored) (steps := s.size + 2)
            (seeding := true) (matched := false) hwf hr hp hstart (by omega)
            hmem0 hpeak0).2.2
        have hres0 : ∀ setup : Nat, Reserved re { init with
            clist := #[], nlist := #[], stk := #[]
            pool := #[], rc := #[], free := #[]
            seen := Array.replicate re.code.size false
            m := ⟨setup, setup, setup⟩ } :=
          fun _ => ⟨hinit.clist, hinit.nlist, hinit.stk, hinit.rc, hinit.free,
            hinit.pool⟩
        split
        · exact hgo _ (hres0 _) (pikeRun_posOk re init _) rfl rfl
        · exact hgo _ (hres0 _) (pikeRun_posOk re init _) rfl rfl
        · split
          · exact hgo _ (hres0 _) (pikeRun_posOk re init _) rfl rfl
          · exact hgo _ (hres0 _) (pikeRun_posOk re init _) rfl rfl

end Pcrevera.Ref
