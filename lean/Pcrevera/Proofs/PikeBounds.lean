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

Seven things live here.

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
which is how `4*C + 2` will be read off the lists rather than off the number
of allocations. Naming the handles a running state carries is left for the
per-position accounting, so what is here is the reading and its algebra.

Seventh is the growth schedule, weighed. `charge_grow` clamps at a declared
maximum, and the section 9 accounting only reads as `3R` and `2R` if the
schedule is left to grow; the clamp is out of reach here because every array
has an entry bound read off the program and the four maxima of `Pike.lean`
sit above twice the largest such bound. That is what `ReWf.coded` and
`ReWf.slots` are in the predicate for.

What is not here yet is the step that joins the closed form to the run: that
the charges a run actually makes stay under it. Its three ingredients — the
dedup, the ownership, the growth schedule — are all below, but the
per-position accounting that composes them is not, and neither is the
closure stack's own `C + 1` bound, which both the pool count and the stack's
growth arm want. Until that lands, R-6 and R-8 hold against the caller's
limits rather than against the certificate, and S-10's Pike half is out of
reach. `ReWf` itself is a hypothesis: it is a fact about compiler output,
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
that anyone still holds. The two arrays travel on their own because that is
all of a state the reading looks at. -/
structure Owned (rc free : Array Nat) (live : List Nat) : Prop where
  capped : rc.size ≤ maxBlocks
  reach : ∀ h ∈ live, h < rc.size
  count : ∀ h, h < rc.size → rc[h]! = live.count h
  onFree : ∀ h, h < rc.size → (rc[h]! = 0 ↔ 0 < free.toList.count h)
  freeRange : ∀ h ∈ free.toList, h < rc.size
  freeOnce : ∀ h, free.toList.count h ≤ 1

/-- Which order the caller lists its handles in is not the pool's business. -/
theorem Owned.perm {rc free : Array Nat} {l₁ l₂ : List Nat}
    (h : Owned rc free l₁) (hp : l₂.Perm l₁) : Owned rc free l₂ where
  capped := h.capped
  reach := fun x hx => h.reach x (hp.mem_iff.mp hx)
  count := fun x hx => by rw [h.count x hx, hp.count_eq]
  onFree := h.onFree
  freeRange := h.freeRange
  freeOnce := h.freeOnce

/-- The payoff: a block is on the free list or someone holds it, so there
are no more blocks than the free list and the live handles together have
room for. -/
theorem Owned.size_le {rc free : Array Nat} {live : List Nat}
    (h : Owned rc free live) : rc.size ≤ free.size + live.length := by
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
theorem owned_release {rc free : Array Nat} {h : Nat} {rest : List Nat}
    (how : Owned rc free (h :: rest)) (hpos : 0 < rest.count h) :
    Owned (rc.set! h (rc[h]! - 1)) free rest := by
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
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, how.freeOnce⟩
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
theorem owned_free {rc free : Array Nat} {h : Nat} {rest : List Nat}
    (how : Owned rc free (h :: rest)) (hz : rest.count h = 0) :
    Owned (rc.set! h (rc[h]! - 1)) (free.push h) rest := by
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
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, ?_⟩
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
theorem owned_share {rc free : Array Nat} {h : Nat} {rest : List Nat}
    (how : Owned rc free (h :: rest)) :
    Owned (rc.set! h (rc[h]! + 1)) free (h :: h :: rest) := by
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
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, how.freeOnce⟩
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
theorem owned_reuse {rc free : Array Nat} {live : List Nat}
    (how : Owned rc free live) (hpos : 0 < free.size) :
    Owned (rc.set! free.back! 1) free.pop (free.back! :: live) := by
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
  refine ⟨by rw [hsize]; exact how.capped, ?_, ?_, ?_, ?_, ?_⟩
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
theorem owned_fresh {rc free : Array Nat} {live : List Nat}
    (how : Owned rc free live) (hnil : free.size = 0) (hcap : rc.size < maxBlocks) :
    Owned (rc.push 1) free (rc.size :: live) := by
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
  refine ⟨by rw [hsz]; omega, ?_, ?_, ?_, ?_, ?_⟩
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
    st'.rc = st.rc ∧ st'.free = st.free := by
  unfold pikeDefer at hok
  split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩

theorem pikePark_pool {st st' : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} (hok : pikePark st intoNext pc h lim = .ok st') :
    st'.rc = st.rc ∧ st'.free = st.free := by
  unfold pikePark at hok
  split at hok <;> split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩

theorem pikeTake_fill_pool {lim : Limits} : ∀ {k : Nat} {st st' : PikeSt},
    pikeTake.fill lim k st = .ok st' → st'.rc = st.rc ∧ st'.free = st.free := by
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

/-! ### The helpers, read against the state -/

/-- Letting a handle go. The block returns to the free list exactly when its
last holder let it go. -/
theorem pikeDrop_owned {st st' : PikeSt} {h : Nat} {rest : List Nat}
    {lim : Limits} (hok : pikeDrop st h lim = .ok st')
    (how : Owned st.rc st.free (h :: rest)) : Owned st'.rc st'.free rest := by
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
theorem pikeDrop_none_owned {st st' : PikeSt} {live : List Nat} {lim : Limits}
    (hok : pikeDrop st none32 lim = .ok st')
    (how : Owned st.rc st.free live) : Owned st'.rc st'.free live := by
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
    (how : Owned st.rc st.free live) :
    Owned st'.rc st'.free (hOut :: live) ∧
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
          obtain ⟨hrcF, hfreeF⟩ := pikeTake_fill_pool hfill
          have hcount := how.size_le
          rw [hzero] at hcount
          refine ⟨by rw [hrcF, hfreeF]; exact owned_fresh how hzero (by omega),
            ?_⟩
          rw [hrcF]
          simp only [Array.size_push]
          omega

/-- A copy-on-write hands the caller a fresh block and lets go of the shared
one, which someone else still holds — that is why the write had to copy. -/
theorem pikeWrite_owned {st st' : PikeSt} {novec h slot hOut : Nat}
    {value : UInt32} {rest : List Nat} {lim : Limits}
    (hok : pikeWrite st novec h slot value lim = .ok (st', hOut))
    (how : Owned st.rc st.free (h :: rest)) :
    Owned st'.rc st'.free (hOut :: rest) := by
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
        have htake := (pikeTake_owned hTake how).1
        exact owned_release (htake.perm (List.Perm.swap _ _ _))
          (by rw [List.count_cons]; split <;> omega)
  · injection hok with hok
    injection hok with hok hh
    subst hok
    subst hh
    exact how


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
buffers counted at the peak. -/
theorem chargeGrow_capFor {oldcap len esize maxv cap claim : Nat}
    {m m' : Meter} {lim : Limits}
    (hgm : growMin ≤ maxv) (hclaim : growFactor * claim ≤ maxv)
    (hlen : len < claim) (hroom : oldcap ≤ capFor claim)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    cap ≤ capFor claim ∧ oldcap ≤ cap ∧
      m'.cost + 3 * (oldcap * esize) ≤ m.cost + 3 * (cap * esize) ∧
      m'.mem + oldcap * esize = m.mem + cap * esize ∧
      m'.peak ≤ max m.peak (m.mem + cap * esize) := by
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
it stays inside every room, its memory reading is the setup plus what it
reserves, and its peak never passes the setup and twice the reservation.

The cost line is amortized the way section 5's is. Growth is charged once
across the call rather than once per position, and the schedule doubles, so
a stretch that grows an array from `c` entries to `2c` pays `3c` entry
widths and leaves three times the new reservation standing. Carrying the
reservation on both sides of the inequality is what lets the positions
compose without counting a growth twice. -/
structure Charged (re : Re) (setup spent : Nat) (st out : PikeSt) : Prop where
  charge : out.m.cost + 3 * st.reserved ≤ st.m.cost + 3 * out.reserved + spent
  rooms : Rooms re out
  held : out.m.mem = setup + out.reserved
  resident : out.m.peak ≤ max st.m.peak (setup + 2 * pikeScratch re)

/-- Standing still is inside any price, and so is a step that writes a
buffer without growing it — the reading is about capacities and the meter,
and neither moves. -/
theorem Charged.idle {re : Re} {setup : Nat} {st st' : PikeSt}
    (hrooms : Rooms re st') (hres : st'.reserved = st.reserved)
    (hm : st'.m = st.m) (hmem : st.m.mem = setup + st.reserved) :
    Charged re setup 0 st st' :=
  ⟨by rw [hm, hres]; omega, hrooms, by rw [hm, hres]; exact hmem,
    by rw [hm]; exact Nat.le_max_left _ _⟩

/-- Two stretches in a row spend what the two of them spend, and the
reservation in the middle cancels — which is the point of carrying it. -/
theorem Charged.trans {re : Re} {setup a b : Nat} {st mid out : PikeSt}
    (h₁ : Charged re setup a st mid) (h₂ : Charged re setup b mid out) :
    Charged re setup (a + b) st out := by
  obtain ⟨c₁, -, -, p₁⟩ := h₁
  obtain ⟨c₂, r₂, m₂, p₂⟩ := h₂
  exact ⟨by omega, r₂, m₂, by omega⟩

/-- A stretch inside one price is inside any larger one. -/
theorem Charged.mono {re : Re} {setup a b : Nat} {st out : PikeSt}
    (h : Charged re setup a st out) (hle : a ≤ b) : Charged re setup b st out :=
  ⟨by have := h.charge; omega, h.rooms, h.held, h.resident⟩

/-- A charge that moves nothing else: the mark a closure pays for a fresh
pc, the unit a step pays per suspended thread, the visited set cleared. -/
theorem Charged.pay {re : Re} {setup : Nat} {st : PikeSt} (c : Nat)
    (hrooms : Rooms re st) (hmem : st.m.mem = setup + st.reserved) :
    Charged re setup c st
      { st with m := { st.m with cost := st.m.cost + c } } := by
  refine ⟨?_, ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
    hrooms.pool⟩, ?_, ?_⟩
  · show st.m.cost + c + 3 * st.reserved ≤ st.m.cost + 3 * st.reserved + c
    omega
  · show st.m.mem = setup + st.reserved
    exact hmem
  · show st.m.peak ≤ max st.m.peak (setup + 2 * pikeScratch re)
    exact Nat.le_max_left _ _

/-- One growth step read into the run's own reading. Only the array's
capacity moves, so the reservation on both sides of the schedule's
inequalities is the same up to that one term, and the three lines follow
from `chargeGrow_capFor` verbatim. -/
theorem charged_of_grow {re : Re} {setup rest old new esize : Nat}
    {st st' : PikeSt} (hrooms : Rooms re st') (hold : old ≤ new)
    (hres : st.reserved = rest + old * esize)
    (hres' : st'.reserved = rest + new * esize)
    (hmem : st.m.mem = setup + st.reserved)
    (hcost : st'.m.cost + 3 * (old * esize) ≤ st.m.cost + 3 * (new * esize))
    (hmem' : st'.m.mem + old * esize = st.m.mem + new * esize)
    (hpeak : st'.m.peak ≤ max st.m.peak (st.m.mem + new * esize)) :
    Charged re setup 0 st st' := by
  have hle := hrooms.scratch_le
  have hstep : old * esize ≤ new * esize := Nat.mul_le_mul_right esize hold
  exact ⟨by omega, hrooms, by omega, by omega⟩

/-! ### What each helper's growth costs -/

theorem pikeDefer_charged {re : Re} {st st' : PikeSt} {pc h setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem = setup + st.reserved)
    (hsize : st.stk.size < re.code.size * 2)
    (hok : pikeDefer st pc h lim = .ok st') : Charged re setup 0 st st' := by
  unfold pikeDefer at hok
  split at hok
  · simp at hok
  · rename_i mm cap hg
    injection hok with hok
    subst hok
    obtain ⟨-, ⟨hgm, hcl⟩, -, -⟩ := pikeSchedule hwf
    obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
      chargeGrow_capFor hgm hcl hsize hrooms.stk hg
    exact charged_of_grow (esize := thSize)
      (rest := (st.clistCap + st.nlistCap) * thSize +
        (st.rcCap + st.freeCap + st.poolCap) * regSize)
      ⟨hrooms.clist, hrooms.nlist, hcap, hrooms.rc, hrooms.free, hrooms.pool⟩
      hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
      (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost hmem'
      hpeak

theorem pikePark_charged {re : Re} {st st' : PikeSt} {intoNext : Bool}
    {pc h setup : Nat} {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem = setup + st.reserved)
    (hsize : (if intoNext then st.nlist else st.clist).size < re.code.size)
    (hok : pikePark st intoNext pc h lim = .ok st') :
    Charged re setup 0 st st' := by
  obtain ⟨⟨hgm, hcl⟩, -, -, -⟩ := pikeSchedule hwf
  unfold pikePark at hok
  split at hok
  · rename_i hin
    rw [if_pos hin] at hsize
    split at hok
    · simp at hok
    · rename_i mm cap hg
      injection hok with hok
      subst hok
      obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
        chargeGrow_capFor hgm hcl hsize hrooms.nlist hg
      exact charged_of_grow (esize := thSize)
        (rest := (st.clistCap + st.stkCap) * thSize +
          (st.rcCap + st.freeCap + st.poolCap) * regSize)
        ⟨hrooms.clist, hcap, hrooms.stk, hrooms.rc, hrooms.free, hrooms.pool⟩
        hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
        (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
        hmem' hpeak
  · rename_i hin
    rw [if_neg hin] at hsize
    split at hok
    · simp at hok
    · rename_i mm cap hg
      injection hok with hok
      subst hok
      obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
        chargeGrow_capFor hgm hcl hsize hrooms.clist hg
      exact charged_of_grow (esize := thSize)
        (rest := (st.nlistCap + st.stkCap) * thSize +
          (st.rcCap + st.freeCap + st.poolCap) * regSize)
        ⟨hcap, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free, hrooms.pool⟩
        hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
        (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
        hmem' hpeak

theorem pikeDrop_charged {re : Re} {st st' : PikeSt} {h setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem = setup + st.reserved)
    (hsize : st.rc[h]! ≤ 1 → st.free.size < re.code.size * 4 + 2)
    (hok : pikeDrop st h lim = .ok st') : Charged re setup 0 st st' := by
  obtain ⟨-, -, ⟨hgm, hcl⟩, -⟩ := pikeSchedule hwf
  unfold pikeDrop at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    subst hok
    exact Charged.idle hrooms rfl rfl hmem
  · split at hok
    · split at hok
      · simp at hok
      · rename_i mm cap hg
        rename_i hzero _
        injection hok with hok
        subst hok
        obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
          chargeGrow_capFor hgm hcl (hsize (by simp only [beq_iff_eq] at hzero; omega))
            hrooms.free hg
        exact charged_of_grow (esize := regSize)
          (rest := (st.clistCap + st.nlistCap + st.stkCap) * thSize +
            (st.rcCap + st.poolCap) * regSize)
          ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hcap,
            hrooms.pool⟩
          hold (by simp only [PikeSt.reserved, thSize, regSize]; omega)
          (by simp only [PikeSt.reserved, thSize, regSize]; omega) hmem hcost
          hmem' hpeak
    · injection hok with hok
      subst hok
      exact Charged.idle ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc,
        hrooms.free, hrooms.pool⟩ rfl rfl hmem

/-- The block fill of `pike_take`: one pool push per slot, each inside the
pool's own entry bound because the block it is filling is one the pool has
room for. -/
theorem pikeTake_fill_charged {re : Re} {setup : Nat} {lim : Limits}
    (hwf : ReWf re) : ∀ (k : Nat) {st st' : PikeSt}, Rooms re st →
      st.m.mem = setup + st.reserved →
      st.pool.size + k ≤ (re.code.size * 4 + 2) * re.novec →
      pikeTake.fill lim k st = .ok st' → Charged re setup 0 st st' := by
  obtain ⟨-, -, -, ⟨hgm, hcl⟩⟩ := pikeSchedule hwf
  intro k
  induction k with
  | zero =>
      intro st st' hrooms hmem _ hok
      rw [pikeTake.fill] at hok
      injection hok with hok
      subst hok
      exact Charged.idle hrooms rfl rfl hmem
  | succ n ih =>
      intro st st' hrooms hmem hpool hok
      rw [pikeTake.fill] at hok
      split at hok
      · simp at hok
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
        exact (hstep.trans (ih hstep.rooms hstep.held (by simp; omega) hok)).mono
          (by omega)

theorem pikeTake_charged {re : Re} {st st' : PikeSt} {novec hOut setup : Nat}
    {lim : Limits} (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem = setup + st.reserved)
    (hrc : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2)
    (hpool : st.free.size = 0 →
      st.pool.size + novec ≤ (re.code.size * 4 + 2) * re.novec)
    (hok : pikeTake st novec lim = .ok (st', hOut)) :
    Charged re setup 0 st st' := by
  obtain ⟨-, -, ⟨hgm, hcl⟩, -⟩ := pikeSchedule hwf
  unfold pikeTake at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    injection hok with hok _
    subst hok
    exact Charged.idle ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc,
      hrooms.free, hrooms.pool⟩ rfl rfl hmem
  · rename_i hempty
    have hzero : st.free.size = 0 := by
      rcases Nat.eq_zero_or_pos st.free.size with hz | hp
      · exact hz
      · exact absurd (by simpa using hp) hempty
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
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
        split at hok
        · simp at hok
        · rename_i stF hfill
          injection hok with hok
          injection hok with hok _
          subst hok
          exact (hstep.trans (pikeTake_fill_charged hwf novec hstep.rooms
            hstep.held (by simpa using hpool hzero) hfill)).mono (by omega)

/-- The copy-on-write of `pike_write`: one block copied out at a cost unit
per byte, and the fresh block it copies into. -/
theorem pikeWrite_charged {re : Re} {st st' : PikeSt}
    {novec h slot hOut setup : Nat} {value : UInt32} {lim : Limits}
    (hwf : ReWf re) (hrooms : Rooms re st)
    (hmem : st.m.mem = setup + st.reserved)
    (hrc : st.free.size = 0 → st.rc.size < re.code.size * 4 + 2)
    (hpool : st.free.size = 0 →
      st.pool.size + novec ≤ (re.code.size * 4 + 2) * re.novec)
    (hok : pikeWrite st novec h slot value lim = .ok (st', hOut)) :
    Charged re setup (novec * regSize) st st' := by
  unfold pikeWrite at hok
  simp only [] at hok
  split at hok
  · split at hok
    · simp at hok
    · rename_i hcopy
      split at hok
      · simp at hok
      · rename_i hTake
        injection hok with hok
        injection hok with hok _
        subst hok
        have hpaid := Charged.pay (re := re) (setup := setup)
          (novec * regSize) hrooms hmem
        have htake := pikeTake_charged hwf hpaid.rooms hpaid.held hrc hpool hTake
        refine Charged.mono ((hpaid.trans htake).trans
          (Charged.idle ?_ rfl rfl htake.held)) (by omega)
        exact ⟨htake.rooms.clist, htake.rooms.nlist, htake.rooms.stk,
          htake.rooms.rc, htake.rooms.free, htake.rooms.pool⟩
  · injection hok with hok
    injection hok with hok _
    subst hok
    refine Charged.mono (Charged.idle ?_ rfl rfl hmem) (by omega)
    exact ⟨hrooms.clist, hrooms.nlist, hrooms.stk, hrooms.rc, hrooms.free,
      hrooms.pool⟩

end Pcrevera.Ref
