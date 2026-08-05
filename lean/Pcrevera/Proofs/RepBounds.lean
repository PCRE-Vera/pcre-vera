import Pcrevera.Proofs.BtBounds

/-!
# The pricing of a counted repetition (BOUNDS.md section 4.4)

Sections 4.1 to 4.3 are priced by `flowCost`, a walk over the code that
charges each opcode once and follows every edge forward. A counted repetition
breaks that in one place: its tail jumps back to its own head, so what is
still to come from a point inside it depends on the counter and not on the
program point alone.

What makes the walk forward again is that a repetition's *price* is a closed
form even though its control flow is a loop. `repLeft ways each base k` is
that form — `k` rounds of the recurrence and then the base — and reading it at
the number of passes the head still has left turns the head into a leaf of the
walk rather than a way back into the body. Every remaining edge goes forward,
so `re.code.size` is enough fuel here exactly as it is for `flowCost`, and the
development below is `costAt`'s with the counters carried along.

The pass count is the only place the subject enters. Bounded, it is the
counter value the head leaves at. Unbounded, the head never leaves by its
counter and the empty-match rule stops it instead, so what is left is the
unmet part of the minimum plus one pass per byte still ahead. One more than
that number, at the counter a `RepZero` leaves behind, is at most the
checker's `repPasses` — equal to it at the start of a subject and smaller
further in — and covering `repPasses` is what the checker's flow does. That
is not a coincidence; it is where the two halves of section 4.4 meet.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## How many passes the head still has -/

/-- The counter values a repetition's head still has to read from here.

Bounded, the head's own test stops the count and nothing else is needed.
Unbounded, `rep.hi` is the sentinel the counter never reaches, and what ends
the loop is an iteration that consumed nothing — so every pass past the
minimum eats a byte, and the bytes still ahead bound what is left. -/
def repK (rep : RepInfo) (n c pos : Nat) : Nat :=
  if rep.hi = none32 then (rep.lo - c) + (n + 1 - pos) else repCeil rep - c

/-- Consuming a byte spends a pass, or leaves the count where it was. -/
theorem repK_mono_pos {rep : RepInfo} {n c pos pos' : Nat} (h : pos ≤ pos') :
    repK rep n c pos' ≤ repK rep n c pos := by
  unfold repK
  split <;> omega

/-- And so does counting one. -/
theorem repK_mono_count {rep : RepInfo} {n c pos : Nat} :
    repK rep n (c + 1) pos ≤ repK rep n c pos := by
  unfold repK
  split <;> omega

/-- At the counter a `RepZero` leaves behind the passes are the checker's own
`repPasses`, one short — the one the head spends finding the count spent. -/
theorem repK_zero_le {rep : RepInfo} (n pos : Nat) :
    repK rep n 0 pos + 1 ≤ repPasses rep n := by
  unfold repK repPasses repCeil
  by_cases hb : rep.hi = none32
  · rw [if_pos hb, if_pos hb]
    omega
  · rw [if_neg hb, if_neg hb]
    split <;> omega

/-- Unbounded, the loop is never over at the head while the cursor is inside
the subject: there is the pass that reads the count, and the bytes ahead to
spend. -/
theorem repK_pos_unbounded {rep : RepInfo} {n c pos : Nat}
    (hu : rep.hi = none32) (hpos : pos ≤ n) : 1 ≤ repK rep n c pos := by
  unfold repK
  rw [if_pos hu]
  omega

/-- Bounded, it is over exactly at the count the head leaves at. -/
theorem repK_bounded {rep : RepInfo} {n c pos : Nat} (hb : rep.hi ≠ none32) :
    repK rep n c pos = repCeil rep - c := by
  unfold repK
  rw [if_neg hb]

/-! ## The walk -/

/-- The head of a repetition, priced: one round of the recurrence per counter
value still to read, and the base is the pass that reads the spent count and
leaves. `x` is what the pricing is where control leaves the region, and it is
charged `1 + ways` times per pass — once at the head and once per way the body
found to finish. -/
def repHeadPrice (unitHead ways charge x k : Nat) : Nat :=
  repLeft ways (charge + (1 + ways) * x) (unitHead + x) k

/-- The register file a `RepNext` leaves behind. -/
def repBump (re : Re) (i : Inst) (regs : Array UInt32) : Array UInt32 :=
  regs.set! (repSlot re i) (regs[repSlot re i]! + 1)

/-- The counter a repetition opcode reads. -/
def repCount (re : Re) (i : Inst) (regs : Array UInt32) : Nat :=
  (regs[repSlot re i]!).toNat

/-- Where a tail is priced from: one position ahead when the iteration that
just ended consumed nothing and the minimum is met, because then the loop is
over and the head is not reached again; at the cursor otherwise.

This is the one place the empty-match rule enters the pricing, and it has to,
or the round the head just paid for would buy nothing. The function is
non-decreasing in the cursor, which is what keeps the whole pricing
non-increasing in it. -/
def repAhead (re : Re) (i : Inst) (regs : Array UInt32) (pos : Nat) : Nat :=
  if (re.reps[i.arg]!).hi = none32 ∧
      (re.reps[i.arg]!).lo ≤ repCount re i (repBump re i regs) ∧
      regs[repSlot re i + 1]! = pos.toUInt32 then pos + 1 else pos

/-- Where the cursor has come further, so has the position a tail is priced
from. This is what keeps the whole pricing non-increasing in the cursor. -/
theorem repAhead_mono {re : Re} {i : Inst} {regs regs' : Array UInt32}
    {pos pos' : Nat} (hle : pos ≤ pos')
    (hbump : repCount re i (repBump re i regs) =
      repCount re i (repBump re i regs'))
    (hentry : regs[repSlot re i + 1]! = pos.toUInt32 →
      regs'[repSlot re i + 1]! = pos'.toUInt32) :
    repAhead re i regs pos ≤ repAhead re i regs' pos' := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · unfold repAhead
    split
    · rename_i hc
      rw [if_pos ⟨hc.1, hbump ▸ hc.2.1, hentry hc.2.2⟩]
      omega
    · split <;> omega
  · unfold repAhead
    split <;> split <;> omega

/-- Control at this point only ever moves forward, with the two repetition
opcodes that name a target read through the repetition record rather than off
the instruction. The tail's jump back to the head is not here, because the
walk does not follow it: the head is priced by its closed form. -/
def RepFwd (re : Re) (pc : Nat) : Prop :=
  ((re.code[pc]!).op = .split → pc < (re.code[pc]!).arg ∧ pc < (re.code[pc]!).alt) ∧
    ((re.code[pc]!).op = .jump → pc < (re.code[pc]!).arg) ∧
    (((re.code[pc]!).op = .repLoop ∨ (re.code[pc]!).op = .repNext) →
      pc < (re.reps[(re.code[pc]!).arg]!).after)

/-- What the rest of an attempt may still cost from a program point, read off
the code with the counters in hand.

`ways` and `charge` are the two numbers section 4.4 reads off a repetition's
body, indexed by the repetition rather than by the region: its ambiguity, and
what one pass through the head charges besides the crossings of the region's
end. They come from the checker's own walk over the body, and the pricing
takes them as given the way the fork account takes a pricing as given.

`fuel` is the ground still to cover, and `code.size` is always enough of it,
because every edge the walk follows goes forward. -/
def repCostAt (re : Re) (unit : Inst → Nat) (n : Nat) (ways charge : Nat → Nat) :
    Nat → Nat → Array UInt32 → Nat → Nat
  | 0, _, _, _ => 0
  | fuel + 1, pc, regs, pos =>
      if pc ≥ re.code.size then 0
      else
        match (re.code[pc]!).op with
        | .accept => unit (re.code[pc]!)
        | .split =>
            unit (re.code[pc]!) +
              repCostAt re unit n ways charge fuel (re.code[pc]!).arg regs pos +
              repCostAt re unit n ways charge fuel (re.code[pc]!).alt regs pos
        | .jump =>
            unit (re.code[pc]!) +
              repCostAt re unit n ways charge fuel (re.code[pc]!).arg regs pos
        | .repZero =>
            unit (re.code[pc]!) +
              repCostAt re unit n ways charge fuel (pc + 1)
                (regs.set! (repSlot re (re.code[pc]!)) 0) pos
        | .repEnter =>
            unit (re.code[pc]!) +
              repCostAt re unit n ways charge fuel (pc + 1)
                (regs.set! (repSlot re (re.code[pc]!) + 1) pos.toUInt32) pos
        | .repLoop =>
            repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
              (charge (re.code[pc]!).arg)
              (repCostAt re unit n ways charge fuel
                (re.reps[(re.code[pc]!).arg]!).after regs pos)
              (repK (re.reps[(re.code[pc]!).arg]!) n
                (repCount re (re.code[pc]!) regs) pos)
        | .repNext =>
            unit (re.code[pc]!) +
              repHeadPrice
                (unit (re.code[(re.reps[(re.code[pc]!).arg]!).head]!))
                (ways (re.code[pc]!).arg) (charge (re.code[pc]!).arg)
                (repCostAt re unit n ways charge fuel
                  (re.reps[(re.code[pc]!).arg]!).after
                  (repBump re (re.code[pc]!) regs) pos)
                (repK (re.reps[(re.code[pc]!).arg]!) n
                  (repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs))
                  (repAhead re (re.code[pc]!) regs pos)) +
              repCostAt re unit n ways charge fuel
                (re.reps[(re.code[pc]!).arg]!).after
                (repBump re (re.code[pc]!) regs) pos
        | _ =>
            unit (re.code[pc]!) +
              repCostAt re unit n ways charge fuel (pc + 1) regs pos

/-- More fuel than the ground left changes nothing. -/
theorem repCostAt_stable {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} (hfwd : ∀ pc, pc < re.code.size → RepFwd re pc) :
    ∀ (f pc : Nat) (regs : Array UInt32) (pos : Nat), re.code.size - pc ≤ f →
      repCostAt re unit n ways charge f pc regs pos =
        repCostAt re unit n ways charge (f + 1) pc regs pos := by
  intro f
  induction f with
  | zero =>
      intro pc regs pos hk
      rw [repCostAt, repCostAt, if_pos (by omega)]
  | succ f ih =>
      intro pc regs pos hk
      by_cases hpc : pc ≥ re.code.size
      · rw [repCostAt, repCostAt, if_pos hpc, if_pos hpc]
      · rw [repCostAt, repCostAt, if_neg hpc, if_neg hpc]
        obtain ⟨hsp, hjp, hrp⟩ := hfwd pc (by omega)
        split
        · rfl
        · rename_i hop
          rw [← ih _ _ _ (by have := (hsp hop).1; omega),
            ← ih _ _ _ (by have := (hsp hop).2; omega)]
        · rename_i hop
          rw [← ih _ _ _ (by have := hjp hop; omega)]
        · rw [← ih (pc + 1) _ _ (by omega)]
        · rw [← ih (pc + 1) _ _ (by omega)]
        · rename_i hop
          rw [← ih _ _ _ (by have := hrp (Or.inl hop); omega)]
        · rename_i hop
          rw [← ih _ _ _ (by have := hrp (Or.inr hop); omega)]
        · rw [← ih (pc + 1) _ _ (by omega)]

/-- So any two sufficient fuels agree. -/
theorem repCostAt_const {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} (hfwd : ∀ pc, pc < re.code.size → RepFwd re pc) :
    ∀ (f g pc : Nat) (regs : Array UInt32) (pos : Nat), re.code.size - pc ≤ f →
      f ≤ g → repCostAt re unit n ways charge f pc regs pos =
        repCostAt re unit n ways charge g pc regs pos := by
  intro f g pc regs pos hf hfg
  induction g with
  | zero => have : f = 0 := by omega
            rw [this]
  | succ g ih =>
      rcases Nat.eq_or_lt_of_le hfg with rfl | hlt
      · rfl
      · rw [ih (by omega), repCostAt_stable hfwd g pc regs pos (by omega)]

/-- The pricing itself, run on the whole program's worth of fuel. -/
def repCost (re : Re) (unit : Inst → Nat) (n : Nat) (ways charge : Nat → Nat)
    (pc : Nat) (regs : Array UInt32) (pos : Nat) : Nat :=
  repCostAt re unit n ways charge re.code.size pc regs pos

/-- Past the end of the program there is nothing left to charge. -/
theorem repCost_out {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (h : re.code.size ≤ pc) : repCost re unit n ways charge pc regs pos = 0 := by
  unfold repCost
  cases hsz : re.code.size with
  | zero => rw [repCostAt]
  | succ f => rw [repCostAt, if_pos (by omega)]

/-! ## What the walk reads of the register file

Two facts, and they are the two rules BOUNDS.md leaves to the compiler. The
walk reads a register only through a repetition's counter or its entry
position, both of which sit at or above `novec`, so a `Save` — which names a
capture slot, below `novec` — is invisible to it. And where two runs differ
only in how far the cursor has come, the walk at the later cursor is the
cheaper one.
-/

/-- Reading a `set!` back at the index it wrote. -/
theorem uset!_self (a : Array UInt32) (i : Nat) (v : UInt32) (h : i < a.size) :
    (a.set! i v)[i]! = v := by simp [h]

/-- And a write the array had no room for is no write at all. -/
theorem uset!_out (a : Array UInt32) (i : Nat) (v : UInt32) (h : a.size ≤ i) :
    a.set! i v = a := by
  rw [Array.set!, Array.setIfInBounds_eq_of_size_le h]

/-- The same write on two files of the same size leaves them agreeing wherever
they agreed. -/
theorem uset!_agree {a b : Array UInt32} {k q : Nat} {v : UInt32}
    (hsize : a.size = b.size) (h : a[q]! = b[q]!) :
    (a.set! k v)[q]! = (b.set! k v)[q]! := by
  by_cases hq : q = k
  · subst hq
    by_cases hlt : q < a.size
    · rw [uset!_self _ _ _ hlt, uset!_self _ _ _ (by omega)]
    · rw [uset!_out _ _ _ (by omega), uset!_out _ _ _ (by omega)]
      exact h
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq),
      Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq)]
    exact h

theorem uset!_size (a : Array UInt32) (i : Nat) (v : UInt32) :
    (a.set! i v).size = a.size := by
  simp only [Array.set!, Array.size_setIfInBounds]

/-- Register files the walk cannot tell apart: they agree everywhere a
repetition keeps anything. -/
structure RegsSame (re : Re) (regs regs' : Array UInt32) : Prop where
  size : regs.size = regs'.size
  slots : ∀ k, re.novec ≤ k → regs[k]! = regs'[k]!

theorem RegsSame.set {re : Re} {regs regs' : Array UInt32} {k : Nat}
    {v : UInt32} (h : RegsSame re regs regs') :
    RegsSame re (regs.set! k v) (regs'.set! k v) :=
  ⟨by rw [uset!_size, uset!_size]; exact h.size,
    fun q hq => uset!_agree h.size (h.slots q hq)⟩

/-- A write below `novec` is one the walk never reads. -/
theorem RegsSame.below {re : Re} {regs : Array UInt32} {k : Nat} {v : UInt32}
    (h : k < re.novec) : RegsSame re (regs.set! k v) regs :=
  ⟨uset!_size _ _ _, fun q hq => Array.getElem!_set!_ne _ _ _ _ (by omega)⟩

/-- So the walk is the same on both. -/
theorem repCostAt_congr {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} :
    ∀ (f pc : Nat) (regs regs' : Array UInt32) (pos : Nat),
      RegsSame re regs regs' →
      repCostAt re unit n ways charge f pc regs pos =
        repCostAt re unit n ways charge f pc regs' pos := by
  intro f
  induction f with
  | zero => intro pc regs regs' pos _; rw [repCostAt, repCostAt]
  | succ f ih =>
      intro pc regs regs' pos hs
      rw [repCostAt, repCostAt]
      by_cases hpc : pc ≥ re.code.size
      · rw [if_pos hpc, if_pos hpc]
      rw [if_neg hpc, if_neg hpc]
      have hslot : re.novec ≤ repSlot re (re.code[pc]!) := by
        simp only [repSlot]; omega
      split
      · rfl
      · rw [ih _ _ _ _ hs, ih _ _ _ _ hs]
      · rw [ih _ _ _ _ hs]
      · rw [ih _ _ _ _ hs.set]
      · rw [ih _ _ _ _ hs.set]
      · rw [ih _ _ _ _ hs, repCount, repCount, hs.slots _ hslot]
      · have hb : RegsSame re (repBump re (re.code[pc]!) regs)
            (repBump re (re.code[pc]!) regs') := by
          simp only [repBump, hs.slots _ hslot]
          exact hs.set
        rw [ih _ _ _ _ hb, repCount, repCount, hb.slots _ hslot, repAhead,
          repAhead, repCount, repCount, hb.slots _ hslot,
          hs.slots _ (by omega)]
      · rw [ih _ _ _ _ hs]

/-- What a walk reads of the register file, restricted to the code it can
still reach: two files that agree on every counter and entry position named
at or after the cursor.

This is the reading `RegsSame` is the whole-program case of, and it is the one
section 4.4 needs. Past a repetition's exit no opcode names it any more, so
the price where control leaves a region does not depend on the counter that
region was driving — which is what lets a region's claim be stated against the
register file its parent hands in. -/
def RegsHere (re : Re) (regs regs' : Array UInt32) (pc : Nat) : Prop :=
  regs.size = regs'.size ∧
    ∀ q, pc ≤ q → q < re.code.size →
      ((re.code[q]!).op = .repZero ∨ (re.code[q]!).op = .repLoop ∨
        (re.code[q]!).op = .repEnter ∨ (re.code[q]!).op = .repNext) →
      regs[repSlot re (re.code[q]!)]! = regs'[repSlot re (re.code[q]!)]! ∧
        regs[repSlot re (re.code[q]!) + 1]! =
          regs'[repSlot re (re.code[q]!) + 1]!

/-- Ground already covered is ground the walk will not read again. -/
theorem RegsHere.mono {re : Re} {regs regs' : Array UInt32} {pc pc' : Nat}
    (h : RegsHere re regs regs' pc) (hle : pc ≤ pc') :
    RegsHere re regs regs' pc' :=
  ⟨h.1, fun q hq => h.2 q (by omega)⟩

/-- The same write on both sides leaves them agreeing. -/
theorem RegsHere.write {re : Re} {regs regs' : Array UInt32} {pc pc' k : Nat}
    {v : UInt32} (h : RegsHere re regs regs' pc) (hle : pc ≤ pc') :
    RegsHere re (regs.set! k v) (regs'.set! k v) pc' :=
  ⟨by rw [uset!_size, uset!_size]; exact h.1,
    fun q hq hq2 hop =>
      ⟨uset!_agree h.1 (h.2 q (by omega) hq2 hop).1,
        uset!_agree h.1 (h.2 q (by omega) hq2 hop).2⟩⟩

/-- Whole-program agreement is agreement everywhere the walk can reach. -/
theorem RegsSame.here {re : Re} {regs regs' : Array UInt32} {pc : Nat}
    (h : RegsSame re regs regs') : RegsHere re regs regs' pc :=
  ⟨h.size, fun q _ _ _ =>
    ⟨h.slots _ (by simp only [repSlot]; omega),
      h.slots _ (by simp only [repSlot]; omega)⟩⟩

/-- So a walk is a function of what its own reach holds. -/
theorem repCostAt_local {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} (hfwd : ∀ q, q < re.code.size → RepFwd re q) :
    ∀ (f pc : Nat) (regs regs' : Array UInt32) (pos : Nat),
      RegsHere re regs regs' pc →
      repCostAt re unit n ways charge f pc regs pos =
        repCostAt re unit n ways charge f pc regs' pos := by
  intro f
  induction f with
  | zero => intro pc regs regs' pos _; rw [repCostAt, repCostAt]
  | succ f ih =>
      intro pc regs regs' pos hs
      rw [repCostAt, repCostAt]
      by_cases hpc : pc ≥ re.code.size
      · rw [if_pos hpc, if_pos hpc]
      rw [if_neg hpc, if_neg hpc]
      obtain ⟨hsp, hjp, hrp⟩ := hfwd pc (by omega)
      split
      · rfl
      · rename_i hop
        rw [ih _ _ _ _ (hs.mono (by have := (hsp hop).1; omega)),
          ih _ _ _ _ (hs.mono (by have := (hsp hop).2; omega))]
      · rename_i hop
        rw [ih _ _ _ _ (hs.mono (by have := hjp hop; omega))]
      · rw [ih _ _ _ _ (hs.write (Nat.le_succ pc))]
      · rw [ih _ _ _ _ (hs.write (Nat.le_succ pc))]
      · rename_i hop
        have hq := (hs.2 pc (Nat.le_refl _) (by omega) (Or.inr (Or.inl hop))).1
        rw [ih _ _ _ _ (hs.mono (by have := hrp (Or.inl hop); omega)),
          repCount, repCount, hq]
      · rename_i hop
        have hq := hs.2 pc (Nat.le_refl _) (by omega) (Or.inr (Or.inr (Or.inr hop)))
        have hb : RegsHere re (repBump re (re.code[pc]!) regs)
            (repBump re (re.code[pc]!) regs')
            (re.reps[(re.code[pc]!).arg]!).after := by
          simp only [repBump, hq.1]
          exact hs.write (by have := hrp (Or.inr hop); omega)
        have hbc : repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs) =
            repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs') := by
          simp only [repCount, repBump, hq.1]
          exact congrArg UInt32.toNat (uset!_agree hs.1 hq.1)
        rw [ih _ _ _ _ hb, hbc, repAhead, repAhead, hbc, hq.2]
      · rw [ih _ _ _ _ (hs.mono (Nat.le_succ pc))]

/-! ## The pricing never rises as the subject is consumed -/

/-- `repLeft` read as a bound rather than as a value: it is monotone in every
argument that can only grow. -/
theorem repLeft_le {w e e' b b' j k : Nat} (hb : b ≤ e) (he : e' ≤ e)
    (hbb : b' ≤ b) (hk : j ≤ k) : repLeft w e' b' j ≤ repLeft w e b k := by
  have hstep : ∀ q, repLeft w e' b' q ≤ repLeft w e b q := by
    intro q
    induction q with
    | zero => exact Nat.le_trans hbb (Nat.le_refl b)
    | succ q ih =>
        have h : repLeft w e' b' (q + 1) = e' + w * repLeft w e' b' q := rfl
        have h2 : repLeft w e b (q + 1) = e + w * repLeft w e b q := rfl
        have hm : w * repLeft w e' b' q ≤ w * repLeft w e b q :=
          Nat.mul_le_mul_left _ ih
        omega
  exact Nat.le_trans (hstep j) (repLeft_mono hb hk)

/-- And so is the head's closed form, in what it costs to leave the region and
in the passes still to come. -/
theorem repHeadPrice_le {u w c x x' k k' : Nat} (hu : u ≤ c) (hx : x' ≤ x)
    (hk : k' ≤ k) : repHeadPrice u w c x' k' ≤ repHeadPrice u w c x k := by
  refine repLeft_le ?_ ?_ ?_ hk
  · have : 1 * x ≤ (1 + w) * x := Nat.mul_le_mul_right _ (by omega)
    omega
  · have : (1 + w) * x' ≤ (1 + w) * x := Nat.mul_le_mul_left _ hx
    omega
  · omega

/-- Register files a walk at a later cursor can be compared against: the
counters agree, and where the earlier one says a repetition began at its own
cursor, the later one says the same of its. -/
structure RegsAhead (re : Re) (regs regs' : Array UInt32) (pos pos' : Nat) :
    Prop where
  size : regs.size = regs'.size
  count : ∀ j, regs[re.novec + j * 2]! = regs'[re.novec + j * 2]!
  entry : ∀ j, regs[re.novec + j * 2 + 1]! = pos.toUInt32 →
    regs'[re.novec + j * 2 + 1]! = pos'.toUInt32

/-- Zeroing a counter, on both sides at once. -/
theorem RegsAhead.zero {re : Re} {regs regs' : Array UInt32} {pos pos' a : Nat}
    (h : RegsAhead re regs regs' pos pos') :
    RegsAhead re (regs.set! (re.novec + a * 2) 0)
      (regs'.set! (re.novec + a * 2) 0) pos pos' :=
  ⟨by rw [uset!_size, uset!_size]; exact h.size,
    fun j => uset!_agree h.size (h.count j),
    fun j hj => by
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hj ⊢
      exact h.entry j hj⟩

/-- Counting one, on both sides at once. -/
theorem RegsAhead.bump {re : Re} {regs regs' : Array UInt32} {pos pos' a : Nat}
    (h : RegsAhead re regs regs' pos pos') :
    RegsAhead re (regs.set! (re.novec + a * 2) (regs[re.novec + a * 2]! + 1))
      (regs'.set! (re.novec + a * 2) (regs'[re.novec + a * 2]! + 1)) pos pos' := by
  rw [← h.count a]
  exact ⟨by rw [uset!_size, uset!_size]; exact h.size,
    fun j => uset!_agree h.size (h.count j),
    fun j hj => by
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hj ⊢
      exact h.entry j hj⟩

/-- And remembering where an iteration began, each at its own cursor. -/
theorem RegsAhead.enter {re : Re} {regs regs' : Array UInt32} {pos pos' a : Nat}
    (h : RegsAhead re regs regs' pos pos') :
    RegsAhead re (regs.set! (re.novec + a * 2 + 1) pos.toUInt32)
      (regs'.set! (re.novec + a * 2 + 1) pos'.toUInt32) pos pos' := by
  refine ⟨by rw [uset!_size, uset!_size]; exact h.size, ?_, ?_⟩
  · intro j
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
      Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.count j
  · intro j hj
    have hs := h.size
    by_cases hj2 : j = a
    · subst hj2
      by_cases hlt : re.novec + j * 2 + 1 < regs.size
      · exact uset!_self _ _ _ (by omega)
      · rw [uset!_out _ _ _ (by omega)]
        rw [uset!_out _ _ _ (by omega)] at hj
        exact h.entry j hj
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at hj ⊢
      exact h.entry j hj

/-- The pricing never rises as the cursor moves forward.

Every clause is monotone in the cursor, and the two the counters touch are
monotone for the two reasons section 4.4 turns on: `repK` falls as the bytes
ahead run out, and `repAhead` rises with the cursor, so a tail priced at a
later position is priced for fewer rounds. The two side conditions say that a
repetition's per-pass charge covers the head's own visit, which is what makes
the closed form monotone in the passes still to come. -/
theorem repCostAt_mono_pos {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat}
    (hhead : ∀ q : Nat, (re.code[q]!).op = .repLoop →
      unit (re.code[q]!) ≤ charge (re.code[q]!).arg)
    (htail : ∀ q : Nat, (re.code[q]!).op = .repNext →
      unit (re.code[(re.reps[(re.code[q]!).arg]!).head]!) ≤
        charge (re.code[q]!).arg) :
    ∀ (f pc : Nat) (regs regs' : Array UInt32) (pos pos' : Nat),
      pos ≤ pos' → RegsAhead re regs regs' pos pos' →
      repCostAt re unit n ways charge f pc regs' pos' ≤
        repCostAt re unit n ways charge f pc regs pos := by
  intro f
  induction f with
  | zero =>
      intro pc regs regs' pos pos' _ _
      rw [repCostAt, repCostAt]
      exact Nat.le_refl _
  | succ f ih =>
      intro pc regs regs' pos pos' hle ha
      rw [repCostAt, repCostAt]
      by_cases hpc : pc ≥ re.code.size
      · rw [if_pos hpc, if_pos hpc]
        exact Nat.le_refl _
      rw [if_neg hpc, if_neg hpc]
      have hc : repCount re (re.code[pc]!) regs = repCount re (re.code[pc]!) regs' := by
        simp only [repCount, repSlot, ha.count (re.code[pc]!).arg]
      split
      · exact Nat.le_refl _
      · exact Nat.add_le_add (Nat.add_le_add_left (ih _ _ _ _ _ hle ha) _)
          (ih _ _ _ _ _ hle ha)
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hle ha) _
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hle ha.zero) _
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hle ha.enter) _
      · rename_i hop
        exact repHeadPrice_le (hhead pc hop) (ih _ _ _ _ _ hle ha)
          (hc ▸ repK_mono_pos hle)
      · rename_i hop
        have hb : RegsAhead re (repBump re (re.code[pc]!) regs)
            (repBump re (re.code[pc]!) regs') pos pos' := by
          simp only [repBump, repSlot]
          exact ha.bump
        have hcb : repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs) =
            repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs') := by
          simp only [repCount, repSlot, hb.count (re.code[pc]!).arg]
        refine Nat.add_le_add (Nat.add_le_add_left ?_ _) (ih _ _ _ _ _ hle hb)
        refine repHeadPrice_le (htail pc hop) (ih _ _ _ _ _ hle hb) ?_
        rw [← hcb]
        exact repK_mono_pos (repAhead_mono hle hcb
          (fun hx => by
            have := ha.entry (re.code[pc]!).arg
            simp only [repSlot] at hx ⊢
            exact this hx))
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hle ha) _

/-- One step of the pricing, with the fuel taken out. -/
theorem repCost_unfold {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size) :
    repCost re unit n ways charge pc regs pos =
      match (re.code[pc]!).op with
      | .accept => unit (re.code[pc]!)
      | .split =>
          unit (re.code[pc]!) +
            repCost re unit n ways charge (re.code[pc]!).arg regs pos +
            repCost re unit n ways charge (re.code[pc]!).alt regs pos
      | .jump =>
          unit (re.code[pc]!) +
            repCost re unit n ways charge (re.code[pc]!).arg regs pos
      | .repZero =>
          unit (re.code[pc]!) +
            repCost re unit n ways charge (pc + 1)
              (regs.set! (repSlot re (re.code[pc]!)) 0) pos
      | .repEnter =>
          unit (re.code[pc]!) +
            repCost re unit n ways charge (pc + 1)
              (regs.set! (repSlot re (re.code[pc]!) + 1) pos.toUInt32) pos
      | .repLoop =>
          repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
            (charge (re.code[pc]!).arg)
            (repCost re unit n ways charge
              (re.reps[(re.code[pc]!).arg]!).after regs pos)
            (repK (re.reps[(re.code[pc]!).arg]!) n
              (repCount re (re.code[pc]!) regs) pos)
      | .repNext =>
          unit (re.code[pc]!) +
            repHeadPrice (unit (re.code[(re.reps[(re.code[pc]!).arg]!).head]!))
              (ways (re.code[pc]!).arg) (charge (re.code[pc]!).arg)
              (repCost re unit n ways charge
                (re.reps[(re.code[pc]!).arg]!).after
                (repBump re (re.code[pc]!) regs) pos)
              (repK (re.reps[(re.code[pc]!).arg]!) n
                (repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs))
                (repAhead re (re.code[pc]!) regs pos)) +
            repCost re unit n ways charge
              (re.reps[(re.code[pc]!).arg]!).after
              (repBump re (re.code[pc]!) regs) pos
      | _ =>
          unit (re.code[pc]!) +
            repCost re unit n ways charge (pc + 1) regs pos := by
  obtain ⟨f, hf⟩ : ∃ f, re.code.size = f + 1 := ⟨re.code.size - 1, by omega⟩
  obtain ⟨hsp, hjp, hrp⟩ := hfwd pc hpc
  unfold repCost
  have hL : repCostAt re unit n ways charge re.code.size pc regs pos =
      repCostAt re unit n ways charge (f + 1) pc regs pos := by rw [hf]
  rw [hL, repCostAt, if_neg (by omega)]
  split
  · rfl
  · rename_i hop
    rw [repCostAt_const hfwd f re.code.size _ _ _ (by have := (hsp hop).1; omega)
        (by omega),
      repCostAt_const hfwd f re.code.size _ _ _ (by have := (hsp hop).2; omega)
        (by omega)]
  · rename_i hop
    rw [repCostAt_const hfwd f re.code.size _ _ _ (by have := hjp hop; omega)
      (by omega)]
  · rw [repCostAt_const hfwd f re.code.size (pc + 1) _ _ (by omega) (by omega)]
  · rw [repCostAt_const hfwd f re.code.size (pc + 1) _ _ (by omega) (by omega)]
  · rename_i hop
    rw [repCostAt_const hfwd f re.code.size _ _ _
      (by have := hrp (Or.inl hop); omega) (by omega)]
  · rename_i hop
    rw [repCostAt_const hfwd f re.code.size _ _ _
      (by have := hrp (Or.inr hop); omega) (by omega)]
  · rw [repCostAt_const hfwd f re.code.size (pc + 1) _ _ (by omega) (by omega)]

end Pcrevera.Ref
