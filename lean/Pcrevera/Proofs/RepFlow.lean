import Pcrevera.Proofs.RepShape

/-!
# The fork account over the counted pricing (BOUNDS.md section 4.4)

`RepBounds.lean` builds the walk and `RepShape.lean` says what the code has to
say for it. This is where the two meet the account: the walk satisfies
`RegFlow`, so every theorem stated over a pricing — the cost account, the
budget account and the steady account — holds of a program with a counted
repetition in it.

Every clause but the head's is the walk read one step forward. The head is
where a repetition's price stops being a walk and becomes a closed form, so
what the head costs has to be compared against what a pass through the body
actually charges, and that comparison is the region tree's business rather
than one instruction's. It enters here as `PassPriced` and the tree induction
discharges it.

The counters carry no invariant of their own, which is worth saying because it
is not what one expects. The pricing reads a counter as a number and the
recurrence at the head needs the successor of that reading to be its
successor, so a counter at the sentinel would break the bound. What stops it
is the head's own maximum test, and unbounded the maximum it reads *is* the
sentinel: control leaves before the counter can wrap. All the domain asks of
the register file is that it be long enough to hold the counters, because a
`RepEnter` with nowhere to write would leave the empty-match rule with nothing
to fire on.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## The three charges of the BOUNDS.md section 3 table, with the
repetition opcodes in them -/

/-- Every instruction visited costs one. -/
def unitVisitR (_ : Inst) : Nat := 1

/-- An undo entry at every write: a `Save`, and the three repetition opcodes
that move a register. -/
def unitRecordR (i : Inst) : Nat :=
  if i.op = .save ∨ i.op = .repZero ∨ i.op = .repEnter ∨ i.op = .repNext then 1
  else 0

/-- A backtrack entry at every fork: a `Split`, and the head of a repetition,
which forks once per pass between going round again and leaving. -/
def unitPushR (i : Inst) : Nat :=
  if i.op = .split ∨ i.op = .repLoop then 1 else 0

theorem unitVisitR_eq (i : Inst) : unitVisitR i = 1 := rfl

theorem unitRecordR_le (i : Inst) : unitRecordR i ≤ 1 := by
  unfold unitRecordR; split <;> omega

theorem unitRecordR_write {i : Inst}
    (h : i.op = .save ∨ i.op = .repZero ∨ i.op = .repEnter ∨ i.op = .repNext) :
    unitRecordR i = 1 := by rw [unitRecordR, if_pos h]

theorem unitRecordR_quiet {i : Inst} (h1 : i.op ≠ .save) (h2 : i.op ≠ .repZero)
    (h3 : i.op ≠ .repEnter) (h4 : i.op ≠ .repNext) : unitRecordR i = 0 := by
  rw [unitRecordR, if_neg (by rintro (h | h | h | h) <;> simp_all)]

theorem unitPushR_fork {i : Inst} (h : i.op = .split ∨ i.op = .repLoop) :
    unitPushR i = 1 := by rw [unitPushR, if_pos h]

theorem unitPushR_quiet {i : Inst} (h1 : i.op ≠ .split) (h2 : i.op ≠ .repLoop) :
    unitPushR i = 0 := by
  rw [unitPushR, if_neg (by rintro (h | h) <;> simp_all)]

/-! ## The domain the pricing covers -/

/-- Inside the program, with the cursor inside the subject and a register file
long enough to hold every counter.

The counters themselves carry no invariant, and the reason is the head's own
maximum test. Bounded, it stops the count below the declared maximum;
unbounded, the maximum it reads is the sentinel, which is the largest value a
counter can hold — so the head leaves before its counter can wrap, and the
recurrence is only ever unfolded where the successor of a reading really is
its successor.

The file's length is the other half of the empty-match rule. A `RepEnter` with
nowhere to write would leave the position it remembers unset, the rule would
never fire, and an unbounded repetition would count without ever spending a
byte. -/
def RepOk (re : Re) (n : Nat) (pc : Nat) (regs : Array UInt32) (pos : Nat) :
    Prop :=
  pc < re.code.size ∧ pos ≤ n ∧ re.novec + re.reps.size * 2 ≤ regs.size

/-! ## What one pass through a head has to charge -/

/-- BOUNDS.md section 4.4's `A`, read against the walk rather than against the
checker: the head's own visit, the `RepEnter`, the body, and one `RepNext` per
way the body found to finish.

This is the one clause of the account a single instruction cannot settle. The
body is a span with child regions in it, so what it charges is what the region
tree says it charges, and the tree induction is what discharges this. -/
def PassPriced (re : Re) (unit : Inst → Nat) (n : Nat) (ways charge : Nat → Nat)
    (q : Nat) : Prop :=
  ∀ (regs : Array UInt32) (pos : Nat),
    unit (re.code[q]!) + unit (re.code[q + 1]!) +
        repCost re unit n ways charge (q + 2) regs pos +
        ways (re.code[q]!).arg *
          unit (re.code[(re.reps[(re.code[q]!).arg]!).after - 1]!) ≤
      charge (re.code[q]!).arg +
        ways (re.code[q]!).arg *
          repCost re unit n ways charge
            ((re.reps[(re.code[q]!).arg]!).after - 1) regs pos

/-! ## What a repetition's record has at the offsets it names

`RepCodeOk` reads the code and says where an opcode naming a repetition may
sit. The head needs the converse: that the offsets the record names hold the
opcodes the layout put there, because that is what turns one pass through the
head into the `RepEnter`, the body and the `RepNext` the price is written
over. `shape_repeat` checks exactly this, and `rep_header_of_cert` below reads
it back off an accepted certificate. -/

/-- The two ends of a counted repetition, read through its own record: the
body entry holds the `RepEnter` and the instruction before the exit holds the
`RepNext`, both naming the repetition, and the exit is a program point rather
than the end of the code. -/
structure RepHeader (re : Re) (a : Nat) : Prop where
  enterOp : (re.code[(re.reps[a]!).body]!).op = .repEnter
  enterArg : (re.code[(re.reps[a]!).body]!).arg = a
  tailOp : (re.code[(re.reps[a]!).after - 1]!).op = .repNext
  tailArg : (re.code[(re.reps[a]!).after - 1]!).arg = a
  exit : (re.reps[a]!).after < re.code.size

/-! ## The counter the head reads, counted on -/

/-- A counter with room left in it counts on as a number counts on. -/
theorem repCount_bump_succ {re : Re} {i : Inst} {regs : Array UInt32}
    (hlt : repSlot re i < regs.size)
    (hroom : repCount re i regs + 1 < UInt32.size) :
    repCount re i (repBump re i regs) = repCount re i regs + 1 := by
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have h2 : (regs[repSlot re i]!).toNat + 1 < 2 ^ 32 := hroom
  unfold repCount repBump
  rw [uset!_self _ _ _ hlt, UInt32.toNat_add, h1, Nat.mod_eq_of_lt h2]

/-- One pass spends one of the counter values the head still has to read.

Bounded, that is the count itself, and the head's own tests say the ceiling is
still ahead. Unbounded, the count only ever runs down to the minimum and what
spends a pass past it is the byte the empty-match rule asks for — which is why
the position the pass is priced at has to move on in exactly that case. -/
theorem repK_drop {rep : RepInfo} {n cnt pos pos' : Nat} (hpos : pos ≤ n)
    (harm : cnt < rep.lo ∨ cnt < rep.hi)
    (hbyte : rep.hi = none32 → rep.lo ≤ cnt + 1 → pos + 1 ≤ pos')
    (hle : pos ≤ pos') :
    repK rep n (cnt + 1) pos' + 1 ≤ repK rep n cnt pos := by
  unfold repK
  by_cases hb : rep.hi = none32
  · rw [if_pos hb, if_pos hb]
    by_cases hm : rep.lo ≤ cnt + 1
    · have h := hbyte hb hm
      omega
    · omega
  · rw [if_neg hb, if_neg hb]
    unfold repCeil
    rcases harm with h | h <;> split <;> omega

/-- And where the head enters the body at all, the counter is below the value
that would wrap it: below the minimum, which the compiler keeps inside a
counter, or below the maximum, which is the sentinel at the largest. -/
theorem repCount_room {rep : RepInfo} {cnt : Nat} (hlo : rep.lo ≤ none32)
    (hhi : rep.hi ≤ none32) (harm : cnt < rep.lo ∨ cnt < rep.hi) :
    cnt + 1 < UInt32.size := by
  have h1 : none32 = 4294967295 := rfl
  have h2 : UInt32.size = 4294967296 := by decide
  omega

/-! ## The pricing falls as the cursor moves on

`repCostAt_mono_pos` compares two runs at two cursors, and it asks that where
the earlier one says an iteration began at its own cursor, the later one says
the same of its. That is what a walk gives a walk one step apart. It is not
what one walk gives itself at a cursor that has really moved on: a register
holding the old position is not holding the new one, and it does not have to
be, because a pass priced from further along is a pass the empty-match rule
has already been paid for. Below is that reading, with the entry positions
left to say whatever they say.
-/

/-- Register files two walks can be compared across when the cursor has moved
on strictly: the counters agree, and nothing is asked of the positions the
`RepEnter`s remember. -/
structure RegsCounted (re : Re) (regs regs' : Array UInt32) : Prop where
  size : regs.size = regs'.size
  count : ∀ j : Nat, regs[re.novec + j * 2]! = regs'[re.novec + j * 2]!

theorem RegsCounted.zero {re : Re} {regs regs' : Array UInt32} {a : Nat}
    (h : RegsCounted re regs regs') :
    RegsCounted re (regs.set! (re.novec + a * 2) 0)
      (regs'.set! (re.novec + a * 2) 0) :=
  ⟨by rw [uset!_size, uset!_size]; exact h.size,
    fun j => uset!_agree h.size (h.count j)⟩

theorem RegsCounted.bump {re : Re} {regs regs' : Array UInt32} {a : Nat}
    (h : RegsCounted re regs regs') :
    RegsCounted re (regs.set! (re.novec + a * 2) (regs[re.novec + a * 2]! + 1))
      (regs'.set! (re.novec + a * 2) (regs'[re.novec + a * 2]! + 1)) := by
  rw [← h.count a]
  exact ⟨by rw [uset!_size, uset!_size]; exact h.size,
    fun j => uset!_agree h.size (h.count j)⟩

theorem RegsCounted.enter {re : Re} {regs regs' : Array UInt32} {a v v' : Nat}
    (h : RegsCounted re regs regs') :
    RegsCounted re (regs.set! (re.novec + a * 2 + 1) v.toUInt32)
      (regs'.set! (re.novec + a * 2 + 1) v'.toUInt32) :=
  ⟨by rw [uset!_size, uset!_size]; exact h.size,
    fun j => by
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact h.count j⟩

/-- Where the cursor has really moved on, the position a tail is priced from
has moved on with it, whatever the register file says: either the empty-match
rule fires at the new cursor, which is one further still, or it does not, and
the new cursor is already past the old one's answer. -/
theorem repAhead_lt {re : Re} {i : Inst} {regs regs' : Array UInt32}
    {pos pos' : Nat} (h : pos < pos') :
    repAhead re i regs pos ≤ repAhead re i regs' pos' := by
  unfold repAhead
  split <;> split <;> omega

/-- So the whole pricing falls, one walk against itself. -/
theorem repCostAt_fall {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat}
    (hhead : ∀ q : Nat, (re.code[q]!).op = .repLoop →
      unit (re.code[q]!) ≤ charge (re.code[q]!).arg)
    (htail : ∀ q : Nat, (re.code[q]!).op = .repNext →
      unit (re.code[(re.reps[(re.code[q]!).arg]!).head]!) ≤
        charge (re.code[q]!).arg) :
    ∀ (f pc : Nat) (regs regs' : Array UInt32) (pos pos' : Nat),
      pos < pos' → RegsCounted re regs regs' →
      repCostAt re unit n ways charge f pc regs' pos' ≤
        repCostAt re unit n ways charge f pc regs pos := by
  intro f
  induction f with
  | zero =>
      intro pc regs regs' pos pos' _ _
      rw [repCostAt, repCostAt]
      exact Nat.le_refl _
  | succ f ih =>
      intro pc regs regs' pos pos' hlt hc
      rw [repCostAt, repCostAt]
      by_cases hpc : pc ≥ re.code.size
      · rw [if_pos hpc, if_pos hpc]
        exact Nat.le_refl _
      rw [if_neg hpc, if_neg hpc]
      have hcnt : repCount re (re.code[pc]!) regs =
          repCount re (re.code[pc]!) regs' := by
        simp only [repCount, repSlot, hc.count (re.code[pc]!).arg]
      split
      · exact Nat.le_refl _
      · exact Nat.add_le_add (Nat.add_le_add_left (ih _ _ _ _ _ hlt hc) _)
          (ih _ _ _ _ _ hlt hc)
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hlt hc) _
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hlt hc.zero) _
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hlt hc.enter) _
      · rename_i hop
        exact repHeadPrice_le (hhead pc hop) (ih _ _ _ _ _ hlt hc)
          (hcnt ▸ repK_mono_pos (Nat.le_of_lt hlt))
      · rename_i hop
        have hb : RegsCounted re (repBump re (re.code[pc]!) regs)
            (repBump re (re.code[pc]!) regs') := by
          simp only [repBump, repSlot]
          exact hc.bump
        have hcb : repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs) =
            repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs') := by
          simp only [repCount, repSlot, hb.count (re.code[pc]!).arg]
        refine Nat.add_le_add (Nat.add_le_add_left ?_ _) (ih _ _ _ _ _ hlt hb)
        refine repHeadPrice_le (htail pc hop) (ih _ _ _ _ _ hlt hb) ?_
        rw [← hcb]
        exact repK_mono_pos (repAhead_lt hlt)
      · exact Nat.add_le_add_left (ih _ _ _ _ _ hlt hc) _

/-- The same, run on the whole program's worth of fuel and with the two
cursors allowed to be the one cursor. -/
theorem repCost_fall {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat}
    (hhead : ∀ q : Nat, (re.code[q]!).op = .repLoop →
      unit (re.code[q]!) ≤ charge (re.code[q]!).arg)
    (htail : ∀ q : Nat, (re.code[q]!).op = .repNext →
      unit (re.code[(re.reps[(re.code[q]!).arg]!).head]!) ≤
        charge (re.code[q]!).arg)
    {pc : Nat} {regs : Array UInt32} {pos pos' : Nat} (hle : pos ≤ pos') :
    repCost re unit n ways charge pc regs pos' ≤
      repCost re unit n ways charge pc regs pos := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact Nat.le_refl _
  · exact repCostAt_fall hhead htail _ _ _ _ _ _ hlt ⟨rfl, fun _ => rfl⟩

/-! ## What the price where control leaves does not depend on -/

/-- Past a repetition's exit no opcode names it, so the two slots it drives
are invisible there. This is what lets a region's claim be read against the
register file its parent hands in rather than against the one its own passes
leave behind. -/
theorem repCost_exit_stable {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} (hcode : ∀ q, q < re.code.size → RepCodeOk re q)
    {a : Nat} {regs : Array UInt32} {u v : UInt32} {pos : Nat} :
    repCost re unit n ways charge (re.reps[a]!).after
        ((regs.set! (re.novec + a * 2 + 1) u).set! (re.novec + a * 2) v) pos =
      repCost re unit n ways charge (re.reps[a]!).after regs pos := by
  unfold repCost
  refine repCostAt_local (fun q hq => (hcode q hq).fwd) _ _ _ _ _ ⟨?_, ?_⟩
  · rw [uset!_size, uset!_size]
  · intro q hq hq2 hop
    have hin := ((hcode q hq2).ranged hop).inside
    have hne : (re.code[q]!).arg ≠ a := by
      intro h
      rw [h] at hin
      omega
    have hslot : repSlot re (re.code[q]!) = re.novec + (re.code[q]!).arg * 2 := rfl
    rw [hslot]
    exact ⟨by rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)],
      by rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)]⟩

/-- Everything that neither forks, jumps nor drives a repetition moves on by
one and leaves the register file where it was. A `Save` is here too: the walk
has no clause for it, because the slot it writes is one the walk never
reads. -/
theorem repCost_onward {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hacc : (re.code[pc]!).op ≠ .accept) (hsp : (re.code[pc]!).op ≠ .split)
    (hjp : (re.code[pc]!).op ≠ .jump) (hz : (re.code[pc]!).op ≠ .repZero)
    (hen : (re.code[pc]!).op ≠ .repEnter) (hlp : (re.code[pc]!).op ≠ .repLoop)
    (htl : (re.code[pc]!).op ≠ .repNext) :
    repCost re unit n ways charge pc regs pos =
      unit (re.code[pc]!) + repCost re unit n ways charge (pc + 1) regs pos := by
  rw [repCost_unfold hfwd hpc]
  split
  · rename_i h; exact absurd h hacc
  · rename_i h; exact absurd h hsp
  · rename_i h; exact absurd h hjp
  · rename_i h; exact absurd h hz
  · rename_i h; exact absurd h hen
  · rename_i h; exact absurd h hlp
  · rename_i h; exact absurd h htl
  · rfl

/-! ## The head

The head is the one clause that has to be argued rather than read off the
walk. Leaving is the easy half: the closed form is one round of the recurrence
per pass still to come and the base is the pass that reads the spent count, so
whatever the count, the price of leaving is inside it.

Going round again is the other half, and it is where `PassPriced` is spent.
One pass is the head, the `RepEnter`, the body and one `RepNext` per way the
body found to finish; what the `RepNext` costs is the head again at one pass
fewer, and the two facts that make that a smaller number are that the price
where control leaves has not moved and that the pass really was spent.
-/

/-- Whatever the counter reads, the price of leaving the region is inside the
head's own price. -/
theorem repHead_leaves {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hop : (re.code[pc]!).op = .repLoop)
    (hu : unit (re.code[pc]!) ≤ charge (re.code[pc]!).arg) :
    unit (re.code[pc]!) +
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos ≤
      repCost re unit n ways charge pc regs pos := by
  have hX : 1 * repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after
        regs pos ≤
      (1 + ways (re.code[pc]!).arg) *
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.one_mul] at hX
  rw [repCost_unfold hfwd hpc]
  simp only [hop]
  unfold repHeadPrice
  exact repLeft_mono (by omega) (Nat.zero_le _)

/-- And where the head enters the body, one pass through it is inside the
head's own price too — which is the whole of the fork account at a head, since
the two arms of the fork are the body and the exit. -/
theorem repHead_enters {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hcode : ∀ q, q < re.code.size → RepCodeOk re q)
    (hhdr : RepHeader re (re.code[pc]!).arg)
    (hpass : PassPriced re unit n ways charge pc)
    (hu : unit (re.code[pc]!) ≤ charge (re.code[pc]!).arg)
    (hlo : (re.reps[(re.code[pc]!).arg]!).lo ≤ none32)
    (hhi : (re.reps[(re.code[pc]!).arg]!).hi ≤ none32)
    (hpc : pc < re.code.size) (hop : (re.code[pc]!).op = .repLoop)
    (hsize : re.novec + re.reps.size * 2 ≤ regs.size) (hpos : pos ≤ n)
    (harm : repCount re (re.code[pc]!) regs < (re.reps[(re.code[pc]!).arg]!).lo ∨
      repCount re (re.code[pc]!) regs < (re.reps[(re.code[pc]!).arg]!).hi) :
    unit (re.code[pc]!) +
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).body regs
          pos +
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos ≤
      repCost re unit n ways charge pc regs pos := by
  have hfwd : ∀ q, q < re.code.size → RepFwd re q := fun q hq => (hcode q hq).fwd
  obtain ⟨hhead, hbody⟩ := (hcode pc hpc).loop hop
  have ha : (re.code[pc]!).arg < re.reps.size :=
    ((hcode pc hpc).ranged (Or.inr (Or.inl hop))).1
  have honward : pc + 1 < re.code.size :=
    (hcode pc hpc).onward (by rw [hop]; decide)
  have hentOp : (re.code[pc + 1]!).op = .repEnter := by
    rw [← hbody]; exact hhdr.enterOp
  have hentArg : (re.code[pc + 1]!).arg = (re.code[pc]!).arg := by
    rw [← hbody]; exact hhdr.enterArg
  have htaillt : (re.reps[(re.code[pc]!).arg]!).after - 1 < re.code.size := by
    have := hhdr.exit; omega
  have hslotE : repSlot re (re.code[pc + 1]!) =
      re.novec + (re.code[pc]!).arg * 2 := by simp only [repSlot, hentArg]
  have hslotT : repSlot re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!) =
      re.novec + (re.code[pc]!).arg * 2 := by simp only [repSlot, hhdr.tailArg]
  have hsize1 : (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1)
      pos.toUInt32).size = regs.size := uset!_size _ _ _
  -- one pass, priced at the file the `RepEnter` leaves behind
  have hent : repCost re unit n ways charge (pc + 1) regs pos =
      unit (re.code[pc + 1]!) +
        repCost re unit n ways charge (pc + 2)
          (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32) pos := by
    rw [repCost_unfold hfwd honward]
    simp only [hentOp, hslotE]
  have hp := hpass (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1)
    pos.toUInt32) pos
  -- the counter, counted on, and the position the tail is priced from
  have hcntT : repCount re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
      (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32) =
      repCount re (re.code[pc]!) regs := by
    simp only [repCount, repSlot, hhdr.tailArg]
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
  have hcnt2 : repCount re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
      (repBump re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
        (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32)) =
      repCount re (re.code[pc]!) regs + 1 := by
    rw [repCount_bump_succ (by rw [hslotT, hsize1]; omega)
      (by rw [hcntT]; exact repCount_room hlo hhi harm), hcntT]
  have hentry : (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1)
      pos.toUInt32)[repSlot re
        (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!) + 1]! =
      pos.toUInt32 := by
    rw [hslotT]
    exact uset!_self _ _ _ (by omega)
  have hahead : pos ≤ repAhead re
      (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
      (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32) pos := by
    unfold repAhead
    split <;> omega
  have hbyte : (re.reps[(re.code[pc]!).arg]!).hi = none32 →
      (re.reps[(re.code[pc]!).arg]!).lo ≤ repCount re (re.code[pc]!) regs + 1 →
      pos + 1 ≤ repAhead re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
        (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32) pos := by
    intro hb hm
    unfold repAhead
    rw [if_pos ⟨by rw [hhdr.tailArg]; exact hb,
      by rw [hhdr.tailArg, hcnt2]; exact hm, hentry⟩]
    omega
  have hK := repK_drop (rep := re.reps[(re.code[pc]!).arg]!) (n := n) hpos harm
    hbyte hahead
  -- the tail, priced at the file that pass leaves behind
  have hbumpEq : repBump re
        (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
        (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32) =
      (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32).set!
        (re.novec + (re.code[pc]!).arg * 2)
        (regs[re.novec + (re.code[pc]!).arg * 2]! + 1) := by
    unfold repBump
    rw [hslotT, Array.getElem!_set!_ne _ _ _ _ (by omega)]
  have hX2 : repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after
        (repBump re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
          (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32)) pos =
      repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
        pos := by
    rw [hbumpEq]
    exact repCost_exit_stable hcode
  have htl : repCost re unit n ways charge
        ((re.reps[(re.code[pc]!).arg]!).after - 1)
        (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32) pos =
      unit (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!) +
        repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
          (charge (re.code[pc]!).arg)
          (repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after
            regs pos)
          (repK (re.reps[(re.code[pc]!).arg]!) n
            (repCount re (re.code[pc]!) regs + 1)
            (repAhead re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
              (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32)
              pos)) +
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos := by
    rw [repCost_unfold hfwd htaillt]
    simp only [hhdr.tailOp, hhdr.tailArg, ← hhead, hcnt2, hX2]
  have hhp : repCost re unit n ways charge pc regs pos =
      repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
        (charge (re.code[pc]!).arg)
        (repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos)
        (repK (re.reps[(re.code[pc]!).arg]!) n
          (repCount re (re.code[pc]!) regs) pos) := by
    rw [repCost_unfold hfwd hpc]
    simp only [hop]
  -- and the round of the recurrence that pass is
  obtain ⟨k, hkeq⟩ : ∃ k, repK (re.reps[(re.code[pc]!).arg]!) n
      (repCount re (re.code[pc]!) regs) pos = k + 1 :=
    ⟨repK (re.reps[(re.code[pc]!).arg]!) n (repCount re (re.code[pc]!) regs)
      pos - 1, by omega⟩
  have hX : 1 * repCost re unit n ways charge
        (re.reps[(re.code[pc]!).arg]!).after regs pos ≤
      (1 + ways (re.code[pc]!).arg) *
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.one_mul] at hX
  have hmono : repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
        (charge (re.code[pc]!).arg)
        (repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos)
        (repK (re.reps[(re.code[pc]!).arg]!) n
          (repCount re (re.code[pc]!) regs + 1)
          (repAhead re (re.code[(re.reps[(re.code[pc]!).arg]!).after - 1]!)
            (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32)
            pos)) ≤
      repLeft (ways (re.code[pc]!).arg)
        (charge (re.code[pc]!).arg + (1 + ways (re.code[pc]!).arg) *
          repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
            pos)
        (unit (re.code[pc]!) +
          repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
            pos) k := by
    unfold repHeadPrice
    exact repLeft_mono (by omega) (by omega)
  have hstep : repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
      (charge (re.code[pc]!).arg)
      (repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
        pos) (k + 1) =
      (charge (re.code[pc]!).arg + (1 + ways (re.code[pc]!).arg) *
          repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
            pos) +
        ways (re.code[pc]!).arg *
          repLeft (ways (re.code[pc]!).arg)
            (charge (re.code[pc]!).arg + (1 + ways (re.code[pc]!).arg) *
              repCost re unit n ways charge
                (re.reps[(re.code[pc]!).arg]!).after regs pos)
            (unit (re.code[pc]!) +
              repCost re unit n ways charge
                (re.reps[(re.code[pc]!).arg]!).after regs pos) k := rfl
  have hshare : (1 + ways (re.code[pc]!).arg) *
        repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos =
      repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos +
        ways (re.code[pc]!).arg *
          repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
            pos := by
    rw [Nat.add_mul, Nat.one_mul]
  have hways := Nat.mul_le_mul_left (ways (re.code[pc]!).arg) hmono
  rw [htl, Nat.mul_add, Nat.mul_add] at hp
  rw [hbody, hent, hhp, hkeq, hstep]
  omega

/-! ## The account -/

/-- BOUNDS.md section 4.4's last piece: the counted pricing prices a program's
control flow, counted repetitions and all.

Six clauses are the walk read one step forward and settle themselves. The
`Save` is the seventh, and it holds because the slot a `Save` names is one the
walk never reads — the first of the two rules the checker does not have. The
tail is the eighth, and it needs no counter fact at all: the walk's own exit
test is the run's, so on the arm that goes back to the head the two pass counts
are the same number and on the arm that leaves, the price of leaving is what
pays.

The head is the ninth and it is the whole of section 4.4. What a pass through
it charges is `PassPriced`, which the region tree settles; what makes a pass
smaller than the head's own price is that the pass was really spent, and that
is `repK_drop`.

`hfits` is the third rule the checker does not have: a repetition's declared
bounds fit in a counter. `hcw` and `hct` say a pass charges at least the head's
own visit and its own fork, which is what makes the closed form monotone in the
passes still to come — the record's charge has no such clause because a
`RepLoop` records nothing. -/
theorem regFlow_of_repCode {re : Re} {n : Nat}
    {ways chargeW chargeR chargeT : Nat → Nat}
    (hcode : ∀ q, q < re.code.size → RepCodeOk re q)
    (hhdr : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      RepHeader re (re.code[q]!).arg)
    (hsave : ∀ q, q < re.code.size → (re.code[q]!).op = .save →
      (re.code[q]!).arg < re.novec)
    (hfits : ∀ a : Nat, a < re.reps.size →
      (re.reps[a]!).lo ≤ none32 ∧ (re.reps[a]!).hi ≤ none32)
    (hcw : ∀ a : Nat, a < re.reps.size → 1 ≤ chargeW a)
    (hct : ∀ a : Nat, a < re.reps.size → 1 ≤ chargeT a)
    (hpassW : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      PassPriced re unitVisitR n ways chargeW q)
    (hpassR : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      PassPriced re unitRecordR n ways chargeR q)
    (hpassT : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      PassPriced re unitPushR n ways chargeT q) :
    RegFlow re (RepOk re n) (repCost re unitVisitR n ways chargeW)
      (repCost re unitRecordR n ways chargeR)
      (repCost re unitPushR n ways chargeT) n := by
  have hfwd : ∀ q, q < re.code.size → RepFwd re q := fun q hq => (hcode q hq).fwd
  have hchr : ∀ q : Nat, re.code.size ≤ q → (re.code[q]!).op = .chr := by
    intro q hq
    rw [getElem!_neg re.code q (by omega)]
    rfl
  have hargOf : ∀ q : Nat,
      ((re.code[q]!).op = .repLoop ∨ (re.code[q]!).op = .repNext) →
      (re.code[q]!).arg < re.reps.size := by
    intro q hq
    rcases Nat.lt_or_ge q re.code.size with h | h
    · rcases hq with hq | hq
      · exact ((hcode q h).ranged (Or.inr (Or.inl hq))).1
      · exact ((hcode q h).ranged (Or.inr (Or.inr (Or.inr hq)))).1
    · rw [hchr q h] at hq
      rcases hq with hq | hq <;> exact absurd hq (by decide)
  have hloopAt : ∀ q : Nat, (re.code[q]!).op = .repNext →
      (re.code[(re.reps[(re.code[q]!).arg]!).head]!).op = .repLoop := by
    intro q hq
    rcases Nat.lt_or_ge q re.code.size with h | h
    · exact ((hcode q h).head hq).1
    · rw [hchr q h] at hq
      exact absurd hq (by decide)
  have hheadW : ∀ q : Nat, (re.code[q]!).op = .repLoop →
      unitVisitR (re.code[q]!) ≤ chargeW (re.code[q]!).arg :=
    fun q hq => by rw [unitVisitR_eq]; exact hcw _ (hargOf q (Or.inl hq))
  have htailW : ∀ q : Nat, (re.code[q]!).op = .repNext →
      unitVisitR (re.code[(re.reps[(re.code[q]!).arg]!).head]!) ≤
        chargeW (re.code[q]!).arg :=
    fun q hq => by rw [unitVisitR_eq]; exact hcw _ (hargOf q (Or.inr hq))
  have hheadR : ∀ q : Nat, (re.code[q]!).op = .repLoop →
      unitRecordR (re.code[q]!) ≤ chargeR (re.code[q]!).arg := by
    intro q hq
    rw [unitRecordR_quiet (by rw [hq]; decide) (by rw [hq]; decide)
      (by rw [hq]; decide) (by rw [hq]; decide)]
    exact Nat.zero_le _
  have htailR : ∀ q : Nat, (re.code[q]!).op = .repNext →
      unitRecordR (re.code[(re.reps[(re.code[q]!).arg]!).head]!) ≤
        chargeR (re.code[q]!).arg := by
    intro q hq
    have h := hloopAt q hq
    rw [unitRecordR_quiet (by rw [h]; decide) (by rw [h]; decide)
      (by rw [h]; decide) (by rw [h]; decide)]
    exact Nat.zero_le _
  have hheadT : ∀ q : Nat, (re.code[q]!).op = .repLoop →
      unitPushR (re.code[q]!) ≤ chargeT (re.code[q]!).arg := by
    intro q hq
    rw [unitPushR_fork (Or.inr hq)]
    exact hct _ (hargOf q (Or.inl hq))
  have htailT : ∀ q : Nat, (re.code[q]!).op = .repNext →
      unitPushR (re.code[(re.reps[(re.code[q]!).arg]!).head]!) ≤
        chargeT (re.code[q]!).arg := by
    intro q hq
    rw [unitPushR_fork (Or.inr (hloopAt q hq))]
    exact hct _ (hargOf q (Or.inr hq))
  intro pc regs pos hok
  obtain ⟨hpc, hpos, hsize⟩ := hok
  by_cases hacc : (re.code[pc]!).op = .accept
  · refine Or.inl ⟨hacc, ?_⟩
    have hstop : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c pc regs pos = u (re.code[pc]!) := by
      intro u c
      rw [repCost_unfold hfwd hpc]
      simp only [hacc]
    have hW := hstop unitVisitR chargeW
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    omega
  by_cases hsp : (re.code[pc]!).op = .split
  · obtain ⟨harg, halt⟩ := (hcode pc hpc).split hsp
    have hstep : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c pc regs pos =
          u (re.code[pc]!) + repCost re u n ways c (re.code[pc]!).arg regs pos +
            repCost re u n ways c (re.code[pc]!).alt regs pos := by
      intro u c
      rw [repCost_unfold hfwd hpc]
      simp only [hsp]
    have hW := hstep unitVisitR chargeW
    have hR := hstep unitRecordR chargeR
    have hT := hstep unitPushR chargeT
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    have hvR : unitRecordR (re.code[pc]!) = 0 :=
      unitRecordR_quiet (by rw [hsp]; decide) (by rw [hsp]; decide)
        (by rw [hsp]; decide) (by rw [hsp]; decide)
    have hvT : unitPushR (re.code[pc]!) = 1 := unitPushR_fork (Or.inl hsp)
    exact Or.inr (Or.inl ⟨hsp, ⟨harg, hpos, hsize⟩, ⟨halt, hpos, hsize⟩,
      by omega, by omega, by omega⟩)
  by_cases hjp : (re.code[pc]!).op = .jump
  · have harg := (hcode pc hpc).jump hjp
    have hstep : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c pc regs pos =
          u (re.code[pc]!) +
            repCost re u n ways c (re.code[pc]!).arg regs pos := by
      intro u c
      rw [repCost_unfold hfwd hpc]
      simp only [hjp]
    have hW := hstep unitVisitR chargeW
    have hR := hstep unitRecordR chargeR
    have hT := hstep unitPushR chargeT
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    have hvR : unitRecordR (re.code[pc]!) = 0 :=
      unitRecordR_quiet (by rw [hjp]; decide) (by rw [hjp]; decide)
        (by rw [hjp]; decide) (by rw [hjp]; decide)
    have hvT : unitPushR (re.code[pc]!) = 0 :=
      unitPushR_quiet (by rw [hjp]; decide) (by rw [hjp]; decide)
    exact Or.inr (Or.inr (Or.inl ⟨hjp, ⟨harg, hpos, hsize⟩, by omega, by omega,
      by omega⟩))
  by_cases hz : (re.code[pc]!).op = .repZero
  · have honward : pc + 1 < re.code.size :=
      (hcode pc hpc).onward (by rw [hz]; decide)
    have hstep : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c pc regs pos =
          u (re.code[pc]!) + repCost re u n ways c (pc + 1)
            (regs.set! (repSlot re (re.code[pc]!)) 0) pos := by
      intro u c
      rw [repCost_unfold hfwd hpc]
      simp only [hz]
    have hW := hstep unitVisitR chargeW
    have hR := hstep unitRecordR chargeR
    have hT := hstep unitPushR chargeT
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    have hvR : unitRecordR (re.code[pc]!) = 1 :=
      unitRecordR_write (Or.inr (Or.inl hz))
    have hvT : unitPushR (re.code[pc]!) = 0 :=
      unitPushR_quiet (by rw [hz]; decide) (by rw [hz]; decide)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz,
      ⟨honward, hpos, by rw [uset!_size]; exact hsize⟩, by omega, by omega,
      by omega⟩))))
  by_cases hen : (re.code[pc]!).op = .repEnter
  · have honward : pc + 1 < re.code.size :=
      (hcode pc hpc).onward (by rw [hen]; decide)
    have hstep : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c pc regs pos =
          u (re.code[pc]!) + repCost re u n ways c (pc + 1)
            (regs.set! (repSlot re (re.code[pc]!) + 1) pos.toUInt32) pos := by
      intro u c
      rw [repCost_unfold hfwd hpc]
      simp only [hen]
    have hW := hstep unitVisitR chargeW
    have hR := hstep unitRecordR chargeR
    have hT := hstep unitPushR chargeT
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    have hvR : unitRecordR (re.code[pc]!) = 1 :=
      unitRecordR_write (Or.inr (Or.inr (Or.inl hen)))
    have hvT : unitPushR (re.code[pc]!) = 0 :=
      unitPushR_quiet (by rw [hen]; decide) (by rw [hen]; decide)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hen,
      ⟨honward, hpos, by rw [uset!_size]; exact hsize⟩, by omega, by omega,
      by omega⟩)))))
  by_cases hlp : (re.code[pc]!).op = .repLoop
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hlp, ?_⟩))))))
    obtain ⟨-, hbody⟩ := (hcode pc hpc).loop hlp
    have ha : (re.code[pc]!).arg < re.reps.size :=
      ((hcode pc hpc).ranged (Or.inr (Or.inl hlp))).1
    have hhdr' := hhdr pc hpc hlp
    have hokB : RepOk re n (re.reps[(re.code[pc]!).arg]!).body regs pos :=
      ⟨by rw [hbody]; exact (hcode pc hpc).onward (by rw [hlp]; decide), hpos,
        hsize⟩
    have hokA : RepOk re n (re.reps[(re.code[pc]!).arg]!).after regs pos :=
      ⟨hhdr'.exit, hpos, hsize⟩
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    have hvR : unitRecordR (re.code[pc]!) = 0 :=
      unitRecordR_quiet (by rw [hlp]; decide) (by rw [hlp]; decide)
        (by rw [hlp]; decide) (by rw [hlp]; decide)
    have hvT : unitPushR (re.code[pc]!) = 1 := unitPushR_fork (Or.inr hlp)
    have hleaveW := repHead_leaves (unit := unitVisitR) (n := n) (ways := ways)
      (charge := chargeW) (regs := regs) (pos := pos) hfwd hpc hlp
      (by rw [hvW]; exact hcw _ ha)
    have hleaveR := repHead_leaves (unit := unitRecordR) (n := n) (ways := ways)
      (charge := chargeR) (regs := regs) (pos := pos) hfwd hpc hlp
      (by rw [hvR]; exact Nat.zero_le _)
    have hleaveT := repHead_leaves (unit := unitPushR) (n := n) (ways := ways)
      (charge := chargeT) (regs := regs) (pos := pos) hfwd hpc hlp
      (by rw [hvT]; exact hct _ ha)
    have henter : ∀ _harm : repCount re (re.code[pc]!) regs <
          (re.reps[(re.code[pc]!).arg]!).lo ∨
        repCount re (re.code[pc]!) regs < (re.reps[(re.code[pc]!).arg]!).hi,
        unitVisitR (re.code[pc]!) +
            repCost re unitVisitR n ways chargeW
              (re.reps[(re.code[pc]!).arg]!).body regs pos +
            repCost re unitVisitR n ways chargeW
              (re.reps[(re.code[pc]!).arg]!).after regs pos ≤
          repCost re unitVisitR n ways chargeW pc regs pos ∧
        unitRecordR (re.code[pc]!) +
            repCost re unitRecordR n ways chargeR
              (re.reps[(re.code[pc]!).arg]!).body regs pos +
            repCost re unitRecordR n ways chargeR
              (re.reps[(re.code[pc]!).arg]!).after regs pos ≤
          repCost re unitRecordR n ways chargeR pc regs pos ∧
        unitPushR (re.code[pc]!) +
            repCost re unitPushR n ways chargeT
              (re.reps[(re.code[pc]!).arg]!).body regs pos +
            repCost re unitPushR n ways chargeT
              (re.reps[(re.code[pc]!).arg]!).after regs pos ≤
          repCost re unitPushR n ways chargeT pc regs pos := by
      intro harm
      exact ⟨repHead_enters hcode hhdr' (hpassW pc hpc hlp)
          (by rw [hvW]; exact hcw _ ha) (hfits _ ha).1 (hfits _ ha).2 hpc hlp
          hsize hpos harm,
        repHead_enters hcode hhdr' (hpassR pc hpc hlp)
          (by rw [hvR]; exact Nat.zero_le _) (hfits _ ha).1 (hfits _ ha).2 hpc
          hlp hsize hpos harm,
        repHead_enters hcode hhdr' (hpassT pc hpc hlp)
          (by rw [hvT]; exact hct _ ha) (hfits _ ha).1 (hfits _ ha).2 hpc hlp
          hsize hpos harm⟩
    -- the head's tests read the counter the walk prices it by
    have hcv : repCount re (re.code[pc]!) regs =
      (regs[repSlot re (re.code[pc]!)]!).toNat := rfl
    simp only [RepHead]
    by_cases h1 : (regs[repSlot re (re.code[pc]!)]!).toNat <
        (re.reps[(re.code[pc]!).arg]!).lo
    · rw [if_pos h1]
      obtain ⟨heW, heR, heT⟩ := henter (Or.inl h1)
      exact ⟨hokB, by omega, by omega, by omega⟩
    rw [if_neg h1]
    by_cases h2 : (regs[repSlot re (re.code[pc]!)]!).toNat ≥
        (re.reps[(re.code[pc]!).arg]!).hi
    · rw [if_pos h2]
      exact ⟨hokA, by omega, by omega, by omega⟩
    rw [if_neg h2]
    obtain ⟨heW, heR, heT⟩ := henter (Or.inr (by omega))
    by_cases h3 : (re.reps[(re.code[pc]!).arg]!).greedy = true
    · rw [if_pos h3]
      exact ⟨hokB, hokA, by omega, by omega, by omega⟩
    · rw [if_neg h3]
      exact ⟨hokA, hokB, by omega, by omega, by omega⟩
  by_cases htl : (re.code[pc]!).op = .repNext
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨htl, ?_⟩)))))))
    have ha : (re.code[pc]!).arg < re.reps.size :=
      ((hcode pc hpc).ranged (Or.inr (Or.inr (Or.inr htl)))).1
    obtain ⟨hheadOp, hheadArg⟩ := (hcode pc hpc).head htl
    have hheadlt : (re.reps[(re.code[pc]!).arg]!).head < re.code.size := by
      rcases Nat.lt_or_ge (re.reps[(re.code[pc]!).arg]!).head re.code.size with
        h | h
      · exact h
      · rw [hchr _ h] at hheadOp
        exact absurd hheadOp (by decide)
    have hhdr' : RepHeader re (re.code[pc]!).arg := by
      have h := hhdr _ hheadlt hheadOp
      rwa [hheadArg] at h
    have hslotlt : repSlot re (re.code[pc]!) + 1 < regs.size := by
      simp only [repSlot]; omega
    have hbump : regs.set! (repSlot re (re.code[pc]!))
        (regs[repSlot re (re.code[pc]!)]! + 1) =
      repBump re (re.code[pc]!) regs := rfl
    have hsizeB : (repBump re (re.code[pc]!) regs).size = regs.size :=
      uset!_size _ _ _
    have hokA : RepOk re n (re.reps[(re.code[pc]!).arg]!).after
        (repBump re (re.code[pc]!) regs) pos :=
      ⟨hhdr'.exit, hpos, by rw [hsizeB]; exact hsize⟩
    have hokH : RepOk re n (re.reps[(re.code[pc]!).arg]!).head
        (repBump re (re.code[pc]!) regs) pos :=
      ⟨hheadlt, hpos, by rw [hsizeB]; exact hsize⟩
    have hstep : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c pc regs pos =
          u (re.code[pc]!) +
            repHeadPrice (u (re.code[(re.reps[(re.code[pc]!).arg]!).head]!))
              (ways (re.code[pc]!).arg) (c (re.code[pc]!).arg)
              (repCost re u n ways c (re.reps[(re.code[pc]!).arg]!).after
                (repBump re (re.code[pc]!) regs) pos)
              (repK (re.reps[(re.code[pc]!).arg]!) n
                (repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs))
                (repAhead re (re.code[pc]!) regs pos)) +
            repCost re u n ways c (re.reps[(re.code[pc]!).arg]!).after
              (repBump re (re.code[pc]!) regs) pos := by
      intro u c
      rw [repCost_unfold hfwd hpc]
      simp only [htl]
    have hW := hstep unitVisitR chargeW
    have hR := hstep unitRecordR chargeR
    have hT := hstep unitPushR chargeT
    have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
    have hvR : unitRecordR (re.code[pc]!) = 1 :=
      unitRecordR_write (Or.inr (Or.inr (Or.inr htl)))
    have hvT : unitPushR (re.code[pc]!) = 0 :=
      unitPushR_quiet (by rw [htl]; decide) (by rw [htl]; decide)
    simp only [RepTail]
    rw [hbump]
    by_cases hcond : ((re.reps[(re.code[pc]!).arg]!).hi == none32 &&
        pos.toUInt32 == regs[repSlot re (re.code[pc]!) + 1]! &&
        decide ((regs[repSlot re (re.code[pc]!)]! + 1).toNat ≥
          (re.reps[(re.code[pc]!).arg]!).lo)) = true
    · rw [if_pos hcond]
      exact ⟨hokA, by omega, by omega, by omega⟩
    rw [if_neg hcond]
    have hahead : repAhead re (re.code[pc]!) regs pos = pos := by
      have hcv : repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs) =
          (regs[repSlot re (re.code[pc]!)]! + 1).toNat := by
        simp only [repCount, repBump]
        rw [uset!_self _ _ _ (by omega)]
      unfold repAhead
      rw [if_neg (by
        intro h
        apply hcond
        rw [hcv] at h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        exact ⟨⟨h.1, h.2.2.symm⟩, h.2.1⟩)]
    have hcnteq : repCount re (re.code[(re.reps[(re.code[pc]!).arg]!).head]!)
          (repBump re (re.code[pc]!) regs) =
        repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs) := by
      simp only [repCount, repSlot, hheadArg]
    have hback : ∀ (u : Inst → Nat) (c : Nat → Nat),
        repCost re u n ways c (re.reps[(re.code[pc]!).arg]!).head
            (repBump re (re.code[pc]!) regs) pos =
          repHeadPrice (u (re.code[(re.reps[(re.code[pc]!).arg]!).head]!))
            (ways (re.code[pc]!).arg) (c (re.code[pc]!).arg)
            (repCost re u n ways c (re.reps[(re.code[pc]!).arg]!).after
              (repBump re (re.code[pc]!) regs) pos)
            (repK (re.reps[(re.code[pc]!).arg]!) n
              (repCount re (re.code[pc]!) (repBump re (re.code[pc]!) regs))
              pos) := by
      intro u c
      rw [repCost_unfold hfwd hheadlt]
      simp only [hheadOp, hheadArg, hcnteq]
    have hbW := hback unitVisitR chargeW
    have hbR := hback unitRecordR chargeR
    have hbT := hback unitPushR chargeT
    rw [hahead] at hW hR hT
    exact ⟨hokH, by omega, by omega, by omega⟩
  have hlast : (re.code[pc]!).op = .save ∨
      ((re.code[pc]!).op.loose = true ∧ (re.code[pc]!).op ≠ .save) := by
    by_cases h : (re.code[pc]!).op = .save
    · exact Or.inl h
    refine Or.inr ⟨?_, h⟩
    cases hc : (re.code[pc]!).op <;>
      first
        | rfl
        | exact absurd hc hsp
        | exact absurd hc hjp
        | exact absurd hc hz
        | exact absurd hc hen
        | exact absurd hc hlp
        | exact absurd hc htl
  have honward : pc + 1 < re.code.size := (hcode pc hpc).onward hacc
  have hstep : ∀ (u : Inst → Nat) (c : Nat → Nat),
      repCost re u n ways c pc regs pos =
        u (re.code[pc]!) + repCost re u n ways c (pc + 1) regs pos :=
    fun u c => repCost_onward hfwd hpc hacc hsp hjp hz hen hlp htl
  have hW := hstep unitVisitR chargeW
  have hR := hstep unitRecordR chargeR
  have hT := hstep unitPushR chargeT
  have hvW : unitVisitR (re.code[pc]!) = 1 := unitVisitR_eq _
  have hvT : unitPushR (re.code[pc]!) = 0 := unitPushR_quiet hsp hlp
  rcases hlast with hsv | hlo
  · have hvR : unitRecordR (re.code[pc]!) = 1 := unitRecordR_write (Or.inl hsv)
    have hcW : repCost re unitVisitR n ways chargeW (pc + 1)
          (regs.set! (re.code[pc]!).arg pos.toUInt32) pos =
        repCost re unitVisitR n ways chargeW (pc + 1) regs pos := by
      unfold repCost
      exact repCostAt_congr _ _ _ _ _ (RegsSame.below (hsave pc hpc hsv))
    have hcR : repCost re unitRecordR n ways chargeR (pc + 1)
          (regs.set! (re.code[pc]!).arg pos.toUInt32) pos =
        repCost re unitRecordR n ways chargeR (pc + 1) regs pos := by
      unfold repCost
      exact repCostAt_congr _ _ _ _ _ (RegsSame.below (hsave pc hpc hsv))
    have hcT : repCost re unitPushR n ways chargeT (pc + 1)
          (regs.set! (re.code[pc]!).arg pos.toUInt32) pos =
        repCost re unitPushR n ways chargeT (pc + 1) regs pos := by
      unfold repCost
      exact repCostAt_congr _ _ _ _ _ (RegsSame.below (hsave pc hpc hsv))
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsv,
      ⟨honward, hpos, by rw [uset!_size]; exact hsize⟩, by omega, by omega,
      by omega⟩)))
  · obtain ⟨hlo, hnotsave⟩ := hlo
    have hvR : unitRecordR (re.code[pc]!) = 0 :=
      unitRecordR_quiet hnotsave hz hen htl
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hlo, hnotsave, hacc, ?_⟩)))))))
    intro pos' hle hbnd
    have hfW := repCost_fall (unit := unitVisitR) (n := n) (ways := ways)
      (charge := chargeW) hheadW htailW (pc := pc + 1) (regs := regs) hle
    have hfR := repCost_fall (unit := unitRecordR) (n := n) (ways := ways)
      (charge := chargeR) hheadR htailR (pc := pc + 1) (regs := regs) hle
    have hfT := repCost_fall (unit := unitPushR) (n := n) (ways := ways)
      (charge := chargeT) hheadT htailT (pc := pc + 1) (regs := regs) hle
    exact ⟨⟨honward, hbnd, hsize⟩, by omega, by omega, by omega⟩

/-! ## Reading the header off an accepted certificate

`rep_code_ok_of_cert` says where an opcode naming a repetition may sit, which
is what the walk's forwardness needs. The head needs the other direction, and
that is the same tree walk again with the counted arm of `shape_repeat` read
for what it puts at the record's own offsets.
-/

/-- The chain walk of `shape_alt`, read as coverage. What an alternation's
range holds beyond its branches is one split before each of them and one jump
after, so whatever holds of those two and of every branch's range holds of the
whole of it. -/
theorem shapeAltGo_holds {re : Re} {sibs : Array Nat} {hi : Nat}
    {Q : Nat → Prop} (hsplit : ∀ q : Nat, (re.code[q]!).op = .split → Q q)
    (hjump : ∀ q : Nat, (re.code[q]!).op = .jump → Q q)
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hle : ∀ c : Nat, P c → c ≠ none32 →
      (re.regions[c]!).lo ≤ (re.regions[c]!).hi)
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      ∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi → Q q) :
    ∀ (fuel p c k : Nat), P c →
      shapeAltGo re.code re.regions sibs hi fuel p c k = .crOk → c ≠ none32 →
      ∀ q, p ≤ q → q < hi → Q q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p c k _ h hne q _ _
      rw [shapeAltGo, if_pos hne] at h
      exact absurd h (by decide)
  | succ fuel ih =>
      intro p c k hP h hne q h1 h2
      rcases shapeAltGo_step hne h with
        ⟨hnxt, hph, hforkop, harg, hclo, hstop, hleaveop, hleavearg, halt, hrec⟩ |
        ⟨hnxt, hclo, hchi, hrec⟩
      · have hlh := hle c hP hne
        by_cases hq : q = p
        · subst hq
          exact hsplit _ hforkop
        by_cases hq2 : q < (re.regions[c]!).hi
        · exact hkid c hP hne q (by omega) hq2
        by_cases hq3 : q = (re.regions[c]!).hi
        · subst hq3
          exact hjump _ hleaveop
        · exact ih ((re.regions[c]!).hi + 1) (sibs[c]!) (k + 1) (hsib c hP hne)
            hrec hnxt q (by omega) h2
      · exact hkid c hP hne q (by omega) (by omega)

/-- The walk downwards over the region tree, run for the header. Only the
counted arm of a repeat region has anything to say: everywhere else a
`RepLoop` is refused by name, so the claim holds where there is nothing to
claim. -/
theorem region_rep_header {re : Re}
    (hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i)
    (hrange : ∀ i, i < re.regions.size →
      (re.regions[i]!).lo ≤ (re.regions[i]!).hi)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hshape : ∀ j, j < re.regions.size →
      ShapeOk re (regionKids re.regions).1 (regionKids re.regions).2 j) :
    ∀ (k i : Nat), re.regions.size - i ≤ k → i < re.regions.size →
      ∀ q, (re.regions[i]!).lo ≤ q → q < (re.regions[i]!).hi →
        (re.code[q]!).op = .repLoop → RepHeader re (re.code[q]!).arg := by
  intro k
  induction k with
  | zero =>
      intro i hk hi q _ _
      omega
  | succ k ih =>
      intro i hk hi q h1 h2
      have hpos : 0 < re.regions.size := by omega
      have hkid : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ∀ q', (re.regions[c]!).lo ≤ q' → q' < (re.regions[c]!).hi →
            (re.code[q']!).op = .repLoop → RepHeader re (re.code[q']!).arg := by
        intro c hP hne
        rcases hP with rfl | ⟨hic, hcs, -⟩
        · exact absurd rfl hne
        · exact fun q' g1 g2 => ih c (by omega) hcs q' g1 g2
      have hsib : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ChildOf re.regions i ((regionKids re.regions).2[c]!) :=
        fun c hP hne => regionKids_next hpos hord i c hP hne
      have hfirst : ChildOf re.regions i ((regionKids re.regions).1[i]!) :=
        regionKids_first hpos hord i hi
      have hloose : ∀ q' : Nat, (re.code[q']!).op.loose = true →
          ((re.code[q']!).op = .repLoop → RepHeader re (re.code[q']!).arg) :=
        fun q' hl hlp => by rw [hlp] at hl; exact absurd hl (by decide)
      have hsh := hshape i hi
      unfold ShapeOk at hsh
      by_cases hkalt : (re.regions[i]!).kind = .alt
      · rw [hkalt] at hsh
        dsimp only at hsh
        have hfne := shapeAlt_first_ne hsh
        rw [shapeAlt] at hsh
        exact shapeAltGo_holds
          (fun q' hs hlp => by rw [hlp] at hs; exact absurd hs (by decide))
          (fun q' hj hlp => by rw [hlp] at hj; exact absurd hj (by decide))
          (ChildOf re.regions i) hsib
          (fun c hP hne => by
            rcases hP with rfl | ⟨-, hcs, -⟩
            · exact absurd rfl hne
            · exact hrange c hcs)
          hkid re.regions.size (re.regions[i]!).lo
          ((regionKids re.regions).1[i]!) 0 hfirst hsh hfne q h1 h2
      by_cases hkrep : (re.regions[i]!).kind = .«repeat»
      · rw [hkrep] at hsh
        dsimp only at hsh
        have hhi := hends i hi (Or.inr hkrep)
        rcases shapeRepeat_head hsh with hsp | hz
        · obtain ⟨hlt, harms, hbody⟩ := shapeRepeat_opt hsp hsh
          by_cases hq0 : q = (re.regions[i]!).lo
          · subst hq0
            exact fun hlp => by rw [hlp] at hsp; exact absurd hsp (by decide)
          · rw [shapeSpan] at hbody
            exact shapeSpanGo_covers hloose (ChildOf re.regions i) hsib hkid
              ((re.regions[i]!).hi - ((re.regions[i]!).lo + 1))
              ((re.regions[i]!).lo + 1) ((regionKids re.regions).1[i]!) hfirst
              (by omega) hbody q (by omega) h2
        · obtain ⟨h4, hwhich, hloopop, hlooparg, henterop, henterarg, htailop,
            htailarg, hhead, hbody, hafter, hspan⟩ := shapeRepeat_counted hz hsh
          by_cases hq0 : q = (re.regions[i]!).lo ∨ q = (re.regions[i]!).lo + 1 ∨
              q = (re.regions[i]!).lo + 2 ∨ q = (re.regions[i]!).hi - 1
          · intro hlp
            have hq1 : q = (re.regions[i]!).lo + 1 := by
              rcases hq0 with rfl | h | rfl | rfl
              · rw [hz] at hlp; exact absurd hlp (by decide)
              · exact h
              · rw [henterop] at hlp; exact absurd hlp (by decide)
              · rw [htailop] at hlp; exact absurd hlp (by decide)
            subst hq1
            rw [hlooparg]
            exact ⟨by rw [hbody]; exact henterop, by rw [hbody]; exact henterarg,
              by rw [hafter]; exact htailop, by rw [hafter]; exact htailarg,
              by rw [hafter]; exact hhi⟩
          · simp only [not_or] at hq0
            rw [shapeSpan] at hspan
            exact shapeSpanGo_covers hloose (ChildOf re.regions i) hsib hkid
              ((re.regions[i]!).hi - 1 - ((re.regions[i]!).lo + 3))
              ((re.regions[i]!).lo + 3) ((regionKids re.regions).1[i]!) hfirst
              (by omega) hspan q (by omega) (by omega)
      · have hkind : (re.regions[i]!).kind = .root ∨
            (re.regions[i]!).kind = .group ∨ (re.regions[i]!).kind = .branch := by
          cases hk2 : (re.regions[i]!).kind
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd hk2 hkalt
          · exact absurd hk2 hkrep
        have hspan : shapeSpan re.code re.regions (regionKids re.regions).2
            (re.regions[i]!).lo (re.regions[i]!).hi
            (regionKids re.regions).1[i]! = .crOk := by
          rcases hkind with hk | hk | hk <;> (rw [hk] at hsh; exact hsh)
        rw [shapeSpan] at hspan
        exact shapeSpanGo_covers hloose (ChildOf re.regions i) hsib hkid
          ((re.regions[i]!).hi - (re.regions[i]!).lo) (re.regions[i]!).lo
          ((regionKids re.regions).1[i]!) hfirst (by omega) hspan q h1 h2

/-- And the walk run at the root, whose range is the code. The two hypotheses
beyond the certificate are the pricing's own: no repeat region ends the
program, so a counted repetition's exit is a program point, and the program's
last instruction is an `Accept`, so the root's range is the whole code. -/
theorem rep_header_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size) :
    ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      RepHeader re (re.code[q]!).arg := by
  have hshape := (certCheck_bt_spec hcert).2.2.2.2.1
  obtain ⟨hpos, -, hlo0, hhi0⟩ := certShape_root hshape
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape)
  intro q hq
  exact region_rep_header
    (fun i g1 g2 => (certShape_facts hshape i g1 g2).1)
    (region_lo_le hshape) hends (fun j hj => hsh j (Nat.zero_le _) (by omega))
    re.regions.size 0 (by omega) hpos q (by omega) (by omega)

/-- The account, off an accepted certificate. Three rules the checker does not
have travel as hypotheses, and they are the three THEOREMS.md records: the
program ends in an `Accept`, a `Save`'s slot is below `novec`, and a
repetition's declared bounds fit in a counter. The rest is the certificate's
own, and the per-pass charges are the region tree's. -/
theorem regFlow_of_cert {re : Re} {cert : Cert} {n : Nat}
    {ways chargeW chargeR chargeT : Nat → Nat}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hsave : ∀ q, q < re.code.size → (re.code[q]!).op = .save →
      (re.code[q]!).arg < re.novec)
    (hfits : ∀ a : Nat, a < re.reps.size →
      (re.reps[a]!).lo ≤ none32 ∧ (re.reps[a]!).hi ≤ none32)
    (hcw : ∀ a : Nat, a < re.reps.size → 1 ≤ chargeW a)
    (hct : ∀ a : Nat, a < re.reps.size → 1 ≤ chargeT a)
    (hpassW : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      PassPriced re unitVisitR n ways chargeW q)
    (hpassR : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      PassPriced re unitRecordR n ways chargeR q)
    (hpassT : ∀ q, q < re.code.size → (re.code[q]!).op = .repLoop →
      PassPriced re unitPushR n ways chargeT q) :
    RegFlow re (RepOk re n) (repCost re unitVisitR n ways chargeW)
      (repCost re unitRecordR n ways chargeR)
      (repCost re unitPushR n ways chargeT) n :=
  regFlow_of_repCode (rep_code_ok_of_cert hcert hends hlast)
    (rep_header_of_cert hcert hends) hsave hfits hcw hct hpassW hpassR hpassT

end Pcrevera.Ref
