import Pcrevera.Proofs.RepFlow

/-!
# The region tree, priced by the counted walk (BOUNDS.md section 4.4)

`region_priced` composes a program out of its regions over `flowCost`, a
pricing indexed by the program point alone, and it carries the standing
hypothesis that every repeat region is an optional item. That hypothesis is
about the pricing and not about the tree: a counted repetition's price has to
name the counter, and `flowCost` has nowhere to put it.

`repCost` does. What follows is the same tree induction over it, with the
hypothesis dropped, and it establishes the two things section 4.4 still owed.
The first is `PassPriced` at every head, which is the one clause of the fork
account a single instruction cannot settle — what a pass through a head
charges is what the region tree says the body charges. The second is the root
claim, which is what the three entry-point accounts ask for.

Two numbers per repetition ride along: its ambiguity, which is one number for
the whole of it, and what one pass charges besides the crossings of the
region's end, which is one number per account. They are the checker's own,
read off its walk over the body, and the induction needs them as an equation
rather than as a bound — the head's closed form grows with both, so the
region's claim wants them no larger than the checker said and the head's own
clause wants them no smaller.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## The series, read as a bound -/

/-- More counter values to read is more passes through the head. -/
theorem repSum_mono {w j k : Nat} (h : j ≤ k) : repSum w j ≤ repSum w k := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := Nat.le_zero.mp h
      subst hj
      exact Nat.le_refl _
  | succ k ih =>
      cases j with
      | zero => rw [repSum]; exact Nat.zero_le _
      | succ j =>
          have hj : repSum w (j + 1) = 1 + w * repSum w j := rfl
          have hk : repSum w (k + 1) = 1 + w * repSum w k := rfl
          have hm : w * repSum w j ≤ w * repSum w k :=
            Nat.mul_le_mul_left _ (ih (Nat.le_of_succ_le_succ h))
          omega

/-! ## The walk at one instruction

`repCost_unfold` is one step with the fuel taken out, and what follows is that
step read at each opcode the tree induction meets. The register file moves only
where a repetition opcode writes one, which is why every clause but those is
the same as `flowCost`'s.
-/

/-- A counter read back where a `RepZero` has just written it. Out of range
both the write and the read fall away, and the default a register file reads
past its end is zero, so the clause holds without a size hypothesis. -/
theorem uset!_zero (a : Array UInt32) (i : Nat) : (a.set! i 0)[i]! = 0 := by
  by_cases h : i < a.size
  · exact uset!_self _ _ _ h
  · rw [uset!_out _ _ _ (by omega), getElem!_neg a i (by omega)]
    rfl

/-- An `Accept` costs its own visit and nothing after it. -/
theorem repCost_accept {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hop : (re.code[pc]!).op = .accept) :
    repCost re unit n ways charge pc regs pos = unit (re.code[pc]!) := by
  rw [repCost_unfold hfwd hpc]
  simp only [hop]

/-- A split pays for both of its arms. -/
theorem repCost_split {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hop : (re.code[pc]!).op = .split) :
    repCost re unit n ways charge pc regs pos =
      unit (re.code[pc]!) +
        repCost re unit n ways charge (re.code[pc]!).arg regs pos +
        repCost re unit n ways charge (re.code[pc]!).alt regs pos := by
  rw [repCost_unfold hfwd hpc]
  simp only [hop]

/-- And a jump for its target. -/
theorem repCost_jump {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hop : (re.code[pc]!).op = .jump) :
    repCost re unit n ways charge pc regs pos =
      unit (re.code[pc]!) +
        repCost re unit n ways charge (re.code[pc]!).arg regs pos := by
  rw [repCost_unfold hfwd hpc]
  simp only [hop]

/-- Everything a straight-line range holds itself moves by one and leaves the
register file where it was. -/
theorem repCost_step {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hacc : (re.code[pc]!).op ≠ .accept) (hsp : (re.code[pc]!).op ≠ .split)
    (hjp : (re.code[pc]!).op ≠ .jump)
    (hrep : ¬ ((re.code[pc]!).op = .repZero ∨ (re.code[pc]!).op = .repLoop ∨
      (re.code[pc]!).op = .repEnter ∨ (re.code[pc]!).op = .repNext)) :
    repCost re unit n ways charge pc regs pos =
      unit (re.code[pc]!) + repCost re unit n ways charge (pc + 1) regs pos := by
  simp only [not_or] at hrep
  rw [repCost_unfold hfwd hpc]
  split
  · rename_i h; exact absurd h hacc
  · rename_i h; exact absurd h hsp
  · rename_i h; exact absurd h hjp
  · rename_i h; exact absurd h hrep.1
  · rename_i h; exact absurd h hrep.2.2.1
  · rename_i h; exact absurd h hrep.2.1
  · rename_i h; exact absurd h hrep.2.2.2
  · rfl

/-- The `RepZero` a counted region opens with: its own visit, and the counter
it clears. -/
theorem repCost_repZero {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hop : (re.code[pc]!).op = .repZero) :
    repCost re unit n ways charge pc regs pos =
      unit (re.code[pc]!) +
        repCost re unit n ways charge (pc + 1)
          (regs.set! (repSlot re (re.code[pc]!)) 0) pos := by
  rw [repCost_unfold hfwd hpc]
  simp only [hop]

/-- And the head, which is where the walk stops being a walk. -/
theorem repCost_repLoop {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {pc : Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (hpc : pc < re.code.size)
    (hop : (re.code[pc]!).op = .repLoop) :
    repCost re unit n ways charge pc regs pos =
      repHeadPrice (unit (re.code[pc]!)) (ways (re.code[pc]!).arg)
        (charge (re.code[pc]!).arg)
        (repCost re unit n ways charge (re.reps[(re.code[pc]!).arg]!).after regs
          pos)
        (repK (re.reps[(re.code[pc]!).arg]!) n
          (repCount re (re.code[pc]!) regs) pos) := by
  rw [repCost_unfold hfwd hpc]
  simp only [hop]

/-! ## A straight-line range, priced by a walk that reads the counters

`scanSpanGo_priced` asks for its three per-instruction inequalities at every
point of the range, which is more than a counter-indexed pricing can give: a
child region's own head is inside the range, and what a head costs is a closed
form rather than one visit plus the rest.

The range's *own* instructions are another matter. `scan_span` admits the
loose opcodes, a `Save` and an `Accept` and refuses everything else by name, so
asking for the inequalities only at those three is asking for exactly what the
walk uses.

The other change is that `shape_span` walks alongside. The price walk enters a
child on the cursor alone and never tests where that child ends, so what keeps
a child inside the range is the shape walk's own test, and the two walks are
at the same point and the same cursor throughout.
-/

set_option maxHeartbeats 1000000 in
/-- BOUNDS.md section 4.1 against a pricing that reads the register file: the
flow arriving times what the pricing says at the cursor is covered by what the
walk accumulates plus the flow leaving times what it says at the end.

The register file never appears. It does not have to: a span's own
instructions leave it where it was, so one file can be fixed throughout, and a
child region is met by its claim rather than by the walk. -/
theorem repSpanGo_priced {code : Array Inst} {regions : Array Region}
    {prices : Array Price} {sibs : Array Nat} {hi n : Nat} {W R T : Nat → Nat}
    (hcode : ∀ pc, pc < hi →
      ((code[pc]!).op.loose = true ∨ (code[pc]!).op = .save ∨
        (code[pc]!).op = .accept) →
      (W pc ≤ 1 + W (pc + 1) ∧ R pc ≤ 1 + R (pc + 1) ∧ T pc ≤ T (pc + 1)) ∧
      ((code[pc]!).op ≠ .save → R pc ≤ R (pc + 1)) ∧
      ((code[pc]!).op = .accept → W pc ≤ 1 ∧ R pc = 0 ∧ T pc = 0))
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      (regions[c]!).lo < (regions[c]!).hi → (regions[c]!).hi ≤ hi →
      W (regions[c]!).lo ≤ (prices[c]!).work.val n
          + (prices[c]!).outs.val n * W (regions[c]!).hi ∧
        R (regions[c]!).lo ≤ (prices[c]!).trail.val n
          + (prices[c]!).outs.val n * R (regions[c]!).hi ∧
        T (regions[c]!).lo ≤ (prices[c]!).stack.val n
          + (prices[c]!).outs.val n * T (regions[c]!).hi) :
    ∀ (k pc cursor : Nat), P cursor → hi - pc ≤ k → pc ≤ hi →
      shapeSpanGo code regions sibs hi pc cursor = .crOk →
      ∀ (acc acc' : Acc) (over over' : Bool),
      scanSpanGo code regions prices sibs hi pc cursor acc over =
        (.crOk, acc', over') → over' = false →
      over = false ∧
        acc.work.val n + acc.flow.val n * W pc ≤
          acc'.work.val n + acc'.flow.val n * W hi ∧
        acc.trail.val n + acc.flow.val n * R pc ≤
          acc'.trail.val n + acc'.flow.val n * R hi ∧
        acc.stack.val n + acc.flow.val n * T pc ≤
          acc'.stack.val n + acc'.flow.val n * T hi := by
  intro k
  induction k with
  | zero =>
      intro pc cursor hP hk hle hsh acc acc' over over' h hover
      have hpe : pc = hi := by omega
      subst hpe
      rw [scanSpanGo, dif_neg (by omega)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, hacc, hov⟩ := h
      subst hacc
      subst hov
      exact ⟨hover, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | succ k ih =>
      intro pc cursor hP hk hle hsh acc acc' over over' h hover
      by_cases hpc : pc < hi
      · rw [scanSpanGo, dif_pos hpc] at h
        rw [shapeSpanGo, dif_pos hpc] at hsh
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
          split at h
          · exact absurd h (by simp)
          rename_i hkhi
          dsimp only at h
          rw [if_neg (show ¬((cursor != none32 && (regions[cursor]!).lo < pc) = true) by
              simp [hcond.2]),
            if_pos (show (cursor != none32 && (regions[cursor]!).lo == pc) = true by
              simp [hcond.1, hcond.2]),
            dif_neg hkhi] at hsh
          by_cases hchi : (regions[cursor]!).hi > hi
          · rw [if_pos hchi] at hsh
            exact absurd hsh (by decide)
          rw [if_neg hchi] at hsh
          obtain ⟨hcw, hcr, hct⟩ :=
            hkid cursor hP hcond.1 (by omega) (by omega)
          obtain ⟨hov, hw, hr, ht⟩ :=
            ih (regions[cursor]!).hi (sibs[cursor]!) (hsib cursor hP hcond.1)
              (by omega) (by omega) hsh _ _ _ _ h hover
          dsimp only at hw hr ht
          have f6 := polyMul_snd hov
          have f5 := polyAdd_snd f6
          have f4 := polyMul_snd f5
          have f3 := polyAdd_snd f4
          have f2 := polyMul_snd f3
          have f1 := polyAdd_snd f2
          have vcw := polyMul_eq f1 n
          have vw := polyAdd_le f2 n
          have vcs := polyMul_eq f3 n
          have vs := polyAdd_le f4 n
          have vct := polyMul_eq f5 n
          have vt := polyAdd_le f6 n
          have von := polyMul_eq hov n
          rw [von] at hw hr ht
          refine ⟨polyMul_snd f1, ?_, ?_, ?_⟩
          · have hm : acc.flow.val n * W pc ≤
                acc.flow.val n * (prices[cursor]!).work.val n
                  + acc.flow.val n * (prices[cursor]!).outs.val n *
                    W (regions[cursor]!).hi := by
              have h1 : acc.flow.val n * W pc ≤ acc.flow.val n *
                  ((prices[cursor]!).work.val n + (prices[cursor]!).outs.val n *
                    W (regions[cursor]!).hi) :=
                Nat.mul_le_mul_left _ (by rw [← hcond.2]; exact hcw)
              rw [Nat.mul_add, ← Nat.mul_assoc] at h1
              exact h1
            omega
          · have hm : acc.flow.val n * R pc ≤
                acc.flow.val n * (prices[cursor]!).trail.val n
                  + acc.flow.val n * (prices[cursor]!).outs.val n *
                    R (regions[cursor]!).hi := by
              have h1 : acc.flow.val n * R pc ≤ acc.flow.val n *
                  ((prices[cursor]!).trail.val n + (prices[cursor]!).outs.val n *
                    R (regions[cursor]!).hi) :=
                Nat.mul_le_mul_left _ (by rw [← hcond.2]; exact hcr)
              rw [Nat.mul_add, ← Nat.mul_assoc] at h1
              exact h1
            omega
          · have hm : acc.flow.val n * T pc ≤
                acc.flow.val n * (prices[cursor]!).stack.val n
                  + acc.flow.val n * (prices[cursor]!).outs.val n *
                    T (regions[cursor]!).hi := by
              have h1 : acc.flow.val n * T pc ≤ acc.flow.val n *
                  ((prices[cursor]!).stack.val n + (prices[cursor]!).outs.val n *
                    T (regions[cursor]!).hi) :=
                Nat.mul_le_mul_left _ (by rw [← hcond.2]; exact hct)
              rw [Nat.mul_add, ← Nat.mul_assoc] at h1
              exact h1
            omega
        · rename_i hcond
          dsimp only at h
          by_cases hback : (cursor != none32 && (regions[cursor]!).lo < pc) = true
          · rw [if_pos hback] at hsh
            exact absurd hsh (by decide)
          rw [if_neg hback, if_neg hcond] at hsh
          by_cases hacc : (code[pc]!).op = .accept
          · obtain ⟨⟨hw1, hr1, ht1⟩, hrns, haccv⟩ :=
              hcode pc hpc (Or.inr (Or.inr hacc))
            simp only [hacc] at h hsh
            obtain ⟨hW0, hR0, hT0⟩ := haccv hacc
            obtain ⟨hov, hw, hr, ht⟩ :=
              ih (pc + 1) cursor hP (by omega) (by omega) hsh _ _ _ _ h hover
            dsimp only at hw hr ht
            have hvis := polyAdd_le hov n
            simp only [Poly.val_zero, Nat.zero_mul] at hw hr ht
            refine ⟨polyAdd_snd hov, ?_, ?_, ?_⟩
            · have hm : acc.flow.val n * W pc ≤ acc.flow.val n * 1 :=
                Nat.mul_le_mul_left _ hW0
              rw [Nat.mul_one] at hm
              omega
            · have hm : acc.flow.val n * R pc = 0 := by rw [hR0, Nat.mul_zero]
              omega
            · have hm : acc.flow.val n * T pc = 0 := by rw [hT0, Nat.mul_zero]
              omega
          by_cases hsav : (code[pc]!).op = .save
          · obtain ⟨⟨hw1, hr1, ht1⟩, hrns, haccv⟩ :=
              hcode pc hpc (Or.inr (Or.inl hsav))
            simp only [hsav] at h hsh
            obtain ⟨hov, hw, hr, ht⟩ :=
              ih (pc + 1) cursor hP (by omega) (by omega) hsh _ _ _ _ h hover
            dsimp only at hw hr ht
            have f1 := polyAdd_snd hov
            have hvisw := polyAdd_le f1 n
            have hvist := polyAdd_le hov n
            refine ⟨polyAdd_snd f1, ?_, ?_, ?_⟩
            · have hm : acc.flow.val n * W pc ≤ acc.flow.val n * (1 + W (pc + 1)) :=
                Nat.mul_le_mul_left _ hw1
              rw [Nat.mul_add, Nat.mul_one] at hm
              omega
            · have hm : acc.flow.val n * R pc ≤ acc.flow.val n * (1 + R (pc + 1)) :=
                Nat.mul_le_mul_left _ hr1
              rw [Nat.mul_add, Nat.mul_one] at hm
              omega
            · have hm : acc.flow.val n * T pc ≤ acc.flow.val n * T (pc + 1) :=
                Nat.mul_le_mul_left _ ht1
              omega
          · split at h
            all_goals rename_i hop
            all_goals
              first
                | (simp only [Prod.mk.injEq] at h
                   exact absurd h.1 (by decide))
                | exact absurd hop hacc
                | exact absurd hop hsav
                | (obtain ⟨⟨hw1, hr1, ht1⟩, hrns, haccv⟩ :=
                     hcode pc hpc (Or.inl (by rw [hop]; rfl))
                   simp only [hop] at hsh
                   obtain ⟨hov, hw, hr, ht⟩ :=
                     ih (pc + 1) cursor hP (by omega) (by omega) hsh _ _ _ _ h hover
                   dsimp only at hw hr ht
                   have hvis := polyAdd_le hov n
                   have hrn := hrns hsav
                   refine ⟨polyAdd_snd hov, ?_, ?_, ?_⟩
                   · have hm : acc.flow.val n * W pc ≤
                         acc.flow.val n * (1 + W (pc + 1)) :=
                       Nat.mul_le_mul_left _ hw1
                     rw [Nat.mul_add, Nat.mul_one] at hm
                     omega
                   · have hm : acc.flow.val n * R pc ≤ acc.flow.val n * R (pc + 1) :=
                       Nat.mul_le_mul_left _ hrn
                     omega
                   · have hm : acc.flow.val n * T pc ≤ acc.flow.val n * T (pc + 1) :=
                       Nat.mul_le_mul_left _ ht1
                     omega)
      · have hpe : pc = hi := by omega
        subst hpe
        rw [scanSpanGo, dif_neg hpc] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, hacc, hov⟩ := h
        subst hacc
        subst hov
        exact ⟨hover, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-! ## The three accounts, read off one instruction

The section 3 table again, this time against the counted walk. `unitVisitR`,
`unitRecordR` and `unitPushR` are the three charges and they travel together,
because the two walks below take all three at once.
-/

/-- What a split, a jump and the four repetition opcodes are not. -/
theorem loose_facts {i : Inst} (h : i.op.loose = true) :
    i.op ≠ .split ∧ i.op ≠ .jump ∧
      ¬ (i.op = .repZero ∨ i.op = .repLoop ∨ i.op = .repEnter ∨
        i.op = .repNext) := by
  refine ⟨fun hop => ?_, fun hop => ?_, ?_⟩
  · rw [hop] at h; exact absurd h (by decide)
  · rw [hop] at h; exact absurd h (by decide)
  · rintro (hop | hop | hop | hop) <;> (rw [hop] at h; exact absurd h (by decide))

/-- The three clauses `scanAltGo_priced` asks for at a split. -/
theorem repCost_split_facts {re : Re} {n : Nat}
    {ways chargeW chargeR chargeT : Nat → Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (p : Nat)
    (hop : (re.code[p]!).op = .split) :
    repCost re unitVisitR n ways chargeW p regs pos ≤
        1 + repCost re unitVisitR n ways chargeW (re.code[p]!).arg regs pos
          + repCost re unitVisitR n ways chargeW (re.code[p]!).alt regs pos ∧
      repCost re unitRecordR n ways chargeR p regs pos ≤
        repCost re unitRecordR n ways chargeR (re.code[p]!).arg regs pos
          + repCost re unitRecordR n ways chargeR (re.code[p]!).alt regs pos ∧
      repCost re unitPushR n ways chargeT p regs pos ≤
        1 + repCost re unitPushR n ways chargeT (re.code[p]!).arg regs pos
          + repCost re unitPushR n ways chargeT (re.code[p]!).alt regs pos := by
  have hpc := flowCost_inside hop (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [repCost_split hfwd hpc hop, unitVisitR_eq]
    omega
  · rw [repCost_split hfwd hpc hop,
      unitRecordR_quiet (by rw [hop]; decide) (by rw [hop]; decide)
        (by rw [hop]; decide) (by rw [hop]; decide)]
    omega
  · rw [repCost_split hfwd hpc hop, unitPushR_fork (Or.inl hop)]
    omega

/-- And at a jump. -/
theorem repCost_jump_facts {re : Re} {n : Nat}
    {ways chargeW chargeR chargeT : Nat → Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (p : Nat)
    (hop : (re.code[p]!).op = .jump) :
    repCost re unitVisitR n ways chargeW p regs pos ≤
        1 + repCost re unitVisitR n ways chargeW (re.code[p]!).arg regs pos ∧
      repCost re unitRecordR n ways chargeR p regs pos ≤
        repCost re unitRecordR n ways chargeR (re.code[p]!).arg regs pos ∧
      repCost re unitPushR n ways chargeT p regs pos ≤
        repCost re unitPushR n ways chargeT (re.code[p]!).arg regs pos := by
  have hpc := flowCost_inside hop (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [repCost_jump hfwd hpc hop, unitVisitR_eq]
    omega
  · rw [repCost_jump hfwd hpc hop,
      unitRecordR_quiet (by rw [hop]; decide) (by rw [hop]; decide)
        (by rw [hop]; decide) (by rw [hop]; decide)]
    omega
  · rw [repCost_jump hfwd hpc hop,
      unitPushR_quiet (by rw [hop]; decide) (by rw [hop]; decide)]
    omega

/-- And the ones `repSpanGo_priced` asks for at everything a straight-line
range holds itself: one visit, an undo entry only at a `Save`, no backtrack
entry at all, and an `Accept` that costs its own visit and nothing after
it. -/
theorem repCost_span_facts {re : Re} {n : Nat}
    {ways chargeW chargeR chargeT : Nat → Nat} {regs : Array UInt32} {pos : Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q) (pc : Nat)
    (hpc : pc < re.code.size)
    (hkind : (re.code[pc]!).op.loose = true ∨ (re.code[pc]!).op = .save ∨
      (re.code[pc]!).op = .accept) :
    (repCost re unitVisitR n ways chargeW pc regs pos ≤
          1 + repCost re unitVisitR n ways chargeW (pc + 1) regs pos ∧
        repCost re unitRecordR n ways chargeR pc regs pos ≤
          1 + repCost re unitRecordR n ways chargeR (pc + 1) regs pos ∧
        repCost re unitPushR n ways chargeT pc regs pos ≤
          repCost re unitPushR n ways chargeT (pc + 1) regs pos) ∧
      ((re.code[pc]!).op ≠ .save →
        repCost re unitRecordR n ways chargeR pc regs pos ≤
          repCost re unitRecordR n ways chargeR (pc + 1) regs pos) ∧
      ((re.code[pc]!).op = .accept →
        repCost re unitVisitR n ways chargeW pc regs pos ≤ 1 ∧
          repCost re unitRecordR n ways chargeR pc regs pos = 0 ∧
          repCost re unitPushR n ways chargeT pc regs pos = 0) := by
  by_cases hacc : (re.code[pc]!).op = .accept
  · have hv : repCost re unitVisitR n ways chargeW pc regs pos =
        unitVisitR (re.code[pc]!) := repCost_accept hfwd hpc hacc
    have hr : repCost re unitRecordR n ways chargeR pc regs pos =
        unitRecordR (re.code[pc]!) := repCost_accept hfwd hpc hacc
    have ht : repCost re unitPushR n ways chargeT pc regs pos =
        unitPushR (re.code[pc]!) := repCost_accept hfwd hpc hacc
    rw [unitVisitR_eq] at hv
    rw [unitRecordR_quiet (by rw [hacc]; decide) (by rw [hacc]; decide)
      (by rw [hacc]; decide) (by rw [hacc]; decide)] at hr
    rw [unitPushR_quiet (by rw [hacc]; decide) (by rw [hacc]; decide)] at ht
    exact ⟨⟨by omega, by omega, by omega⟩, fun _ => by omega,
      fun _ => ⟨by omega, hr, ht⟩⟩
  · have hnot : (re.code[pc]!).op ≠ .split ∧ (re.code[pc]!).op ≠ .jump ∧
        ¬ ((re.code[pc]!).op = .repZero ∨ (re.code[pc]!).op = .repLoop ∨
          (re.code[pc]!).op = .repEnter ∨ (re.code[pc]!).op = .repNext) := by
      rcases hkind with hl | hs | ha
      · exact loose_facts hl
      · refine ⟨by rw [hs]; decide, by rw [hs]; decide, ?_⟩
        rintro (hop | hop | hop | hop) <;> (rw [hs] at hop; exact absurd hop (by decide))
      · exact absurd ha hacc
    simp only [not_or] at hnot
    have hv : repCost re unitVisitR n ways chargeW pc regs pos =
        unitVisitR (re.code[pc]!) +
          repCost re unitVisitR n ways chargeW (pc + 1) regs pos :=
      repCost_step hfwd hpc hacc hnot.1 hnot.2.1 (by simp only [not_or]; exact hnot.2.2)
    have hr : repCost re unitRecordR n ways chargeR pc regs pos =
        unitRecordR (re.code[pc]!) +
          repCost re unitRecordR n ways chargeR (pc + 1) regs pos :=
      repCost_step hfwd hpc hacc hnot.1 hnot.2.1 (by simp only [not_or]; exact hnot.2.2)
    have ht : repCost re unitPushR n ways chargeT pc regs pos =
        unitPushR (re.code[pc]!) +
          repCost re unitPushR n ways chargeT (pc + 1) regs pos :=
      repCost_step hfwd hpc hacc hnot.1 hnot.2.1 (by simp only [not_or]; exact hnot.2.2)
    rw [unitVisitR_eq] at hv
    rw [unitPushR_quiet hnot.1 hnot.2.2.2.1] at ht
    have hrle := unitRecordR_le (re.code[pc]!)
    refine ⟨⟨by omega, by omega, by omega⟩, fun hns => ?_, fun hx => absurd hx hacc⟩
    rw [unitRecordR_quiet hns hnot.2.2.1 hnot.2.2.2.2.1 hnot.2.2.2.2.2] at hr
    omega

/-! ## An alternation's range, covered

`shapeAltGo_ok` and `shapeAltGo_rep_ok` are this walk read for one particular
predicate each. What the range holds beyond its branches is one split before
each of them and one jump after, so a predicate that holds of those two and of
every branch's range holds of the whole of it.
-/

/-- The chain walk of `shape_alt`, read as coverage. -/
theorem shapeAltGo_covers {re : Re} {sibs : Array Nat} {hi : Nat}
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

/-! ## What the tree induction carries

Three accounts at once, because the two priced walks take all three together,
and one clause per region plus one clause per head. What a repetition
contributes is read off the checker's walk over its body: its ambiguity, one
number for the whole of it, and what one pass through the head charges besides
the crossings of the region's end, one number per account.

They enter as an equation rather than as a bound. The head's closed form grows
with both of them, so the region's claim wants them no larger than the checker
said and the head's own clause wants them no smaller.
-/

/-- The two numbers section 4.4 reads off a repetition's body, tied to the
walk the checker ran over it. `chargeW`, `chargeR` and `chargeT` are one pass
through the head in the three accounts: the head's own visit, the `RepEnter`,
the body, and one `RepNext` per way the body found to finish. -/
def RepCharges (re : Re) (prices : Array Price) (n : Nat)
    (ways chargeW chargeR chargeT : Nat → Nat) : Prop :=
  ∀ i, i < re.regions.size → (re.regions[i]!).kind = .«repeat» →
    (re.code[(re.regions[i]!).lo]!).op = .repZero →
    ∀ acc : Acc,
      scanSpan re.code re.regions prices (regionKids re.regions).2
          ((re.regions[i]!).lo + 3) ((re.regions[i]!).hi - 1)
          (regionKids re.regions).1[i]! (Acc.fresh (Poly.const 1)) false =
        (.crOk, acc, false) →
      ways (re.code[(re.regions[i]!).lo]!).arg = acc.flow.val n ∧
        chargeW (re.code[(re.regions[i]!).lo]!).arg =
          2 + acc.work.val n + acc.flow.val n ∧
        chargeR (re.code[(re.regions[i]!).lo]!).arg =
          1 + acc.flow.val n + acc.trail.val n ∧
        chargeT (re.code[(re.regions[i]!).lo]!).arg = 1 + acc.stack.val n

/-- One region's claim, read against the counted walk: the pricing where the
region begins is inside the claimed cost plus the claimed ways out times the
pricing where control leaves it.

The register file is universally quantified because a region's claim has to
hold at the file its parent hands in, whatever that file holds. -/
def RepRegionPriced (re : Re) (prices : Array Price) (n : Nat)
    (ways chargeW chargeR chargeT : Nat → Nat) (i : Nat) : Prop :=
  ∀ (regs : Array UInt32) (pos : Nat),
    repCost re unitVisitR n ways chargeW (re.regions[i]!).lo regs pos ≤
        (prices[i]!).work.val n + (prices[i]!).outs.val n *
          repCost re unitVisitR n ways chargeW (re.regions[i]!).hi regs pos ∧
      repCost re unitRecordR n ways chargeR (re.regions[i]!).lo regs pos ≤
        (prices[i]!).trail.val n + (prices[i]!).outs.val n *
          repCost re unitRecordR n ways chargeR (re.regions[i]!).hi regs pos ∧
      repCost re unitPushR n ways chargeT (re.regions[i]!).lo regs pos ≤
        (prices[i]!).stack.val n + (prices[i]!).outs.val n *
          repCost re unitPushR n ways chargeT (re.regions[i]!).hi regs pos

/-- `PassPriced` in the three accounts, which is how a head is carried. -/
def RepPassPriced (re : Re) (n : Nat) (ways chargeW chargeR chargeT : Nat → Nat)
    (q : Nat) : Prop :=
  PassPriced re unitVisitR n ways chargeW q ∧
    PassPriced re unitRecordR n ways chargeR q ∧
    PassPriced re unitPushR n ways chargeT q

/-- A head is priced as soon as its body is: what one pass charges is the two
instructions in front of the body, the body itself, and one `RepNext` per way
the body found to finish. Nothing here knows where the body's bound came
from. -/
theorem passPriced_of_body {re : Re} {unit : Inst → Nat} {n : Nat}
    {ways charge : Nat → Nat} {lo hi r body : Nat}
    (harg : (re.code[lo + 1]!).arg = r) (hafter : (re.reps[r]!).after = hi)
    (hbody : ∀ (regs : Array UInt32) (pos : Nat),
      repCost re unit n ways charge (lo + 3) regs pos ≤
        body + ways r * repCost re unit n ways charge (hi - 1) regs pos)
    (hcharge : unit (re.code[lo + 1]!) + unit (re.code[lo + 2]!) + body +
      ways r * unit (re.code[hi - 1]!) ≤ charge r) :
    PassPriced re unit n ways charge (lo + 1) := by
  intro regs pos
  have h2 : lo + 1 + 1 = lo + 2 := by omega
  have h3 : lo + 1 + 2 = lo + 3 := by omega
  rw [harg, hafter, h2, h3]
  have := hbody regs pos
  omega

/-- The head's closed form against the region's claim, which is BOUNDS.md
section 4.4's arithmetic with the pricing already in closed form. `outside` is
the `RepZero`, charged before the head is reached; `c` is what one pass
charges; and `flow` is the checker's own choice, whose only obligation is to
cover the series. -/
theorem repHeadPrice_dom {u w c X K flow outside claimA claimOuts : Nat}
    (hu : u ≤ c) (hS : repSum w (K + 1) ≤ flow)
    (hclaim : outside + flow * c ≤ claimA)
    (houts : flow * (1 + w) ≤ claimOuts) :
    outside + repHeadPrice u w c X K ≤ claimA + claimOuts * X := by
  have hbase : u + X ≤ c + (1 + w) * X := by
    have h1 : 1 * X ≤ (1 + w) * X := Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 := repLeft_dom (w := w) (k := K) (A := c) (X := X) (base := u + X)
    (flow := flow) hbase hS
  have h3 : flow * (1 + w) * X ≤ claimOuts * X := Nat.mul_le_mul_right _ houts
  unfold repHeadPrice
  omega

set_option maxHeartbeats 1000000 in
/-- The tree induction of BOUNDS.md section 4, over the pricing that names the
counters. It is `region_priced` with the counted arm of `scan_repeat` opened,
and it carries one more clause: every head inside a region's range is priced,
which is the hypothesis the fork account takes and cannot settle on its own.

A straight-line region gets its claim from `repSpanGo_priced`, an alternation
from `scanAltGo_priced`, an optional item from the two of them together, and a
counted repetition from `repHeadPrice_dom` — its `RepZero`, then the closed
form the head reads at the counter that `RepZero` left behind.

The register file is where the counted arm differs from the rest. Pricing the
head writes the region's own counter, and the claim is about the file the
parent handed in, so the two have to be shown to agree: past a repetition's
exit no opcode names it, which is what `hinside` says and what `RegsHere`
turns into an equation. -/
theorem repRegion_priced {re : Re} {prices : Array Price} {n : Nat}
    {ways chargeW chargeR chargeT : Nat → Nat}
    (hfwd : ∀ q, q < re.code.size → RepFwd re q)
    (hinside : ∀ q : Nat, q < re.code.size →
      ((re.code[q]!).op = .repZero ∨ (re.code[q]!).op = .repLoop ∨
        (re.code[q]!).op = .repEnter ∨ (re.code[q]!).op = .repNext) →
      q < (re.reps[(re.code[q]!).arg]!).after)
    (hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i)
    (hin : ∀ i, i < re.regions.size → (re.regions[i]!).hi ≤ re.code.size)
    (hlo : ∀ i, i < re.regions.size → (re.regions[i]!).lo ≤ (re.regions[i]!).hi)
    (hsize : prices.size = re.regions.size)
    (hshape : ∀ j, j < re.regions.size →
      ShapeOk re (regionKids re.regions).1 (regionKids re.regions).2 j)
    (hprice : ∀ j, j < re.regions.size →
      RegionPriced re prices (regionKids re.regions).1 (regionKids re.regions).2 j)
    (hcharges : RepCharges re prices n ways chargeW chargeR chargeT) :
    ∀ (k i : Nat), re.regions.size - i ≤ k → i < re.regions.size →
      RepRegionPriced re prices n ways chargeW chargeR chargeT i ∧
        ∀ q, (re.regions[i]!).lo ≤ q → q < (re.regions[i]!).hi →
          (re.code[q]!).op = .repLoop →
          RepPassPriced re n ways chargeW chargeR chargeT q := by
  intro k
  induction k with
  | zero =>
      intro i hk hi
      omega
  | succ k ih =>
      intro i hk hi
      have hpos : 0 < re.regions.size := by omega
      have hkids : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          RepRegionPriced re prices n ways chargeW chargeR chargeT c ∧
            ∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi →
              (re.code[q]!).op = .repLoop →
              RepPassPriced re n ways chargeW chargeR chargeT q := by
        intro c hP hne
        rcases hP with rfl | ⟨hic, hcs, hpar⟩
        · exact absurd rfl hne
        · exact ih c (by omega) hcs
      have hfirst : ChildOf re.regions i ((regionKids re.regions).1[i]!) :=
        regionKids_first hpos hord i hi
      have hsibs : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ChildOf re.regions i ((regionKids re.regions).2[c]!) :=
        fun c hP hne => regionKids_next hpos hord i c hP hne
      have hlooseq : ∀ q : Nat, (re.code[q]!).op.loose = true →
          ((re.code[q]!).op = .repLoop →
            RepPassPriced re n ways chargeW chargeR chargeT q) := by
        intro q hl hql
        rw [hql] at hl
        exact absurd hl (by decide)
      have hcovkid : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi →
            ((re.code[q]!).op = .repLoop →
              RepPassPriced re n ways chargeW chargeR chargeT q) :=
        fun c hP hne => (hkids c hP hne).2
      have hsh := hshape i hi
      unfold ShapeOk at hsh
      by_cases hkalt : (re.regions[i]!).kind = .alt
      · obtain ⟨acc, hscan, hdw, hdo, hds, hdt⟩ := (hprice i hi).alt hkalt
        rw [hkalt] at hsh
        dsimp only at hsh
        have hfne := shapeAlt_first_ne hsh
        rw [shapeAlt] at hsh
        rw [scanAlt, hsize] at hscan
        constructor
        · intro regs pos
          obtain ⟨-, hrest⟩ :=
            scanAltGo_priced (n := n)
              (W := fun p => repCost re unitVisitR n ways chargeW p regs pos)
              (R := fun p => repCost re unitRecordR n ways chargeR p regs pos)
              (T := fun p => repCost re unitPushR n ways chargeT p regs pos)
              (ChildOf re.regions i) hsibs
              (fun p hop => repCost_split_facts hfwd p hop)
              (fun p hop => repCost_jump_facts hfwd p hop)
              (fun c hP hne => (hkids c hP hne).1 regs pos)
              re.regions.size (re.regions[i]!).lo ((regionKids re.regions).1[i]!) 0
              _ _ _ _ hfirst hsh hscan rfl
          obtain ⟨hw, hr, ht⟩ := hrest hfne
          simp only [Acc.fresh, Poly.val_zero, Nat.zero_mul, Nat.zero_add] at hw hr ht
          have mw := Nat.mul_le_mul_right
            (repCost re unitVisitR n ways chargeW (re.regions[i]!).hi regs pos)
            (polyGe_sound hdo n)
          have mr := Nat.mul_le_mul_right
            (repCost re unitRecordR n ways chargeR (re.regions[i]!).hi regs pos)
            (polyGe_sound hdo n)
          have mt := Nat.mul_le_mul_right
            (repCost re unitPushR n ways chargeT (re.regions[i]!).hi regs pos)
            (polyGe_sound hdo n)
          have dw := polyGe_sound hdw n
          have ds := polyGe_sound hds n
          have dt := polyGe_sound hdt n
          exact ⟨by omega, by omega, by omega⟩
        · intro q h1 h2
          exact shapeAltGo_covers
            (Q := fun q => (re.code[q]!).op = .repLoop →
              RepPassPriced re n ways chargeW chargeR chargeT q)
            (fun p hop hql => by rw [hop] at hql; exact absurd hql (by decide))
            (fun p hop hql => by rw [hop] at hql; exact absurd hql (by decide))
            (ChildOf re.regions i) hsibs
            (fun c hP hne => by
              rcases hP with rfl | ⟨-, hcs, -⟩
              · exact absurd rfl hne
              · exact hlo c hcs)
            hcovkid re.regions.size (re.regions[i]!).lo
            ((regionKids re.regions).1[i]!) 0 hfirst hsh hfne q h1 h2
      by_cases hkrep : (re.regions[i]!).kind = .«repeat»
      · obtain ⟨accR, hscan, hdw, hdo, hds, hdt⟩ := (hprice i hi).rep hkrep
        rw [hkrep] at hsh
        dsimp only at hsh
        rcases shapeRepeat_head hsh with hsp | hz
        · obtain ⟨hlt, harg, hspshape⟩ := shapeRepeat_opt hsp hsh
          obtain ⟨a, hspan, vw, vs, vt, vf⟩ := scanRepeat_opt (n := n) hsp hscan rfl
          rw [shapeSpan] at hspshape
          rw [scanSpan] at hspan
          constructor
          · intro regs pos
            obtain ⟨-, hw, hr, ht⟩ :=
              repSpanGo_priced (n := n)
                (W := fun p => repCost re unitVisitR n ways chargeW p regs pos)
                (R := fun p => repCost re unitRecordR n ways chargeR p regs pos)
                (T := fun p => repCost re unitPushR n ways chargeT p regs pos)
                (fun pc hpc hk2 =>
                  repCost_span_facts hfwd pc (by have := hin i hi; omega) hk2)
                (ChildOf re.regions i) hsibs
                (fun c hP hne _ _ => (hkids c hP hne).1 regs pos)
                ((re.regions[i]!).hi - ((re.regions[i]!).lo + 1))
                ((re.regions[i]!).lo + 1) ((regionKids re.regions).1[i]!) hfirst
                (by omega) (by omega) hspshape _ _ _ _ hspan rfl
            simp only [Acc.fresh, Poly.val_zero, Poly.val_const, Nat.one_mul,
              Nat.zero_add] at hw hr ht
            obtain ⟨sw, sr, st⟩ :=
              repCost_split_facts (n := n) (ways := ways) (chargeW := chargeW)
                (chargeR := chargeR) (chargeT := chargeT) (regs := regs) (pos := pos)
                hfwd (re.regions[i]!).lo hsp
            have dw := polyGe_sound hdw n
            have dov := polyGe_sound hdo n
            have ds := polyGe_sound hds n
            have dt := polyGe_sound hdt n
            rw [vt] at dt
            have mw : (a.flow.val n + 1) *
                repCost re unitVisitR n ways chargeW (re.regions[i]!).hi regs pos ≤
                (prices[i]!).outs.val n *
                  repCost re unitVisitR n ways chargeW (re.regions[i]!).hi regs pos :=
              Nat.mul_le_mul_right _ (by omega)
            have mr : (a.flow.val n + 1) *
                repCost re unitRecordR n ways chargeR (re.regions[i]!).hi regs pos ≤
                (prices[i]!).outs.val n *
                  repCost re unitRecordR n ways chargeR (re.regions[i]!).hi regs pos :=
              Nat.mul_le_mul_right _ (by omega)
            have mt : (a.flow.val n + 1) *
                repCost re unitPushR n ways chargeT (re.regions[i]!).hi regs pos ≤
                (prices[i]!).outs.val n *
                  repCost re unitPushR n ways chargeT (re.regions[i]!).hi regs pos :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.add_mul, Nat.one_mul] at mw mr mt
            rcases harg with ⟨ha, hb⟩ | ⟨ha, hb⟩
            all_goals rw [ha, hb] at sw sr st
            all_goals exact ⟨by omega, by omega, by omega⟩
          · intro q h1 h2
            by_cases hq0 : q = (re.regions[i]!).lo
            · intro hql
              rw [hq0, hsp] at hql
              exact absurd hql (by decide)
            · exact shapeSpanGo_covers
                (Q := fun q => (re.code[q]!).op = .repLoop →
                  RepPassPriced re n ways chargeW chargeR chargeT q)
                hlooseq (ChildOf re.regions i) hsibs hcovkid
                ((re.regions[i]!).hi - ((re.regions[i]!).lo + 1))
                ((re.regions[i]!).lo + 1) ((regionKids re.regions).1[i]!) hfirst
                (by omega) hspshape q (by omega) h2
        · obtain ⟨h4, hwhich, hloopop, hlooparg, henterop, henterarg, htailop,
            htailarg, hheadeq, hbodyeq, hafter, hspshape⟩ := shapeRepeat_counted hz hsh
          obtain ⟨acc, w, flow, -, -, hspan, hways, hSflow, hcw, hcs, hct, hcf⟩ :=
            scanRepeat_counted (n := n) hz hscan rfl
          obtain ⟨e1, e2, e3, e4⟩ := hcharges i hi hkrep hz acc hspan
          rw [hways] at e1 e2 e3
          rw [shapeSpan] at hspshape
          rw [scanSpan] at hspan
          have hhicode : (re.regions[i]!).hi ≤ re.code.size := hin i hi
          have hlocode : (re.regions[i]!).lo < re.code.size := by omega
          have ur0 : unitRecordR (re.code[(re.regions[i]!).lo]!) = 1 :=
            unitRecordR_write (Or.inr (Or.inl hz))
          have ur1 : unitRecordR (re.code[(re.regions[i]!).lo + 1]!) = 0 :=
            unitRecordR_quiet (by rw [hloopop]; decide) (by rw [hloopop]; decide)
              (by rw [hloopop]; decide) (by rw [hloopop]; decide)
          have ur2 : unitRecordR (re.code[(re.regions[i]!).lo + 2]!) = 1 :=
            unitRecordR_write (Or.inr (Or.inr (Or.inl henterop)))
          have ur3 : unitRecordR (re.code[(re.regions[i]!).hi - 1]!) = 1 :=
            unitRecordR_write (Or.inr (Or.inr (Or.inr htailop)))
          have up0 : unitPushR (re.code[(re.regions[i]!).lo]!) = 0 :=
            unitPushR_quiet (by rw [hz]; decide) (by rw [hz]; decide)
          have up1 : unitPushR (re.code[(re.regions[i]!).lo + 1]!) = 1 :=
            unitPushR_fork (Or.inr hloopop)
          have up2 : unitPushR (re.code[(re.regions[i]!).lo + 2]!) = 0 :=
            unitPushR_quiet (by rw [henterop]; decide) (by rw [henterop]; decide)
          have up3 : unitPushR (re.code[(re.regions[i]!).hi - 1]!) = 0 :=
            unitPushR_quiet (by rw [htailop]; decide) (by rw [htailop]; decide)
          have hbody : ∀ (regs : Array UInt32) (pos : Nat),
              repCost re unitVisitR n ways chargeW ((re.regions[i]!).lo + 3) regs pos ≤
                  acc.work.val n + w * repCost re unitVisitR n ways chargeW
                    ((re.regions[i]!).hi - 1) regs pos ∧
                repCost re unitRecordR n ways chargeR ((re.regions[i]!).lo + 3) regs pos ≤
                  acc.trail.val n + w * repCost re unitRecordR n ways chargeR
                    ((re.regions[i]!).hi - 1) regs pos ∧
                repCost re unitPushR n ways chargeT ((re.regions[i]!).lo + 3) regs pos ≤
                  acc.stack.val n + w * repCost re unitPushR n ways chargeT
                    ((re.regions[i]!).hi - 1) regs pos := by
            intro regs pos
            obtain ⟨-, bw, br, bt⟩ :=
              repSpanGo_priced (n := n)
                (W := fun p => repCost re unitVisitR n ways chargeW p regs pos)
                (R := fun p => repCost re unitRecordR n ways chargeR p regs pos)
                (T := fun p => repCost re unitPushR n ways chargeT p regs pos)
                (fun pc hpc hk2 =>
                  repCost_span_facts hfwd pc (by have := hin i hi; omega) hk2)
                (ChildOf re.regions i) hsibs
                (fun c hP hne _ _ => (hkids c hP hne).1 regs pos)
                ((re.regions[i]!).hi - 1 - ((re.regions[i]!).lo + 3))
                ((re.regions[i]!).lo + 3) ((regionKids re.regions).1[i]!) hfirst
                (by omega) (by omega) hspshape _ _ _ _ hspan rfl
            simp only [Acc.fresh, Poly.val_zero, Poly.val_const, Nat.one_mul,
              Nat.zero_add] at bw br bt
            rw [hways] at bw br bt
            exact ⟨bw, br, bt⟩
          have hpass : RepPassPriced re n ways chargeW chargeR chargeT
              ((re.regions[i]!).lo + 1) := by
            refine ⟨?_, ?_, ?_⟩
            · refine passPriced_of_body (body := acc.work.val n) hlooparg hafter
                (fun regs pos => by rw [e1]; exact (hbody regs pos).1) ?_
              rw [e1, e2]
              simp only [unitVisitR_eq]
              omega
            · refine passPriced_of_body (body := acc.trail.val n) hlooparg hafter
                (fun regs pos => by rw [e1]; exact (hbody regs pos).2.1) ?_
              rw [e1, e3, ur1, ur2, ur3]
              omega
            · refine passPriced_of_body (body := acc.stack.val n) hlooparg hafter
                (fun regs pos => by rw [e1]; exact (hbody regs pos).2.2) ?_
              rw [e1, e4, up1, up2, up3]
              omega
          constructor
          · intro regs pos
            have hslot : repSlot re (re.code[(re.regions[i]!).lo + 1]!) =
                repSlot re (re.code[(re.regions[i]!).lo]!) := by
              simp only [repSlot, hlooparg]
            have hcount : repCount re (re.code[(re.regions[i]!).lo + 1]!)
                (regs.set! (repSlot re (re.code[(re.regions[i]!).lo]!)) 0) = 0 := by
              simp only [repCount, hslot, uset!_zero]
              rfl
            have hregshere : RegsHere re
                (regs.set! (repSlot re (re.code[(re.regions[i]!).lo]!)) 0) regs
                (re.regions[i]!).hi := by
              refine ⟨uset!_size _ _ _, ?_⟩
              intro q hq hqc hop
              have hne : (re.code[q]!).arg ≠ (re.code[(re.regions[i]!).lo]!).arg := by
                intro heq
                have hq2 := hinside q hqc hop
                rw [heq, hafter] at hq2
                omega
              exact ⟨Array.getElem!_set!_ne _ _ _ _ (by simp only [repSlot]; omega),
                Array.getElem!_set!_ne _ _ _ _ (by simp only [repSlot]; omega)⟩
            have hlocal : ∀ (unit : Inst → Nat) (charge : Nat → Nat),
                repCost re unit n ways charge (re.regions[i]!).hi
                    (regs.set! (repSlot re (re.code[(re.regions[i]!).lo]!)) 0) pos =
                  repCost re unit n ways charge (re.regions[i]!).hi regs pos := by
              intro unit charge
              unfold repCost
              exact repCostAt_local hfwd _ _ _ _ _ hregshere
            have hstep : ∀ (unit : Inst → Nat) (charge : Nat → Nat),
                repCost re unit n ways charge (re.regions[i]!).lo regs pos =
                  unit (re.code[(re.regions[i]!).lo]!) +
                    repHeadPrice (unit (re.code[(re.regions[i]!).lo + 1]!)) w
                      (charge (re.code[(re.regions[i]!).lo]!).arg)
                      (repCost re unit n ways charge (re.regions[i]!).hi regs pos)
                      (repK (re.reps[(re.code[(re.regions[i]!).lo]!).arg]!) n 0
                        pos) := by
              intro unit charge
              rw [repCost_repZero hfwd hlocode hz,
                repCost_repLoop hfwd (by omega) hloopop, hcount, hlooparg, hafter,
                e1, hlocal unit charge]
            have hSK : repSum w
                (repK (re.reps[(re.code[(re.regions[i]!).lo]!).arg]!) n 0 pos + 1) ≤
                flow :=
              Nat.le_trans (repSum_mono (repK_zero_le n pos)) hSflow
            have dw := polyGe_sound hdw n
            have dov := polyGe_sound hdo n
            have ds := polyGe_sound hds n
            have dt := polyGe_sound hdt n
            refine ⟨?_, ?_, ?_⟩
            · rw [hstep unitVisitR chargeW]
              exact repHeadPrice_dom (by rw [unitVisitR_eq, e2]; omega) hSK
                (by rw [unitVisitR_eq, e2]; omega) (by omega)
            · rw [hstep unitRecordR chargeR]
              exact repHeadPrice_dom (by rw [ur1]; omega) hSK
                (by rw [ur0, e3]; omega) (by omega)
            · rw [hstep unitPushR chargeT]
              exact repHeadPrice_dom (by rw [up1, e4]; omega) hSK
                (by rw [up0, e4]; omega) (by omega)
          · intro q h1 h2
            by_cases hq0 : q = (re.regions[i]!).lo
            · intro hql
              rw [hq0, hz] at hql
              exact absurd hql (by decide)
            by_cases hq1 : q = (re.regions[i]!).lo + 1
            · intro _
              rw [hq1]
              exact hpass
            by_cases hq2 : q = (re.regions[i]!).lo + 2
            · intro hql
              rw [hq2, henterop] at hql
              exact absurd hql (by decide)
            by_cases hq3 : q = (re.regions[i]!).hi - 1
            · intro hql
              rw [hq3, htailop] at hql
              exact absurd hql (by decide)
            · exact shapeSpanGo_covers
                (Q := fun q => (re.code[q]!).op = .repLoop →
                  RepPassPriced re n ways chargeW chargeR chargeT q)
                hlooseq (ChildOf re.regions i) hsibs hcovkid
                ((re.regions[i]!).hi - 1 - ((re.regions[i]!).lo + 3))
                ((re.regions[i]!).lo + 3) ((regionKids re.regions).1[i]!) hfirst
                (by omega) hspshape q (by omega) (by omega)
      · have hkind : (re.regions[i]!).kind = .root ∨
            (re.regions[i]!).kind = .group ∨ (re.regions[i]!).kind = .branch := by
          cases hk2 : (re.regions[i]!).kind
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd hk2 hkalt
          · exact absurd hk2 hkrep
        obtain ⟨acc, hscan, hdw, hdo, hds, hdt⟩ := (hprice i hi).span hkind
        have hspshape : shapeSpan re.code re.regions (regionKids re.regions).2
            (re.regions[i]!).lo (re.regions[i]!).hi
            (regionKids re.regions).1[i]! = .crOk := by
          rcases hkind with hk2 | hk2 | hk2 <;> (rw [hk2] at hsh; exact hsh)
        rw [shapeSpan] at hspshape
        rw [scanSpan] at hscan
        constructor
        · intro regs pos
          obtain ⟨-, hw, hr, ht⟩ :=
            repSpanGo_priced (n := n)
              (W := fun p => repCost re unitVisitR n ways chargeW p regs pos)
              (R := fun p => repCost re unitRecordR n ways chargeR p regs pos)
              (T := fun p => repCost re unitPushR n ways chargeT p regs pos)
              (fun pc hpc hk2 =>
                repCost_span_facts hfwd pc (by have := hin i hi; omega) hk2)
              (ChildOf re.regions i) hsibs
              (fun c hP hne _ _ => (hkids c hP hne).1 regs pos)
              ((re.regions[i]!).hi - (re.regions[i]!).lo) (re.regions[i]!).lo
              ((regionKids re.regions).1[i]!) hfirst (by omega) (hlo i hi)
              hspshape _ _ _ _ hscan rfl
          simp only [Acc.fresh, Poly.val_zero, Poly.val_const, Nat.one_mul,
            Nat.zero_add] at hw hr ht
          have mw := Nat.mul_le_mul_right
            (repCost re unitVisitR n ways chargeW (re.regions[i]!).hi regs pos)
            (polyGe_sound hdo n)
          have mr := Nat.mul_le_mul_right
            (repCost re unitRecordR n ways chargeR (re.regions[i]!).hi regs pos)
            (polyGe_sound hdo n)
          have mt := Nat.mul_le_mul_right
            (repCost re unitPushR n ways chargeT (re.regions[i]!).hi regs pos)
            (polyGe_sound hdo n)
          have dw := polyGe_sound hdw n
          have ds := polyGe_sound hds n
          have dt := polyGe_sound hdt n
          exact ⟨by omega, by omega, by omega⟩
        · intro q h1 h2
          exact shapeSpanGo_covers
            (Q := fun q => (re.code[q]!).op = .repLoop →
              RepPassPriced re n ways chargeW chargeR chargeT q)
            hlooseq (ChildOf re.regions i) hsibs hcovkid
            ((re.regions[i]!).hi - (re.regions[i]!).lo) (re.regions[i]!).lo
            ((regionKids re.regions).1[i]!) hfirst (by omega) hspshape q h1 h2

/-! ## The whole program

The tree induction run at the root, whose range is the code. Past the end of
the program there is nothing left to charge, so the root's claim comes out
bounding the pricing at the entry point, and every head of the program is
priced along the way.
-/

/-- BOUNDS.md section 4 at the entry point, over the pricing that names the
counters: one entry into the program visits at most the root region's claimed
`work`, records at most the certificate's `trail` and never pushes past its
`stack` — and every head is priced, which is what the fork account still owed.

Beyond an accepted certificate this asks for the two things the forward
pricing asks for as well: the program ends in an `Accept`, and no alternation
and no repeat region ends it. The hypothesis that every repeat region is an
optional item is gone; what replaces it is `hcharges`, which names the
checker's own two numbers per repetition. -/
theorem rep_cert_priced {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (n : Nat)
    {ways chargeW chargeR chargeT : Nat → Nat}
    (hcharges : RepCharges re cert.prices n ways chargeW chargeR chargeT) :
    (∀ (regs : Array UInt32) (pos : Nat),
        repCost re unitVisitR n ways chargeW 0 regs pos ≤
            (cert.prices[0]!).work.val n ∧
          repCost re unitRecordR n ways chargeR 0 regs pos ≤ cert.trail.val n ∧
          repCost re unitPushR n ways chargeT 0 regs pos ≤ cert.stack.val n) ∧
      ∀ q : Nat, (re.code[q]!).op = .repLoop →
        RepPassPriced re n ways chargeW chargeR chargeT q := by
  obtain ⟨-, -, hsize, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨hpos, -, hlo0, hhi0⟩ := certShape_root hshape
  obtain ⟨hstc, htrc⟩ := certCheck_bt_claims hcert
  have hpr := certCheckRegions_all re.regions.size 0 over hregions
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape)
  obtain ⟨hclaim, hheads⟩ :=
    repRegion_priced (n := n) (rep_fwd_of_cert hcert hends hlast)
      (fun q hq hop => (rep_inside_of_cert hcert hends hlast q hq hop).2.2)
      (fun i h1 h2 => (certShape_facts hshape i h1 h2).1)
      (fun i hi => region_hi_le hshape i i (Nat.le_refl _) hi)
      (region_lo_le hshape) hsize
      (fun j hj => hsh j (Nat.zero_le _) (by omega))
      (fun j hj => hpr j (Nat.zero_le _) (by omega)) hcharges
      re.regions.size 0 (by omega) hpos
  refine ⟨fun regs pos => ?_, fun q hop => ?_⟩
  · obtain ⟨hw, hr, ht⟩ := hclaim regs pos
    have h0v : repCost re unitVisitR n ways chargeW re.code.size regs pos = 0 :=
      repCost_out (Nat.le_refl _)
    have h0r : repCost re unitRecordR n ways chargeR re.code.size regs pos = 0 :=
      repCost_out (Nat.le_refl _)
    have h0t : repCost re unitPushR n ways chargeT re.code.size regs pos = 0 :=
      repCost_out (Nat.le_refl _)
    rw [hlo0, hhi0, h0v, Nat.mul_zero, Nat.add_zero] at hw
    rw [hlo0, hhi0, h0r, Nat.mul_zero, Nat.add_zero] at hr
    rw [hlo0, hhi0, h0t, Nat.mul_zero, Nat.add_zero] at ht
    rw [htrc, hstc]
    exact ⟨hw, hr, ht⟩
  · have hq := flowCost_inside hop (by decide)
    exact hheads q (by omega) (by omega) hop

/-! ## Where the two numbers come from

`scanRepeat_counted` states a repetition's ambiguity and its per-pass charge
existentially, one repeat region at a time, and `RepCharges` wants them as
functions of the repetition index. Turning the one into the other is a choice,
and the choice is only well posed if a repetition index reaches one region.

`cert_shape` does enforce that — a second repeat region over the same range
would be met by its parent's span walk as a child starting before the range
the walk had reached, which is `crShape` — but that argument is about the walk
rather than about one region, and it is not carried out here. It enters as
`honce` instead, and `counted_regions_agree` is the part of it the shape check
already hands over: two counted repeat regions naming one repetition have the
same range.
-/

open Classical in
/-- The body span's accumulator, chosen for a repetition index. Out of the
tree the value is not used and the choice falls back on a blank. -/
noncomputable def repBodyAcc (re : Re) (prices : Array Price) (r : Nat) : Acc :=
  if h : ∃ a : Acc, ∃ i : Nat, i < re.regions.size ∧
      (re.regions[i]!).kind = .«repeat» ∧
      (re.code[(re.regions[i]!).lo]!).op = .repZero ∧
      (re.code[(re.regions[i]!).lo]!).arg = r ∧
      scanSpan re.code re.regions prices (regionKids re.regions).2
          ((re.regions[i]!).lo + 3) ((re.regions[i]!).hi - 1)
          (regionKids re.regions).1[i]! (Acc.fresh (Poly.const 1)) false =
        (.crOk, a, false)
    then h.choose
    else Acc.fresh Poly.zero

/-- A repetition's ambiguity: what one iteration hands the next. -/
noncomputable def repWays (re : Re) (prices : Array Price) (n r : Nat) : Nat :=
  (repBodyAcc re prices r).flow.val n

/-- And what one pass through its head charges in the three accounts: the
head's own visit, the `RepEnter`, the body, and one `RepNext` per way the body
found to finish. -/
noncomputable def repChargeW (re : Re) (prices : Array Price) (n r : Nat) : Nat :=
  2 + (repBodyAcc re prices r).work.val n + (repBodyAcc re prices r).flow.val n

noncomputable def repChargeR (re : Re) (prices : Array Price) (n r : Nat) : Nat :=
  1 + (repBodyAcc re prices r).flow.val n + (repBodyAcc re prices r).trail.val n

noncomputable def repChargeT (re : Re) (prices : Array Price) (n r : Nat) : Nat :=
  1 + (repBodyAcc re prices r).stack.val n

/-- And they are the checker's own numbers, as long as a repetition index
reaches one repeat region. -/
theorem repCharges_choose {re : Re} {prices : Array Price} (n : Nat)
    (honce : ∀ i i' : Nat, i < re.regions.size → i' < re.regions.size →
      (re.regions[i]!).kind = .«repeat» → (re.regions[i']!).kind = .«repeat» →
      (re.code[(re.regions[i]!).lo]!).op = .repZero →
      (re.code[(re.regions[i']!).lo]!).op = .repZero →
      (re.code[(re.regions[i']!).lo]!).arg = (re.code[(re.regions[i]!).lo]!).arg →
      i = i') :
    RepCharges re prices n (repWays re prices n) (repChargeW re prices n)
      (repChargeR re prices n) (repChargeT re prices n) := by
  intro i hi hkind hz acc hspan
  have hex : ∃ a : Acc, ∃ i' : Nat, i' < re.regions.size ∧
      (re.regions[i']!).kind = .«repeat» ∧
      (re.code[(re.regions[i']!).lo]!).op = .repZero ∧
      (re.code[(re.regions[i']!).lo]!).arg = (re.code[(re.regions[i]!).lo]!).arg ∧
      scanSpan re.code re.regions prices (regionKids re.regions).2
          ((re.regions[i']!).lo + 3) ((re.regions[i']!).hi - 1)
          (regionKids re.regions).1[i']! (Acc.fresh (Poly.const 1)) false =
        (.crOk, a, false) :=
    ⟨acc, i, hi, hkind, hz, rfl, hspan⟩
  have hpick : repBodyAcc re prices (re.code[(re.regions[i]!).lo]!).arg =
      hex.choose := by
    unfold repBodyAcc
    rw [dif_pos hex]
  obtain ⟨i', hi', hkind', hz', harg', hspan'⟩ := hex.choose_spec
  have hii : i = i' := honce i i' hi hi' hkind hkind' hz hz' harg'
  subst hii
  rw [hspan] at hspan'
  simp only [Prod.mk.injEq] at hspan'
  have hacc : hex.choose = acc := hspan'.2.1.symm
  simp only [repWays, repChargeW, repChargeR, repChargeT, hpick, hacc, and_self]

/-- The per-pass charge covers the head's own visit, at every repetition index
and in all three accounts. `repCostAt_mono_pos` asks for exactly this, at a
`RepLoop` and at the head a `RepNext` names, and the chosen charges pay it
outright: a repetition index the tree never names falls back on a blank body,
which still charges the head. -/
theorem repCharge_covers (re : Re) (prices : Array Price) (n r : Nat)
    {i : Inst} (hop : i.op = .repLoop) :
    unitVisitR i ≤ repChargeW re prices n r ∧
      unitRecordR i ≤ repChargeR re prices n r ∧
      unitPushR i ≤ repChargeT re prices n r := by
  refine ⟨?_, ?_, ?_⟩
  · rw [unitVisitR_eq, repChargeW]
    omega
  · rw [unitRecordR_quiet (by rw [hop]; decide) (by rw [hop]; decide)
      (by rw [hop]; decide) (by rw [hop]; decide)]
    omega
  · rw [unitPushR_fork (Or.inr hop), repChargeT]
    omega

/-- Section 4.4's two halves, joined at the chosen numbers: every head of the
program is priced, and one entry into it is inside the root region's claim. -/
theorem rep_cert_priced_choose {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (honce : ∀ i i' : Nat, i < re.regions.size → i' < re.regions.size →
      (re.regions[i]!).kind = .«repeat» → (re.regions[i']!).kind = .«repeat» →
      (re.code[(re.regions[i]!).lo]!).op = .repZero →
      (re.code[(re.regions[i']!).lo]!).op = .repZero →
      (re.code[(re.regions[i']!).lo]!).arg = (re.code[(re.regions[i]!).lo]!).arg →
      i = i') (n : Nat) :
    (∀ (regs : Array UInt32) (pos : Nat),
        repCost re unitVisitR n (repWays re cert.prices n)
            (repChargeW re cert.prices n) 0 regs pos ≤
            (cert.prices[0]!).work.val n ∧
          repCost re unitRecordR n (repWays re cert.prices n)
            (repChargeR re cert.prices n) 0 regs pos ≤ cert.trail.val n ∧
          repCost re unitPushR n (repWays re cert.prices n)
            (repChargeT re cert.prices n) 0 regs pos ≤ cert.stack.val n) ∧
      ∀ q : Nat, (re.code[q]!).op = .repLoop →
        RepPassPriced re n (repWays re cert.prices n) (repChargeW re cert.prices n)
          (repChargeR re cert.prices n) (repChargeT re cert.prices n) q :=
  rep_cert_priced hcert hends hlast n (repCharges_choose n honce)

end Pcrevera.Ref
