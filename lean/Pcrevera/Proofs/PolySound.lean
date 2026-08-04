import Pcrevera.Proofs.CtxReserve

/-!
# What a bound is worth (BOUNDS.md section 2, read as arithmetic)

A `Poly` claims a number for every subject length: `base^n` times its
polynomial in `n + 1`. This file writes that number down — `Poly.val` — and
then holds each operation of the certificate algebra against it.
Normalization keeps the value, dominance and equality mean what they say
pointwise, and addition and multiplication with a clean overflow flag
compute a value that is at least (for `polyAdd`, which keeps the larger
base) or exactly (for `polyMul`) the value of the inputs. Evaluation is the
end of the story: `polyValue` either answers the value itself or refuses,
and a refusal really does mean the value passed the counter cap.

These are the arithmetic facts the layer A checker-soundness theorems
(R-6 through R-8 in THEOREMS.md) compose over; nothing here knows about
patterns or programs, only about `Poly` and the counters.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- The polynomial part of a bound at length `n`: its coefficients spent on
the powers of `n + 1`. -/
def Poly.part (p : Poly) (n : Nat) : Nat :=
  p.c0 + p.c1 * (n + 1) + p.c2 * (n + 1) ^ 2 + p.c3 * (n + 1) ^ 3 +
    p.c4 * (n + 1) ^ 4

/-- The number a bound stands for at subject length `n` — the mathematical
reading of BOUNDS.md section 2, with none of the counter arithmetic. -/
def Poly.val (p : Poly) (n : Nat) : Nat :=
  p.base ^ n * p.part n

/-- `nothing` spelled out: all five coefficients are zero. -/
theorem nothing_iff {p : Poly} :
    p.nothing = true ↔
      p.c0 = 0 ∧ p.c1 = 0 ∧ p.c2 = 0 ∧ p.c3 = 0 ∧ p.c4 = 0 := by
  simp [Poly.nothing, and_assoc]

/-- Normalization keeps the value: a bound worth nothing is worth nothing
at base one too. -/
theorem val_norm (p : Poly) (n : Nat) : (polyNorm p).val n = p.val n := by
  unfold polyNorm
  split
  · rename_i h
    obtain ⟨h0, h1, h2, h3, h4⟩ := nothing_iff.mp h
    simp [Poly.val, Poly.part, Poly.zero, h0, h1, h2, h3, h4]
  · rfl

/-- Raising the base or any coefficient never lowers the value: every
basis function `base^n * (n + 1)^d` is nonnegative and grows with its
base. -/
theorem val_mono {p q : Poly} (hbase : p.base ≤ q.base)
    (hcoef : ∀ i, p.coef i ≤ q.coef i) (n : Nat) : p.val n ≤ q.val n := by
  have h1 : p.c1 ≤ q.c1 := hcoef 1
  have h2 : p.c2 ≤ q.c2 := hcoef 2
  have h3 : p.c3 ≤ q.c3 := hcoef 3
  have h4 : p.c4 ≤ q.c4 := hcoef 4
  refine Nat.mul_le_mul (Nat.pow_le_pow_left hbase n) ?_
  have h0 : p.c0 ≤ q.c0 := hcoef 0
  have t1 : p.c1 * (n + 1) ≤ q.c1 * (n + 1) := Nat.mul_le_mul_right _ h1
  have t2 : p.c2 * (n + 1) ^ 2 ≤ q.c2 * (n + 1) ^ 2 := Nat.mul_le_mul_right _ h2
  have t3 : p.c3 * (n + 1) ^ 3 ≤ q.c3 * (n + 1) ^ 3 := Nat.mul_le_mul_right _ h3
  have t4 : p.c4 * (n + 1) ^ 4 ≤ q.c4 * (n + 1) ^ 4 := Nat.mul_le_mul_right _ h4
  simp only [Poly.part]
  omega

/-- `polyGe` is sound: coefficientwise dominance with base dominance puts
the claimed value at or above the required one at every length. -/
theorem polyGe_sound {a b : Poly} (h : polyGe a b = true) (n : Nat) :
    b.val n ≤ a.val n := by
  unfold polyGe at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h1 h2 h3 h4 h5 h6
  refine val_mono (Nat.le_of_not_lt h1) ?_ n
  intro i
  rcases i with _ | _ | _ | _ | i
  · exact Nat.le_of_not_lt h2
  · exact Nat.le_of_not_lt h3
  · exact Nat.le_of_not_lt h4
  · exact Nat.le_of_not_lt h5
  · exact Nat.le_of_not_lt h6

/-- `polyEq` really is structural equality. -/
theorem polyEq_eq {a b : Poly} (h : polyEq a b = true) : a = b := by
  unfold polyEq at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h1 h2 h3 h4 h5 h6
  obtain ⟨ab, a0, a1, a2, a3, a4⟩ := a
  obtain ⟨bb, b0, b1, b2, b3, b4⟩ := b
  simp only [Poly.mk.injEq]
  simp only at h1 h2 h3 h4 h5 h6
  omega

/-- `polyEq` is sound: equal bounds are worth the same at every length. -/
theorem polyEq_sound {a b : Poly} (h : polyEq a b = true) (n : Nat) :
    a.val n = b.val n := by
  rw [polyEq_eq h]

/-- Under the cap, `satAdd` is plain addition and keeps its flag. -/
theorem satAdd_of_le {a b : Nat} (over : Bool) (h : a + b ≤ counterMax) :
    satAdd a b over = (a + b, over) := by
  unfold satAdd
  rw [if_neg (by omega)]

/-- Under the cap, `satMul` is plain multiplication and keeps its flag. -/
theorem satMul_of_le {a b : Nat} (over : Bool) (h : a * b ≤ counterMax) :
    satMul a b over = (a * b, over) := by
  unfold satMul
  split
  · rename_i hz
    rcases hz with hz | hz <;> simp [hz]
  · rename_i hz
    rw [not_or] at hz
    rw [if_neg]
    exact Nat.not_lt.mpr ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hz.2)).mpr h)

/-- `polyAdd` with a clean flag over-approximates the sum: the coefficients
added exactly, under the larger of the two bases. -/
theorem polyAdd_sound {a b c : Poly} {over : Bool}
    (h : polyAdd a b over = (c, false)) (n : Nat) :
    a.val n + b.val n ≤ c.val n := by
  simp only [polyAdd] at h
  rw [Prod.mk.injEq] at h
  obtain ⟨hc, hover⟩ := h
  obtain ⟨e4, f3⟩ := satAdd_snd hover
  obtain ⟨e3, f2⟩ := satAdd_snd f3
  obtain ⟨e2, f1⟩ := satAdd_snd f2
  obtain ⟨e1, f0⟩ := satAdd_snd f1
  obtain ⟨e0, -⟩ := satAdd_snd f0
  subst hc
  rw [val_norm, e0, e1, e2, e3, e4]
  have hM1 : a.base ≤ (if b.base > a.base then b.base else a.base) := by
    split <;> omega
  have hM2 : b.base ≤ (if b.base > a.base then b.base else a.base) := by
    split <;> omega
  have h1 : a.val n ≤ (if b.base > a.base then b.base else a.base) ^ n * a.part n :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM1 n)
  have h2 : b.val n ≤ (if b.base > a.base then b.base else a.base) ^ n * b.part n :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM2 n)
  have hsum : (if b.base > a.base then b.base else a.base) ^ n * a.part n +
      (if b.base > a.base then b.base else a.base) ^ n * b.part n =
      (if b.base > a.base then b.base else a.base) ^ n * (a.part n + b.part n) :=
    (Nat.mul_add _ _ _).symm
  have hpart : a.part n + b.part n =
      Poly.part ⟨if b.base > a.base then b.base else a.base, a.c0 + b.c0,
        a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4⟩ n := by
    simp only [Poly.part, Nat.add_mul]
    omega
  calc a.val n + b.val n
      ≤ (if b.base > a.base then b.base else a.base) ^ n * a.part n +
        (if b.base > a.base then b.base else a.base) ^ n * b.part n :=
        Nat.add_le_add h1 h2
    _ = _ := by rw [hsum, hpart]; rfl

/-- What an evaluated `Bound` says about a number: an ok answer is that
number exactly, and a refusal means the number passed the counter cap. The
evaluation chain of `polyValue` preserves this reading step by step. -/
def Bound.approx (b : Bound) (x : Nat) : Prop :=
  (b.ok = true → b.value = x) ∧ (b.ok = false → counterMax < x)

theorem approx_finite (x : Nat) : (Bound.finite x).approx x :=
  ⟨fun _ => rfl, fun h => nomatch h⟩

theorem Bound.approx.congr {b : Bound} {x y : Nat} (h : b.approx x)
    (e : x = y) : b.approx y := e ▸ h

/-- `boundAdd` keeps the reading: exact on exact inputs, and a refusal
either came in — the true number is even bigger — or was a pre-checked
overflow of the true sum. -/
theorem boundAdd_approx {a b : Bound} {x y : Nat}
    (ha : a.approx x) (hb : b.approx y) : (boundAdd a b).approx (x + y) := by
  simp only [boundAdd]
  split
  · rename_i hno
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    have hor : a.ok = false ∨ b.ok = false := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    rcases hor with h' | h'
    · exact Nat.lt_of_lt_of_le (ha.2 h') (Nat.le_add_right x y)
    · exact Nat.lt_of_lt_of_le (hb.2 h') (Nat.le_add_left y x)
  · rename_i hno
    have hab : a.ok = true ∧ b.ok = true := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    rw [ha.1 hab.1, hb.1 hab.2]
    by_cases hover : counterMax - y < x
    · have hs : satAdd x y false = (counterMax, true) := by
        unfold satAdd
        rw [if_pos hover]
      rw [hs]
      exact ⟨(fun h => nomatch h), fun _ => by omega⟩
    · have hs : satAdd x y false = (x + y, false) := by
        unfold satAdd
        rw [if_neg hover]
      rw [hs]
      exact ⟨fun _ => rfl, (fun h => nomatch h)⟩

/-- `boundMul`, same reading. Positivity of both factors is what lets a
refusal on either side survive the multiplication. -/
theorem boundMul_approx {a b : Bound} {x y : Nat} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (ha : a.approx x) (hb : b.approx y) : (boundMul a b).approx (x * y) := by
  simp only [boundMul]
  split
  · rename_i hno
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    have hor : a.ok = false ∨ b.ok = false := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    rcases hor with h' | h'
    · exact Nat.lt_of_lt_of_le (ha.2 h') (Nat.le_mul_of_pos_right x hy)
    · exact Nat.lt_of_lt_of_le (hb.2 h') (Nat.le_mul_of_pos_left y hx)
  · rename_i hno
    have hab : a.ok = true ∧ b.ok = true := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    rw [ha.1 hab.1, hb.1 hab.2]
    by_cases hover : counterMax / y < x
    · have hs : satMul x y false = (counterMax, true) := by
        unfold satMul
        rw [if_neg (by omega), if_pos hover]
      rw [hs]
      exact ⟨(fun h => nomatch h),
        fun _ => (Nat.div_lt_iff_lt_mul (by omega)).mp hover⟩
    · have hs : satMul x y false = (x * y, false) := by
        unfold satMul
        rw [if_neg (by omega), if_neg hover]
      rw [hs]
      exact ⟨fun _ => rfl, (fun h => nomatch h)⟩

/-- A raised `satMul` flag was either already up or marks a product past
the cap. -/
theorem satMul_over {x y : Nat} {over : Bool}
    (h : (satMul x y over).2 = true) : over = true ∨ counterMax < x * y := by
  unfold satMul at h
  split at h
  · exact Or.inl h
  · rename_i hz
    rw [not_or] at hz
    split at h
    · rename_i hgt
      exact Or.inr ((Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hz.2)).mp hgt)
    · exact Or.inl h

/-- Once the power loop refuses, it stays refused whatever fuel is left. -/
theorem boundPowGo_exceeds (base exp v : Nat) :
    ∀ (fuel i : Nat), boundPowGo base exp fuel i ⟨false, v⟩ = ⟨false, v⟩
  | 0, _ => rfl
  | fuel + 1, i => by
      unfold boundPowGo
      rw [if_neg (by simp)]

/-- The loop of `boundPow` on an honest state: with a base of at least two
the running value doubles every round, so within the given fuel it either
finishes with the exact power or refuses one that passed the cap. -/
theorem boundPowGo_spec {base exp : Nat} (hbase : 2 ≤ base) :
    ∀ (fuel i : Nat), i ≤ exp → base ^ i ≤ counterMax →
      min (exp - i) (53 - i) < fuel →
      boundPowGo base exp fuel i ⟨true, base ^ i⟩ =
        if base ^ exp ≤ counterMax then ⟨true, base ^ exp⟩ else ⟨false, 0⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro i _ _ hfuel
    exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro i hle hcap hfuel
    by_cases hi : i < exp
    · have hz1 : base ^ i ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))
      have hz2 : base ≠ 0 := by omega
      unfold boundPowGo
      rw [if_pos ⟨hi, rfl⟩]
      have hi53 : i < 53 := by
        have h2i : 2 ^ i ≤ counterMax :=
          Nat.le_trans (Nat.pow_le_pow_left hbase i) hcap
        rcases Nat.lt_or_ge i 53 with h53 | h53
        · exact h53
        · exfalso
          have hup : 2 ^ 53 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) h53
          have hcm : counterMax < 2 ^ 53 := by decide
          omega
      by_cases hover : counterMax / base < base ^ i
      · have hmul : boundMul ⟨true, base ^ i⟩ (Bound.finite base) = Bound.exceeds := by
          have hs : satMul (base ^ i) base false = (counterMax, true) := by
            unfold satMul
            rw [if_neg (by omega), if_pos hover]
          simp [boundMul, Bound.finite, hs]
        rw [hmul, show Bound.exceeds = (⟨false, 0⟩ : Bound) from rfl,
          boundPowGo_exceeds]
        have hbig : counterMax < base ^ (i + 1) := by
          have := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hz2)).mp hover
          rwa [← Nat.pow_succ] at this
        have hmore : base ^ (i + 1) ≤ base ^ exp :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [if_neg (by omega)]
      · have hcap' : base ^ (i + 1) ≤ counterMax := by
          have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hz2)).mp
            (Nat.not_lt.mp hover)
          rwa [← Nat.pow_succ] at this
        have hmul : boundMul ⟨true, base ^ i⟩ (Bound.finite base) =
            Bound.finite (base ^ (i + 1)) := by
          have hs : satMul (base ^ i) base false = (base ^ (i + 1), false) := by
            rw [Nat.pow_succ]
            exact satMul_of_le false (by rwa [← Nat.pow_succ])
          simp [boundMul, Bound.finite, hs]
        rw [hmul]
        exact ih (i + 1) hi hcap' (by omega)
    · have hie : i = exp := Nat.le_antisymm hle (Nat.not_lt.mp hi)
      subst hie
      unfold boundPowGo
      rw [if_neg (by simp [hi])]
      rw [if_pos hcap]

/-- `boundPow` is `base ^ exp`, or a refusal of a power past the cap. -/
theorem boundPow_spec (base exp : Nat) :
    boundPow base exp =
      if base ^ exp ≤ counterMax then ⟨true, base ^ exp⟩ else ⟨false, 0⟩ := by
  unfold boundPow
  split
  · rename_i h1
    subst h1
    rw [Nat.one_pow, if_pos (by decide)]
    rfl
  · split
    · rename_i h1 h0
      subst h0
      split
      · rename_i he
        subst he
        rw [Nat.pow_zero, if_pos (by decide)]
        rfl
      · rename_i he
        rw [Nat.zero_pow (Nat.pos_of_ne_zero he), if_pos (Nat.zero_le _)]
        rfl
    · rename_i h1 h0
      have hbase : 2 ≤ base := by omega
      have := boundPowGo_spec (exp := exp) hbase 55 0 (Nat.zero_le _)
        (by rw [Nat.pow_zero]; decide) (by omega)
      rw [Nat.pow_zero] at this
      exact this

theorem boundPow_ok {base exp : Nat} (h : (boundPow base exp).ok = true) :
    (boundPow base exp).value = base ^ exp := by
  rw [boundPow_spec] at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
  · cases h

theorem boundPow_not_ok {base exp : Nat} (h : (boundPow base exp).ok = false) :
    counterMax < base ^ exp := by
  rw [boundPow_spec] at h
  split at h
  · cases h
  · rename_i hc
    omega

/-- One coefficient step of `polyValue`: spending a coefficient on a power
keeps the running total honest, and a coefficient of zero spends nothing. -/
theorem coefTerm_approx {tot pw : Bound} {S P : Nat} (c : Nat)
    (htot : tot.approx S) (hpw : pw.approx P) (hP : 1 ≤ P) :
    (if c ≠ 0 then boundAdd tot (boundMul (Bound.finite c) pw)
      else tot).approx (S + c * P) := by
  split
  · rename_i hc
    exact boundAdd_approx htot
      (boundMul_approx (Nat.pos_of_ne_zero hc) hP (approx_finite c) hpw)
  · rename_i hc
    have hc0 : c = 0 := by omega
    exact htot.congr (by simp [hc0])

/-- The shape of a `polyValue` run on a bound that is not nothing: a power
of the base times a coefficient chain that reads back the polynomial part,
which is itself at least one. -/
theorem polyValue_shape (p : Poly) (n : Nat) (hn : ¬ p.nothing = true) :
    ∃ st : Bound, polyValue p n = boundMul (boundPow p.base n) st ∧
      st.approx (p.part n) ∧ 1 ≤ p.part n := by
  rw [polyValue, if_neg hn]
  simp only []
  refine ⟨_, rfl, ?_⟩
  have hA : 0 < n + 1 := Nat.succ_pos n
  have hrise : (boundAdd (Bound.finite n) (Bound.finite 1)).approx (n + 1) :=
    boundAdd_approx (approx_finite n) (approx_finite 1)
  have hpw1 : (boundMul (Bound.finite 1)
      (boundAdd (Bound.finite n) (Bound.finite 1))).approx ((n + 1) ^ 1) :=
    (boundMul_approx (by omega) hA (approx_finite 1) hrise).congr (by simp)
  have hT1 := coefTerm_approx p.c1 (approx_finite p.c0) hpw1 (Nat.pow_pos hA)
  by_cases hc4 : p.c4 = 0
  · by_cases hc3 : p.c3 = 0
    · by_cases hc2 : p.c2 = 0
      · by_cases hc1 : p.c1 = 0
        · -- every higher coefficient is zero: no power was ever
          -- spent, and the total is the constant coefficient
          have g1 : ¬((p.c1 != 0 || p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true) := by
            simp [hc1, hc2, hc3, hc4]
          have g2 : ¬((p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true) := by
            simp [hc2, hc3, hc4]
          have g3 : ¬((p.c3 != 0 || p.c4 != 0) = true) := by simp [hc3, hc4]
          have g4 : ¬((p.c4 != 0) = true) := by simp [hc4]
          simp only [if_neg g1, if_neg g2, if_neg g3, if_neg g4]
          have hc0 : p.c0 ≠ 0 := by
            intro h0
            exact hn (nothing_iff.mpr ⟨h0, hc1, hc2, hc3, hc4⟩)
          refine ⟨(approx_finite p.c0).congr ?_, ?_⟩
          · simp [Poly.part, hc1, hc2, hc3, hc4]
          · simp only [Poly.part, hc1, hc2, hc3, hc4]
            omega
        · -- the highest nonzero coefficient has degree one
          have f1 : (p.c1 != 0 || p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by
            simp [hc1]
          have g2 : ¬((p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true) := by
            simp [hc2, hc3, hc4]
          have g3 : ¬((p.c3 != 0 || p.c4 != 0) = true) := by simp [hc3, hc4]
          have g4 : ¬((p.c4 != 0) = true) := by simp [hc4]
          simp only [if_pos f1, if_neg g2, if_neg g3, if_neg g4]
          refine ⟨hT1.congr ?_, ?_⟩
          · simp [Poly.part, hc2, hc3, hc4, Nat.pow_one]
          · have ht : 0 < p.c1 * (n + 1) :=
              Nat.mul_pos (Nat.pos_of_ne_zero hc1) hA
            simp only [Poly.part]
            omega
      · -- the highest nonzero coefficient has degree two
        have f1 : (p.c1 != 0 || p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by
          simp [hc2]
        have f2 : (p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by simp [hc2]
        have g3 : ¬((p.c3 != 0 || p.c4 != 0) = true) := by simp [hc3, hc4]
        have g4 : ¬((p.c4 != 0) = true) := by simp [hc4]
        simp only [if_pos f1, if_pos f2, if_neg g3, if_neg g4]
        have hpw2 := (boundMul_approx (Nat.pow_pos hA) hA hpw1 hrise).congr
          (by rw [← Nat.pow_succ] :
            (n + 1) ^ 1 * (n + 1) = (n + 1) ^ 2)
        have hT2 := coefTerm_approx p.c2 hT1 hpw2 (Nat.pow_pos hA)
        refine ⟨hT2.congr ?_, ?_⟩
        · simp [Poly.part, hc3, hc4, Nat.pow_one]
        · have ht : 0 < p.c2 * (n + 1) ^ 2 :=
            Nat.mul_pos (Nat.pos_of_ne_zero hc2) (Nat.pow_pos hA)
          simp only [Poly.part]
          omega
    · -- the highest nonzero coefficient has degree three
      have f1 : (p.c1 != 0 || p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by
        simp [hc3]
      have f2 : (p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by simp [hc3]
      have f3 : (p.c3 != 0 || p.c4 != 0) = true := by simp [hc3]
      have g4 : ¬((p.c4 != 0) = true) := by simp [hc4]
      simp only [if_pos f1, if_pos f2, if_pos f3, if_neg g4]
      have hpw2 := (boundMul_approx (Nat.pow_pos hA) hA hpw1 hrise).congr
        (by rw [← Nat.pow_succ] : (n + 1) ^ 1 * (n + 1) = (n + 1) ^ 2)
      have hT2 := coefTerm_approx p.c2 hT1 hpw2 (Nat.pow_pos hA)
      have hpw3 := (boundMul_approx (Nat.pow_pos hA) hA hpw2 hrise).congr
        (by rw [← Nat.pow_succ] : (n + 1) ^ 2 * (n + 1) = (n + 1) ^ 3)
      have hT3 := coefTerm_approx p.c3 hT2 hpw3 (Nat.pow_pos hA)
      refine ⟨hT3.congr ?_, ?_⟩
      · simp [Poly.part, hc4, Nat.pow_one]
      · have ht : 0 < p.c3 * (n + 1) ^ 3 :=
          Nat.mul_pos (Nat.pos_of_ne_zero hc3) (Nat.pow_pos hA)
        simp only [Poly.part]
        omega
  · -- the highest nonzero coefficient has degree four
    have f1 : (p.c1 != 0 || p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by
      simp [hc4]
    have f2 : (p.c2 != 0 || p.c3 != 0 || p.c4 != 0) = true := by simp [hc4]
    have f3 : (p.c3 != 0 || p.c4 != 0) = true := by simp [hc4]
    have f4 : (p.c4 != 0) = true := by simp [hc4]
    simp only [if_pos f1, if_pos f2, if_pos f3, if_pos f4]
    have hpw2 := (boundMul_approx (Nat.pow_pos hA) hA hpw1 hrise).congr
      (by rw [← Nat.pow_succ] : (n + 1) ^ 1 * (n + 1) = (n + 1) ^ 2)
    have hT2 := coefTerm_approx p.c2 hT1 hpw2 (Nat.pow_pos hA)
    have hpw3 := (boundMul_approx (Nat.pow_pos hA) hA hpw2 hrise).congr
      (by rw [← Nat.pow_succ] : (n + 1) ^ 2 * (n + 1) = (n + 1) ^ 3)
    have hT3 := coefTerm_approx p.c3 hT2 hpw3 (Nat.pow_pos hA)
    have hpw4 := (boundMul_approx (Nat.pow_pos hA) hA hpw3 hrise).congr
      (by rw [← Nat.pow_succ] : (n + 1) ^ 3 * (n + 1) = (n + 1) ^ 4)
    have hT4 := coefTerm_approx p.c4 hT3 hpw4 (Nat.pow_pos hA)
    refine ⟨hT4.congr ?_, ?_⟩
    · simp [Poly.part, Nat.pow_one]
    · have ht : 0 < p.c4 * (n + 1) ^ 4 :=
        Nat.mul_pos (Nat.pos_of_ne_zero hc4) (Nat.pow_pos hA)
      simp only [Poly.part]
      omega

/-- An ok `boundMul` had ok inputs and answers their exact product. -/
theorem boundMul_eq_ok {a b : Bound} {v : Nat}
    (h : boundMul a b = ⟨true, v⟩) :
    a.ok = true ∧ b.ok = true ∧ v = a.value * b.value := by
  simp only [boundMul] at h
  split at h
  · simp [Bound.exceeds] at h
  · rename_i hno
    have hab : a.ok = true ∧ b.ok = true := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    refine ⟨hab.1, hab.2, ?_⟩
    split at h
    · simp [Bound.exceeds] at h
    · rename_i hov
      rw [Bool.not_eq_true] at hov
      obtain ⟨he, -⟩ := satMul_snd hov
      have hv : (satMul a.value b.value false).1 = v := by
        simpa [Bound.finite, Bound.mk.injEq] using h
      omega

/-- A refused `boundMul` had a refused input or a product past the cap. -/
theorem boundMul_eq_exceeds {a b : Bound} {v : Nat}
    (h : boundMul a b = ⟨false, v⟩) :
    a.ok = false ∨ b.ok = false ∨
      (a.ok = true ∧ b.ok = true ∧ counterMax < a.value * b.value) := by
  simp only [boundMul] at h
  split at h
  · rename_i hno
    have hor : a.ok = false ∨ b.ok = false := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    rcases hor with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rename_i hno
    have hab : a.ok = true ∧ b.ok = true := by
      rcases h1 : a.ok <;> rcases h2 : b.ok <;> simp_all
    refine Or.inr (Or.inr ⟨hab.1, hab.2, ?_⟩)
    split at h
    · rename_i hov
      rcases satMul_over hov with h' | h'
      · cases h'
      · exact h'
    · simp [Bound.finite] at h

/-- First half of `polyValue`'s soundness: an ok evaluation answers exactly
the value of the bound. -/
theorem polyValue_ok {p : Poly} {n v : Nat}
    (h : polyValue p n = ⟨true, v⟩) : v = p.val n := by
  by_cases hn : p.nothing = true
  · rw [polyValue, if_pos hn] at h
    have hv : v = 0 := by
      have := h
      simp only [Bound.finite, Bound.mk.injEq] at this
      omega
    obtain ⟨h0, h1, h2, h3, h4⟩ := nothing_iff.mp hn
    simp [Poly.val, Poly.part, hv, h0, h1, h2, h3, h4]
  · obtain ⟨st, heq, happ, -⟩ := polyValue_shape p n hn
    rw [heq] at h
    obtain ⟨hpo, hso, hv⟩ := boundMul_eq_ok h
    rw [boundPow_ok hpo, happ.1 hso] at hv
    exact hv

/-- Second half: a refusal really means the value passed the counter cap.
The base must carry at least one — a base-zero bound is worth nothing from
length one on, yet its coefficient chain can still refuse. Nothing in the
algebra lowers a base below one: `Poly.zero` and normalization pin base
one, addition keeps the larger base, and multiplication multiplies. -/
theorem polyValue_exceeds {p : Poly} {n v : Nat} (hbase : 1 ≤ p.base)
    (h : polyValue p n = ⟨false, v⟩) : counterMax < p.val n := by
  by_cases hn : p.nothing = true
  · rw [polyValue, if_pos hn] at h
    simp [Bound.finite, Bound.mk.injEq] at h
  · obtain ⟨st, heq, happ, hpos⟩ := polyValue_shape p n hn
    rw [heq] at h
    have hval : p.val n = p.base ^ n * p.part n := rfl
    rcases boundMul_eq_exceeds h with hpow | hst | ⟨hpo, hso, hover⟩
    · have hbig := boundPow_not_ok hpow
      have h2 : p.base ^ n ≤ p.base ^ n * p.part n :=
        Nat.le_mul_of_pos_right _ hpos
      rw [hval]
      omega
    · have hbig := happ.2 hst
      have h2 : p.part n ≤ p.base ^ n * p.part n :=
        Nat.le_mul_of_pos_left _ (Nat.pow_pos hbase)
      rw [hval]
      omega
    · rw [boundPow_ok hpo, happ.1 hso] at hover
      rw [hval]
      exact hover

theorem Poly.coef_zero (p : Poly) : p.coef 0 = p.c0 := rfl
theorem Poly.coef_one (p : Poly) : p.coef 1 = p.c1 := rfl
theorem Poly.coef_two (p : Poly) : p.coef 2 = p.c2 := rfl
theorem Poly.coef_three (p : Poly) : p.coef 3 = p.c3 := rfl
theorem Poly.coef_four (p : Poly) : p.coef 4 = p.c4 := rfl

theorem Poly.setCoef_base (p : Poly) (d v : Nat) :
    (p.setCoef d v).base = p.base := by
  rcases d with _ | _ | _ | _ | d <;> rfl

theorem Poly.coef_setCoef_self (p : Poly) (d v : Nat) :
    (p.setCoef d v).coef d = v := by
  rcases d with _ | _ | _ | _ | d <;> rfl

theorem Poly.coef_setCoef_ne (p : Poly) {d k : Nat} (v : Nat) (hd : d ≤ 4)
    (hk : k ≤ 4) (hne : k ≠ d) : (p.setCoef d v).coef k = p.coef k := by
  rcases d with _ | _ | _ | _ | d <;> rcases k with _ | _ | _ | _ | k <;>
    first | rfl | omega

/-- The fold step of `polyMul`, written with projections so the proofs can
name it: skip a pair with a zero on either side, refuse a product past
degree four, and otherwise convolve one coefficient product in. -/
def mulStep (a b : Poly) (st : Poly × Bool) (q : Nat × Nat) : Poly × Bool :=
  if a.coef q.1 ≠ 0 ∧ b.coef q.2 ≠ 0 then
    if q.1 + q.2 > maxDegree then (st.1, true)
    else
      (st.1.setCoef (q.1 + q.2)
          (satAdd (st.1.coef (q.1 + q.2))
              (satMul (a.coef q.1) (b.coef q.2) st.2).1
              (satMul (a.coef q.1) (b.coef q.2) st.2).2).1,
        (satAdd (st.1.coef (q.1 + q.2))
            (satMul (a.coef q.1) (b.coef q.2) st.2).1
            (satMul (a.coef q.1) (b.coef q.2) st.2).2).2)
  else st

/-- The step never lowers a raised flag. -/
theorem mulStep_flag {a b : Poly} {st : Poly × Bool} {q : Nat × Nat}
    (h : (mulStep a b st q).2 = false) : st.2 = false := by
  unfold mulStep at h
  split at h
  · split at h
    · simp at h
    · obtain ⟨-, h1⟩ := satAdd_snd h
      obtain ⟨-, h2⟩ := satMul_snd h1
      exact h2
  · exact h

/-- Nor does the fold: a clean flag out means a clean flag in. -/
theorem mulFold_flag {a b : Poly} {f : Poly × Bool → Nat × Nat → Poly × Bool}
    (hf : ∀ st q, f st q = mulStep a b st q) :
    ∀ (L : List (Nat × Nat)) (st : Poly × Bool),
      (L.foldl f st).2 = false → st.2 = false
  | [], _, h => h
  | q :: L, st, h => by
      rw [List.foldl_cons] at h
      have h2 := mulFold_flag hf L (f st q) h
      rw [hf] at h2
      exact mulStep_flag h2

/-- What a clean run of the convolution fold did: the flag came in clean,
the base was left alone, no surviving pair sat above degree four — a
nonzero one would have raised the flag for good — and every coefficient at
or under the cap degree collected exactly its share of the convolution. -/
theorem mulFold_spec {a b : Poly} {f : Poly × Bool → Nat × Nat → Poly × Bool} :
    ∀ (L : List (Nat × Nat)) (out : Poly) (over : Bool),
      (L.foldl f (out, over)).2 = false →
      (∀ st q, f st q = mulStep a b st q) →
      over = false ∧
      (L.foldl f (out, over)).1.base = out.base ∧
      (∀ l r, (l, r) ∈ L → 4 < l + r → a.coef l * b.coef r = 0) ∧
      (∀ k, k ≤ 4 → (L.foldl f (out, over)).1.coef k =
        out.coef k +
          (L.map fun q =>
            if q.1 + q.2 = k then a.coef q.1 * b.coef q.2 else 0).sum) := by
  intro L
  induction L with
  | nil =>
    intro out over h hf
    refine ⟨h, rfl, ?_, ?_⟩
    · intro l r hmem
      cases hmem
    · intro k _
      simp
  | cons q L ih =>
    obtain ⟨l0, r0⟩ := q
    intro out over h hf
    have hmd : maxDegree = 4 := rfl
    simp only [List.foldl_cons, hf, mulStep] at h ⊢
    by_cases hguard : a.coef l0 ≠ 0 ∧ b.coef r0 ≠ 0
    · simp only [if_pos hguard] at h ⊢
      by_cases hdeg : l0 + r0 > maxDegree
      · simp only [if_pos hdeg] at h ⊢
        have := mulFold_flag hf L _ h
        simp at this
      · simp only [if_neg hdeg] at h ⊢
        obtain ⟨hR2, hbase, hpairs, hcoef⟩ := ih _ _ h hf
        obtain ⟨hrun, hsm2⟩ := satAdd_snd hR2
        obtain ⟨hone, hover⟩ := satMul_snd hsm2
        refine ⟨hover, ?_, ?_, ?_⟩
        · rw [hbase, Poly.setCoef_base]
        · intro l r hmem hlr
          rcases List.mem_cons.mp hmem with hq | hq
          · obtain ⟨he1, he2⟩ := Prod.mk.injEq .. |>.mp hq
            subst he1
            subst he2
            omega
          · exact hpairs l r hq hlr
        · intro k hk
          rw [hcoef k hk, List.map_cons, List.sum_cons]
          dsimp only
          by_cases hkd : k = l0 + r0
          · subst hkd
            rw [Poly.coef_setCoef_self, hrun, hone, if_pos rfl]
            omega
          · rw [Poly.coef_setCoef_ne out _ (by omega) hk hkd,
              if_neg (fun hh => hkd hh.symm)]
            omega
    · simp only [if_neg hguard] at h ⊢
      obtain ⟨hover, hbase, hpairs, hcoef⟩ := ih _ _ h hf
      have hz : a.coef l0 * b.coef r0 = 0 := by
        rw [Nat.mul_eq_zero]
        omega
      refine ⟨hover, hbase, ?_, ?_⟩
      · intro l r hmem hlr
        rcases List.mem_cons.mp hmem with hq | hq
        · obtain ⟨he1, he2⟩ := Prod.mk.injEq .. |>.mp hq
          subst he1
          subst he2
          exact hz
        · exact hpairs l r hq hlr
      · intro k hk
        rw [hcoef k hk, List.map_cons, List.sum_cons]
        dsimp only
        rw [hz, ite_self]
        omega

/-- Two five-term polynomials in `A` multiply into their convolution, high
degrees included. Stated over plain numbers so the soundness proof can point
each monomial at a coefficient product. -/
theorem five_term_mul (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 A : Nat) :
    (a0 + a1 * A + a2 * A ^ 2 + a3 * A ^ 3 + a4 * A ^ 4) *
      (b0 + b1 * A + b2 * A ^ 2 + b3 * A ^ 3 + b4 * A ^ 4) =
      a0 * b0
      + (a0 * b1 + a1 * b0) * A
      + (a0 * b2 + a1 * b1 + a2 * b0) * A ^ 2
      + (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * A ^ 3
      + (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) * A ^ 4
      + (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) * A ^ 5
      + (a2 * b4 + a3 * b3 + a4 * b2) * A ^ 6
      + (a3 * b4 + a4 * b3) * A ^ 7
      + a4 * b4 * A ^ 8 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.add_mul, Nat.mul_add]
  ac_rfl

/-- The degree pairs `polyMul` folds over, written out. -/
theorem mulPairs_eq :
    List.flatMap (fun left => List.map (fun right => (left, right))
        (List.range (maxDegree + 1))) (List.range (maxDegree + 1)) =
      [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
       (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
       (2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
       (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
       (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] := rfl

/-- `polyMul` with a clean flag is exact: bases multiply, coefficients
convolve, and every pair that would have landed past degree four had a zero
on one side — a nonzero one would have raised the flag. -/
theorem polyMul_sound {a b c : Poly} {over : Bool}
    (h : polyMul a b over = (c, false)) (n : Nat) :
    c.val n = a.val n * b.val n := by
  simp only [polyMul] at h
  rw [Prod.mk.injEq] at h
  obtain ⟨hc, hflag⟩ := h
  obtain ⟨hov0, hbase, hzero, hcoef⟩ := mulFold_spec _ _ _ hflag (fun st q => rfl)
  rw [mulPairs_eq] at hc hbase hzero hcoef
  obtain ⟨hbe, -⟩ := satMul_snd hov0
  subst hc
  rw [val_norm]
  have hbasef := hbase.trans hbe
  simp only [Poly.zero] at hbasef
  have z14 : a.c1 * b.c4 = 0 := hzero 1 4 (by decide) (by omega)
  have z23 : a.c2 * b.c3 = 0 := hzero 2 3 (by decide) (by omega)
  have z32 : a.c3 * b.c2 = 0 := hzero 3 2 (by decide) (by omega)
  have z41 : a.c4 * b.c1 = 0 := hzero 4 1 (by decide) (by omega)
  have z24 : a.c2 * b.c4 = 0 := hzero 2 4 (by decide) (by omega)
  have z33 : a.c3 * b.c3 = 0 := hzero 3 3 (by decide) (by omega)
  have z42 : a.c4 * b.c2 = 0 := hzero 4 2 (by decide) (by omega)
  have z34 : a.c3 * b.c4 = 0 := hzero 3 4 (by decide) (by omega)
  have z43 : a.c4 * b.c3 = 0 := hzero 4 3 (by decide) (by omega)
  have z44 : a.c4 * b.c4 = 0 := hzero 4 4 (by decide) (by omega)
  have h0 := hcoef 0 (by omega)
  have h1 := hcoef 1 (by omega)
  have h2 := hcoef 2 (by omega)
  have h3 := hcoef 3 (by omega)
  have h4 := hcoef 4 (by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.reduceAdd, Nat.reduceEqDiff, reduceIte, Poly.coef_zero, Poly.coef_one,
    Poly.coef_two, Poly.coef_three, Poly.coef_four, Poly.zero, Nat.zero_add,
    Nat.add_zero] at h0 h1 h2 h3 h4
  have hval : ∀ (x : Poly) (m : Nat), x.val m = x.base ^ m *
      (x.c0 + x.c1 * (m + 1) + x.c2 * (m + 1) ^ 2 +
        x.c3 * (m + 1) ^ 3 + x.c4 * (m + 1) ^ 4) := fun x m => rfl
  simp only [hval, Poly.zero]
  rw [hbasef, h0, h1, h2, h3, h4, Nat.mul_pow, Nat.mul_mul_mul_comm,
    five_term_mul, z14, z23, z32, z41, z24, z33, z42, z34, z43, z44]
  simp only [Nat.add_mul, Nat.zero_mul, Nat.add_zero]
  congr 1
  omega

/-- `growthCap` with a clean flag answers the exact schedule: nothing for
no entries, else the doubling run's final capacity. -/
theorem growthCap_sound {e v : Nat} {over : Bool}
    (h : growthCap e over = (v, false)) :
    v = if e = 0 then 0 else growMin + growFactor * e := by
  unfold growthCap at h
  split at h
  · rename_i he
    obtain ⟨hv, h2⟩ := satAdd_exact h
    obtain ⟨hd, -⟩ := satMul_snd h2
    have hv' : v = (satMul e growFactor over).1 + growMin := hv
    rw [hd] at hv'
    rw [if_neg (by omega)]
    simp only [growMin, growFactor] at hv' ⊢
    omega
  · rename_i he
    rw [Prod.mk.injEq] at h
    rw [if_pos (by omega)]
    omega

end Pcrevera.Ref
