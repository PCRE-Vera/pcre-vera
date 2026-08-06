import Pcrevera.Proofs.LowerEval
import Pcrevera.Proofs.LowerNull

/-!
# The two splices (L-2a and L-2b)

This is where the lowering earns its name. A counted repetition and the
unrolled tree the code generator really walks return *the same ordered list
of threads* — same positions, same capture registers, same order — so nothing
downstream can tell them apart, `scan` picking the first survivor included.

The two quantifier families fail differently and are proved apart.

The bounded one is a finite splice. At count `k` a `x{m,n}` has exactly the
behaviour of the optional chain at `n - k`, and below the minimum exactly the
behaviour of a copy followed by the rest; both are downward inductions, on
`n - k` and on `m - k`, and neither needs a semantic hypothesis. The bounds
being in order is not needed either: `x{5,2}` runs five copies on both sides,
because the count reaches the minimum before the high stops it, and truncated
subtraction leaves the optional chain empty.

The unbounded one turns on a fact rather than on bookkeeping: past the minimum
an unbounded repetition's count stops mattering, because `cnt` is read in two
places and both stop caring once `cnt ≥ lo`. That is `searchRep_count_free`,
and it is what lets the tail of the unrolled form be a pure star whose count
restarts at zero. The splice then needs the body not to match empty, or the
original's empty-match rule would fire at the last copy where the star's would
not — which is `LB_NULLABLE`, arriving here as `Nullable b = false`.
-/

namespace Pcrevera.Spec

open Pcrevera

/-- A one-element concatenation is its element. -/
theorem searchCat_single {fuel : Nat} {c : SCtx} {y : Ast} {pos : Nat}
    {regs : Regs} : searchCat fuel c [y] pos regs = search fuel c y pos regs := by
  have hmap : ∀ l : List Thread,
      (l.mapM fun t => searchCat fuel c [] t.pos t.regs)
        = some (l.map fun t => [t]) := by
    intro l
    induction l with
    | nil => rfl
    | cons t ts ih =>
        rw [List.mapM_cons, searchCat.eq_def, ih]
        rfl
  have hflat : ∀ l : List Thread, (l.map fun t => [t]).flatten = l := by
    intro l
    induction l with
    | nil => rfl
    | cons t ts ih => simp [ih]
  rw [searchCat.eq_def]
  simp only []
  cases hy : search fuel c y pos regs with
  | none => simp
  | some heads => simp [hmap, hflat]

theorem ev_nul {c : SCtx} {pos : Nat} {regs : Regs} :
    ev c .nul pos regs = some [⟨pos, regs⟩] := by
  rw [ev, search.eq_def]

/-- A two-element concatenation, read at each part's own sufficient fuel. -/
theorem ev_cat2 {c : SCtx} {x y : Ast} {pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size) :
    ev c (.cat [x, y]) pos regs =
      (do
        let heads ← ev c x pos regs
        let tails ← heads.mapM fun t => ev c y t.pos t.regs
        pure tails.flatten) := by
  have hx : suffFuel c.s.size x ≤ suffFuel c.s.size (.cat [x, y]) :=
    suffFuel_le_cat (by simp)
  have hy : suffFuel c.s.size y ≤ suffFuel c.s.size (.cat [x, y]) :=
    suffFuel_le_cat (by simp)
  rw [ev, search.eq_def]
  simp only []
  rw [searchCat.eq_def]
  simp only []
  rw [search_eq_ev hpos hx]
  cases hheads : ev c x pos regs with
  | none => rfl
  | some heads =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      refine mapM_flatten_congr fun t ht => ?_
      have hb := ev_pos_le hheads hpos t ht
      rw [searchCat_single, search_eq_ev hb.2 hy]

/-- The one-split optional, read the same way. -/
theorem ev_optional {c : SCtx} {body : Ast} {greedy : Bool} {pos : Nat}
    {regs : Regs} (hpos : pos ≤ c.s.size) :
    ev c (.rep 0 (some 1) greedy body) pos regs =
      (ev c body pos regs).map fun taken =>
        if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken := by
  have hb : suffFuel c.s.size body
      ≤ suffFuel c.s.size (.rep 0 (some 1) greedy body) := by
    rw [suffFuel]; omega
  rw [ev, search.eq_def]
  simp only []
  rw [if_neg (by simp), search_eq_ev hpos hb]

/-- Every other quantifier is its own remaining rounds, counted from zero. -/
theorem ev_rep_bounded {c : SCtx} {body : Ast} {lo h : Nat} {greedy : Bool}
    {pos : Nat} {regs : Regs} (hpos : pos ≤ c.s.size) :
    ev c (.rep lo (some (h + 2)) greedy body) pos regs
      = evRep c body lo (some (h + 2)) greedy 0 pos regs := by
  rw [ev, search.eq_def]
  refine searchRep_eq_evRep hpos ?_
  rw [suffFuel]
  simp only [repRemaining]
  omega

theorem ev_rep_unbounded {c : SCtx} {body : Ast} {lo : Nat} {greedy : Bool}
    {pos : Nat} {regs : Regs} (hpos : pos ≤ c.s.size) :
    ev c (.rep lo none greedy body) pos regs
      = evRep c body lo none greedy 0 pos regs := by
  rw [ev, search.eq_def]
  refine searchRep_eq_evRep hpos ?_
  rw [suffFuel]
  simp only [repRemaining]
  omega

/-- L-2a, the tail: at or past the minimum, a bounded repetition is the
optional chain at what is left of its high. -/
theorem evRep_bounded_tail (c : SCtx) (b : Ast) (g : Bool) (lo h : Nat) :
    ∀ (d k pos : Nat) (regs : Regs), h - k ≤ d → lo ≤ k → pos ≤ c.s.size →
      evRep c b lo (some h) g k pos regs
        = ev c (optionals b g (h - k)) pos regs := by
  intro d
  induction d with
  | zero =>
      intro k pos regs hd hlo hpos
      rw [evRep_eq hpos, if_neg (by omega)]
      rw [if_pos (by simp only [Option.any_some, decide_eq_true_eq]; omega)]
      rw [show h - k = 0 by omega, optionals, ev_nul]
  | succ d ih =>
      intro k pos regs hd hlo hpos
      by_cases hkh : h ≤ k
      · rw [evRep_eq hpos, if_neg (by omega)]
        rw [if_pos (by simp only [Option.any_some, decide_eq_true_eq]; omega)]
        rw [show h - k = 0 by omega, optionals, ev_nul]
      · rw [evRep_eq hpos, if_neg (by omega)]
        rw [if_neg (by simp only [Option.any_some, decide_eq_true_eq]; omega)]
        rw [show h - k = (h - (k + 1)) + 1 by omega, optionals,
          ev_optional hpos, ev_cat2 hpos]
        refine congrArg _ ?_
        unfold repEnter
        obtain ⟨taken, htaken⟩ := Option.isSome_iff_exists.mp
          (ev_isSome (c := c) (a := b) (pos := pos) (regs := regs) hpos)
        rw [htaken]
        simp only [Option.bind_eq_bind, Option.bind_some]
        refine mapM_flatten_congr fun t ht => ?_
        have hb := ev_pos_le htaken hpos t ht
        rw [if_neg (by simp)]
        exact ih (k + 1) t.pos t.regs (by omega) (by omega) hb.2

/-- L-2a: below the minimum, the copies the minimum demands, then the chain. -/
theorem evRep_bounded (c : SCtx) (b : Ast) (g : Bool) (lo h : Nat) :
    ∀ (d k pos : Nat) (regs : Regs), lo - k ≤ d → k ≤ lo → pos ≤ c.s.size →
      evRep c b lo (some h) g k pos regs
        = ev c (copies b (optionals b g (h - lo)) (lo - k)) pos regs := by
  intro d
  induction d with
  | zero =>
      intro k pos regs hd hlo hpos
      rw [show lo - k = 0 by omega, copies]
      rw [evRep_bounded_tail c b g lo h (h - k) k pos regs (by omega)
        (by omega) hpos]
      rw [show k = lo by omega]
  | succ d ih =>
      intro k pos regs hd hlo hpos
      by_cases hkl : lo ≤ k
      · rw [show lo - k = 0 by omega, copies]
        rw [evRep_bounded_tail c b g lo h (h - k) k pos regs (by omega)
          hkl hpos]
        rw [show k = lo by omega]
      · rw [evRep_eq hpos, if_pos (by omega)]
        rw [show lo - k = (lo - (k + 1)) + 1 by omega, copies, ev_cat2 hpos]
        unfold repEnter
        obtain ⟨taken, htaken⟩ := Option.isSome_iff_exists.mp
          (ev_isSome (c := c) (a := b) (pos := pos) (regs := regs) hpos)
        rw [htaken]
        simp only [Option.bind_eq_bind, Option.bind_some]
        refine mapM_flatten_congr fun t ht => ?_
        have hb := ev_pos_le htaken hpos t ht
        rw [if_neg (by simp)]
        exact ih (k + 1) t.pos t.regs (by omega) (by omega) hb.2

/-- Past the minimum, an unbounded repetition's count stops mattering.

`cnt` is read twice — once to ask whether the minimum is behind, once in the
empty-match rule — and both readings settle the moment it is. So two runs that
differ only in how they got here, and in a minimum they have both already
met, cannot be told apart. -/
theorem searchRep_count_free (c : SCtx) (b : Ast) (g : Bool) :
    ∀ (fuel lo lo' k k' pos : Nat) (regs : Regs), lo ≤ k → lo' ≤ k' →
      searchRep fuel c b lo none g k pos regs
        = searchRep fuel c b lo' none g k' pos regs := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo lo' k k' pos regs _ _
      rw [searchRep.eq_def, searchRep.eq_def]
  | succ fuel ih =>
      intro lo lo' k k' pos regs hk hk'
      rw [searchRep.eq_def, searchRep.eq_def]
      simp only []
      rw [if_neg (show ¬ k < lo by omega), if_neg (show ¬ k' < lo' by omega)]
      simp only [Option.any_none, Bool.false_eq_true, if_false]
      have hmap : (fun t : Thread =>
          if (Option.isNone (α := Nat) none && t.pos == pos
              && decide (k + 1 ≥ lo)) = true then
            (pure [t] : Option (List Thread))
          else searchRep fuel c b lo none g (k + 1) t.pos t.regs)
          = (fun t : Thread =>
          if (Option.isNone (α := Nat) none && t.pos == pos
              && decide (k' + 1 ≥ lo')) = true then
            (pure [t] : Option (List Thread))
          else searchRep fuel c b lo' none g (k' + 1) t.pos t.regs) := by
        funext t
        rw [show (decide (k + 1 ≥ lo)) = true by
              simp only [decide_eq_true_eq]; omega,
          show (decide (k' + 1 ≥ lo')) = true by
              simp only [decide_eq_true_eq]; omega]
        split
        · rfl
        · exact ih lo lo' (k + 1) (k' + 1) t.pos t.regs (by omega) (by omega)
      rw [hmap]

/-- The same, read at the fuel each side computes for itself — which is the
same number, since `repRemaining` forgets the count once the minimum is
behind it. -/
theorem evRep_count_free {c : SCtx} {b : Ast} {g : Bool}
    {lo lo' k k' pos : Nat} {regs : Regs} (hk : lo ≤ k) (hk' : lo' ≤ k') :
    evRep c b lo none g k pos regs = evRep c b lo' none g k' pos regs := by
  unfold evRep
  rw [show repRemaining c.s.size lo none k pos
      = repRemaining c.s.size lo' none k' pos by
    simp only [repRemaining]; omega]
  exact searchRep_count_free c b g _ lo lo' k k' pos regs hk hk'

/-- L-2b: an unbounded repetition is its minimum in copies, then a pure star.

The body has to consume, or the last copy would meet pcre2's empty-match rule
on one side and not on the other. -/
theorem evRep_unbounded (c : SCtx) (b : Ast) (g : Bool) (lo : Nat)
    (hcons : Consumes c b) :
    ∀ (d k pos : Nat) (regs : Regs), lo - k ≤ d → k ≤ lo → pos ≤ c.s.size →
      evRep c b lo none g k pos regs
        = ev c (copies b (.rep 0 none g b) (lo - k)) pos regs := by
  intro d
  induction d with
  | zero =>
      intro k pos regs hd hlo hpos
      rw [show lo - k = 0 by omega, copies, ev_rep_unbounded hpos]
      exact evRep_count_free (by omega) (by omega)
  | succ d ih =>
      intro k pos regs hd hlo hpos
      by_cases hkl : lo ≤ k
      · rw [show lo - k = 0 by omega, copies, ev_rep_unbounded hpos]
        exact evRep_count_free hkl (by omega)
      · rw [evRep_eq hpos, if_pos (by omega)]
        rw [show lo - k = (lo - (k + 1)) + 1 by omega, copies, ev_cat2 hpos]
        unfold repEnter
        obtain ⟨taken, htaken⟩ := Option.isSome_iff_exists.mp
          (ev_isSome (c := c) (a := b) (pos := pos) (regs := regs) hpos)
        rw [htaken]
        simp only [Option.bind_eq_bind, Option.bind_some]
        refine mapM_flatten_congr fun t ht => ?_
        have hb := ev_pos_le htaken hpos t ht
        have hlt := hcons pos regs taken hpos htaken t ht
        rw [if_neg (by simp; omega)]
        exact ih (k + 1) t.pos t.regs (by omega) (by omega) hb.2

end Pcrevera.Spec
