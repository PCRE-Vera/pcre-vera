import Pcrevera.Proofs.LowerSplice

/-!
# L-2: the lowering is invisible to the search

The two splices of `LowerSplice.lean` say what a lowered quantifier does. This
file lifts them from one quantifier to a whole tree.

The lift is a congruence argument. `SearchEq` is an equivalence, every AST
constructor respects it, and `lower` rewrites a tree constructor by
constructor — so an induction over the tree carries the splices up to the
root. Nothing here is about fuel and nothing here is about repetitions: it is
the plumbing that makes two interesting lemmas into one theorem.

What comes out is `lower_searchEq`, the load-bearing statement: the same
ordered thread list, positions and capture registers alike, from every
position the search could be asked about. Carrying that to the answer a
caller sees is `LowerPat.lean`'s job, and it needs L-3 first.
-/

namespace Pcrevera.Spec

open Pcrevera

/-- A concatenation's budget, without the `attach` fold: enough for every
child, and visibly monotone along the list. -/
def catFuel (n : Nat) : List Ast → Nat
  | [] => 0
  | k :: rest => suffFuel n k + catFuel n rest

theorem catFuel_ge {n : Nat} {kids : List Ast} {k : Ast} (hk : k ∈ kids) :
    suffFuel n k ≤ catFuel n kids := by
  induction kids with
  | nil => cases hk
  | cons x xs ih =>
      rw [catFuel]
      rcases List.mem_cons.mp hk with rfl | hmem
      · omega
      · have := ih hmem; omega

theorem catFuel_tail {n : Nat} {x : Ast} {xs : List Ast} :
    catFuel n xs ≤ catFuel n (x :: xs) := by rw [catFuel]; omega

/-- Two budgets that both cover every child give the same answer. -/
theorem searchCat_indep {c : SCtx} {kids : List Ast} {pos : Nat} {regs : Regs}
    {fuel fuel' : Nat} (hpos : pos ≤ c.s.size)
    (hf : ∀ k ∈ kids, suffFuel c.s.size k ≤ fuel)
    (hf' : ∀ k ∈ kids, suffFuel c.s.size k ≤ fuel') :
    searchCat fuel c kids pos regs = searchCat fuel' c kids pos regs := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (searchCat_some hpos hf)
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (searchCat_some hpos hf')
  have h1 := searchCat_mono hr (Nat.le_max_left fuel fuel')
  have h2 := searchCat_mono hr' (Nat.le_max_right fuel fuel')
  rw [hr, hr', h1.symm.trans h2]

theorem searchAlt_indep {c : SCtx} {arms : List Ast} {pos : Nat} {regs : Regs}
    {fuel fuel' : Nat} (hpos : pos ≤ c.s.size)
    (hf : ∀ a ∈ arms, suffFuel c.s.size a ≤ fuel)
    (hf' : ∀ a ∈ arms, suffFuel c.s.size a ≤ fuel') :
    searchAlt fuel c arms pos regs = searchAlt fuel' c arms pos regs := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (searchAlt_some hpos hf)
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (searchAlt_some hpos hf')
  have h1 := searchAlt_mono hr (Nat.le_max_left fuel fuel')
  have h2 := searchAlt_mono hr' (Nat.le_max_right fuel fuel')
  rw [hr, hr', h1.symm.trans h2]

/-- A concatenation's children, read at a budget of their own. -/
def evCat (c : SCtx) (kids : List Ast) (pos : Nat) (regs : Regs) :
    Option (List Thread) :=
  searchCat (catFuel c.s.size kids) c kids pos regs

/-- An alternation's branches, likewise. -/
def evAlt (c : SCtx) (arms : List Ast) (pos : Nat) (regs : Regs) :
    Option (List Thread) :=
  searchAlt (catFuel c.s.size arms) c arms pos regs

theorem ev_cat {c : SCtx} {kids : List Ast} {pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size) :
    ev c (.cat kids) pos regs = evCat c kids pos regs := by
  rw [ev, search.eq_def]
  simp only []
  exact searchCat_indep hpos (fun k hk => suffFuel_le_cat hk)
    (fun _ hk => catFuel_ge hk)

theorem ev_alt {c : SCtx} {arms : List Ast} {pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size) :
    ev c (.alt arms) pos regs = evAlt c arms pos regs := by
  rw [ev, search.eq_def]
  simp only []
  exact searchAlt_indep hpos (fun a ha => suffFuel_le_alt ha)
    (fun _ ha => catFuel_ge ha)

theorem evCat_nil {c : SCtx} {pos : Nat} {regs : Regs} :
    evCat c [] pos regs = some [⟨pos, regs⟩] := by
  rw [evCat, searchCat.eq_def]

theorem evCat_cons {c : SCtx} {k : Ast} {rest : List Ast} {pos : Nat}
    {regs : Regs} (hpos : pos ≤ c.s.size) :
    evCat c (k :: rest) pos regs =
      (do
        let heads ← ev c k pos regs
        let tails ← heads.mapM fun t => evCat c rest t.pos t.regs
        pure tails.flatten) := by
  rw [evCat, searchCat.eq_def]
  simp only []
  rw [search_eq_ev hpos (catFuel_ge (by simp))]
  cases hheads : ev c k pos regs with
  | none => rfl
  | some heads =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      refine mapM_flatten_congr fun t ht => ?_
      have hb := ev_pos_le hheads hpos t ht
      exact searchCat_indep hb.2
        (fun x hx => Nat.le_trans (catFuel_ge hx) catFuel_tail)
        (fun _ hx => catFuel_ge hx)

theorem evAlt_nil {c : SCtx} {pos : Nat} {regs : Regs} :
    evAlt c [] pos regs = some [] := by
  rw [evAlt, searchAlt.eq_def]

theorem evAlt_cons {c : SCtx} {arm : Ast} {rest : List Ast} {pos : Nat}
    {regs : Regs} (hpos : pos ≤ c.s.size) :
    evAlt c (arm :: rest) pos regs =
      (do
        let mine ← ev c arm pos regs
        let theirs ← evAlt c rest pos regs
        pure (mine ++ theirs)) := by
  rw [evAlt, searchAlt.eq_def]
  simp only []
  rw [search_eq_ev hpos (catFuel_ge (by simp))]
  rw [show searchAlt (catFuel c.s.size (arm :: rest)) c rest pos regs
      = evAlt c rest pos regs from
    searchAlt_indep hpos
      (fun x hx => Nat.le_trans (catFuel_ge hx) catFuel_tail)
      (fun _ hx => catFuel_ge hx)]

/-- A group, read at its body's budget: the two register writes, and nothing
else the lowering could disturb. -/
theorem ev_grp {c : SCtx} {cap : Nat} {body : Ast} {pos : Nat} {regs : Regs} :
    ev c (.grp cap body) pos regs =
      (ev c body pos (if cap != 0 then regs.set! (2 * cap) pos.toUInt32
        else regs)).map
        (List.map fun t =>
          if cap != 0 then ⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩
          else t) := by
  rw [ev, search.eq_def]
  simp only []
  rw [ev, suffFuel]

theorem ev_rep_zero {c : SCtx} {lo : Nat} {greedy : Bool} {body : Ast}
    {pos : Nat} {regs : Regs} :
    ev c (.rep lo (some 0) greedy body) pos regs = some [⟨pos, regs⟩] := by
  rw [ev, search.eq_def]
  simp only []

theorem ev_rep_one {c : SCtx} {lo : Nat} {greedy : Bool} {body : Ast}
    {pos : Nat} {regs : Regs} (hpos : pos ≤ c.s.size) :
    ev c (.rep lo (some 1) greedy body) pos regs =
      if lo = 1 then ev c body pos regs
      else (ev c body pos regs).map fun taken =>
        if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken := by
  have hb : suffFuel c.s.size body
      ≤ suffFuel c.s.size (.rep lo (some 1) greedy body) := by
    rw [suffFuel]; omega
  rw [ev, search.eq_def]
  simp only []
  rw [search_eq_ev hpos hb]
  split <;> rename_i h
  · rw [if_pos (by simpa using h)]
  · rw [if_neg (by simpa using h)]

/-- The congruence for a repetition: an equivalent body gives an equivalent
round, at every count the rounds can reach. -/
theorem evRep_congr (c : SCtx) (b b' : Ast) (heq : SearchEq c b b')
    (lo : Nat) (hi : Option Nat) (g : Bool) :
    ∀ (d cnt pos : Nat) (regs : Regs),
      repRemaining c.s.size lo hi cnt pos ≤ d → pos ≤ c.s.size →
      evRep c b lo hi g cnt pos regs = evRep c b' lo hi g cnt pos regs := by
  intro d
  induction d with
  | zero =>
      intro cnt pos regs hd hpos
      cases hi with
      | none => simp only [repRemaining] at hd; omega
      | some h =>
          simp only [repRemaining] at hd
          rw [evRep_eq hpos, evRep_eq hpos]
          rw [if_neg (show ¬ cnt < lo by omega), if_neg (show ¬ cnt < lo by omega)]
          rw [if_pos (show Option.any (fun x => decide (cnt ≥ x)) (some h) = true by
                simp only [Option.any_some, decide_eq_true_eq]; omega),
            if_pos (show Option.any (fun x => decide (cnt ≥ x)) (some h) = true by
                simp only [Option.any_some, decide_eq_true_eq]; omega)]
  | succ d ih =>
      intro cnt pos regs hd hpos
      have hround : ∀ _ : cnt < lo ∨ (¬ cnt < lo ∧ ¬ hi.any (cnt ≥ ·) = true),
          repEnter c b lo hi g cnt pos regs
            = repEnter c b' lo hi g cnt pos regs := by
        intro hbranch
        unfold repEnter
        rw [heq pos regs hpos]
        cases htaken : ev c b' pos regs with
        | none => rfl
        | some taken =>
            simp only [Option.bind_eq_bind, Option.bind_some]
            refine mapM_flatten_congr fun t ht => ?_
            have hb := ev_pos_le htaken hpos t ht
            split <;> rename_i hguard
            · rfl
            · have hdesc := repRemaining_descent (c := c) (lo := lo) (hi := hi)
                (cnt := cnt) (pos := pos) (t := t) hb.1 hb.2 hbranch hguard
              exact ih (cnt + 1) t.pos t.regs (by omega) hb.2
      rw [evRep_eq hpos, evRep_eq hpos]
      split <;> rename_i h1
      · rw [hround (Or.inl h1)]
      · split <;> rename_i h2
        · rfl
        · rw [hround (Or.inr ⟨h1, h2⟩)]

/-- Every constructor respects `SearchEq`. -/
theorem SearchEq.grp {c : SCtx} {b b' : Ast} (heq : SearchEq c b b')
    (cap : Nat) : SearchEq c (.grp cap b) (.grp cap b') := by
  intro pos regs hpos
  rw [ev_grp, ev_grp, heq pos _ hpos]

theorem SearchEq.rep {c : SCtx} {b b' : Ast} (heq : SearchEq c b b')
    (lo : Nat) (hi : Option Nat) (g : Bool) :
    SearchEq c (.rep lo hi g b) (.rep lo hi g b') := by
  intro pos regs hpos
  match hi with
  | some 0 => rw [ev_rep_zero, ev_rep_zero]
  | some 1 => rw [ev_rep_one hpos, ev_rep_one hpos, heq pos regs hpos]
  | some (h + 2) =>
      rw [ev_rep_bounded hpos, ev_rep_bounded hpos]
      exact evRep_congr c b b' heq lo (some (h + 2)) g
        (repRemaining c.s.size lo (some (h + 2)) 0 pos) 0 pos regs
        (Nat.le_refl _) hpos
  | none =>
      rw [ev_rep_unbounded hpos, ev_rep_unbounded hpos]
      exact evRep_congr c b b' heq lo none g
        (repRemaining c.s.size lo none 0 pos) 0 pos regs (Nat.le_refl _) hpos

theorem evCat_lower (c : SCtx) : ∀ (kids : List Ast),
    (∀ k ∈ kids, SearchEq c k (lower k)) →
    ∀ (pos : Nat) (regs : Regs), pos ≤ c.s.size →
      evCat c kids pos regs = evCat c (lowerList kids) pos regs := by
  intro kids
  induction kids with
  | nil => intro _ pos regs _; rw [lowerList]
  | cons x xs ih =>
      intro heq pos regs hpos
      rw [lowerList, evCat_cons hpos, evCat_cons hpos]
      rw [heq x (by simp) pos regs hpos]
      cases hheads : ev c (lower x) pos regs with
      | none => rfl
      | some heads =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          refine mapM_flatten_congr fun t ht => ?_
          have hb := ev_pos_le hheads hpos t ht
          exact ih (fun k hk => heq k (by simp [hk])) t.pos t.regs hb.2

theorem evAlt_lower (c : SCtx) : ∀ (arms : List Ast),
    (∀ a ∈ arms, SearchEq c a (lower a)) →
    ∀ (pos : Nat) (regs : Regs), pos ≤ c.s.size →
      evAlt c arms pos regs = evAlt c (lowerList arms) pos regs := by
  intro arms
  induction arms with
  | nil => intro _ pos regs _; rw [lowerList]
  | cons x xs ih =>
      intro heq pos regs hpos
      rw [lowerList, evAlt_cons hpos, evAlt_cons hpos]
      rw [heq x (by simp) pos regs hpos,
        ih (fun a ha => heq a (by simp [ha])) pos regs hpos]

/-- The two splices, gathered: one quantifier and the star form it lowers to
cannot be told apart. -/
theorem lowerRep_searchEq {c : SCtx} {b : Ast} {lo : Nat} {hi : Option Nat}
    {g : Bool} (hcons : hi = none → lo ≠ 0 → Consumes c b) :
    SearchEq c (.rep lo hi g b) (lowerRep lo hi g b) := by
  intro pos regs hpos
  match hi with
  | some 0 => rw [lowerRep]
  | some 1 => rw [lowerRep]
  | some (h + 2) =>
      rw [lowerRep, ev_rep_bounded hpos]
      exact evRep_bounded c b g lo (h + 2) lo 0 pos regs (by omega)
        (Nat.zero_le _) hpos
  | none =>
      rw [lowerRep]
      split <;> rename_i hlo
      · subst hlo; rfl
      · rw [ev_rep_unbounded hpos]
        exact evRep_unbounded c b g lo (hcons rfl hlo) lo 0 pos regs
          (by omega) (Nat.zero_le _) hpos

/-- L-2: the lowering returns the same threads, in the same order, with the
same registers, from every position — for every tree the engine agrees to
lower. -/
theorem lower_searchEq (c : SCtx) (a : Ast) : LowerSafe a = true →
    SearchEq c a (lower a) := by
  match a with
  | .cat kids =>
      intro hsafe pos regs hpos
      rw [LowerSafe] at hsafe
      rw [lower, ev_cat hpos, ev_cat hpos]
      exact evCat_lower c kids
        (fun k hk => lower_searchEq c k (lowerSafe_of_mem hsafe hk)) pos regs hpos
  | .alt arms =>
      intro hsafe pos regs hpos
      rw [LowerSafe] at hsafe
      rw [lower, ev_alt hpos, ev_alt hpos]
      exact evAlt_lower c arms
        (fun k hk => lower_searchEq c k (lowerSafe_of_mem hsafe hk)) pos regs hpos
  | .grp cap body =>
      intro hsafe
      rw [LowerSafe] at hsafe
      rw [lower]
      exact SearchEq.grp (lower_searchEq c body hsafe) cap
  | .rep lo hi greedy body =>
      intro hsafe
      rw [lower]
      by_cases hz : hi = some 0
      · subst hz
        intro pos regs hpos
        rw [lowerRep, ev_rep_zero, ev_rep_zero]
      · rw [LowerSafe] at hsafe
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hsafe
        replace hsafe := hsafe.resolve_left hz
        have hbody := lower_searchEq c body hsafe.2
        refine SearchEq.trans (SearchEq.rep hbody lo hi greedy) ?_
        refine lowerRep_searchEq fun hnone hlo => ?_
        subst hnone
        refine Consumes.congr hbody (consumes_of_not_nullable hsafe.2 ?_)
        rcases hsafe.1.2 with hbound | hnull
        · rcases hbound with hsome | hzero
          · simp at hsome
          · exact absurd hzero hlo
        · simpa using hnull
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      intro _ _ _ _
      rfl
termination_by sizeOf a
decreasing_by
  all_goals
    simp only [Ast.cat.sizeOf_spec, Ast.alt.sizeOf_spec, Ast.grp.sizeOf_spec,
      Ast.rep.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem hk; omega)

end Pcrevera.Spec
