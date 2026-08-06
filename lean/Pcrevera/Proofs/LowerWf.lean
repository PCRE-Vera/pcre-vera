import Pcrevera.Proofs.LowerPat
import Pcrevera.Proofs.Refine

/-!
# L-3, the rest: the lowering keeps a tree well formed

`WfAst` and `CapsBelow` are what the refinement assumes of a tree before it
compiles one, so L-5 cannot hand `R.compile` a lowered tree without them.
Neither is hard and both are worth writing down for the same reason: the
lowering *duplicates* subtrees, and a property that held once has to hold in
every copy.

For `CapsBelow` that is the whole argument — a copied group carries the same
capture number, and the bound it satisfies is a fact about that number.

For `WfAst` there is one thing to check rather than inherit. The quantifier
bounds the lowering introduces are its own, not the ones it read: the nested
optionals are `{0,1}` and the tail of an unbounded splice is `{0,}`. Both sit
inside `maxQuant` with room to spare, which is why the clause survives a
rewrite that does not preserve the numbers it was written about.
-/

namespace Pcrevera.Spec

open Pcrevera Pcrevera.Refine

/-- The `attach` fold of `WfAst` and `CapsBelow`, traded for the quantifier
everything downstream actually wants. -/
theorem attach_foldr_iff {α : Type _} {P : α → Prop} :
    ∀ {l : List α},
      l.attach.foldr (fun x acc => P x.1 ∧ acc) True ↔ ∀ x ∈ l, P x := by
  intro l
  induction l with
  | nil => simp
  | cons y ys ih =>
      simp only [List.attach_cons, List.foldr_cons, List.foldr_map, ih]
      constructor
      · intro h x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h.1
        · exact h.2 x hx'
      · intro h
        exact ⟨h y (by simp), fun x hx => h x (by simp [hx])⟩

/-! ## Well-formedness -/

theorem wfAst_cat {kids : List Ast} :
    WfAst (.cat kids) ↔ ∀ k ∈ kids, WfAst k := by
  rw [WfAst]; exact attach_foldr_iff

theorem wfAst_alt {arms : List Ast} :
    WfAst (.alt arms) ↔ arms ≠ [] ∧ ∀ a ∈ arms, WfAst a := by
  rw [WfAst]
  exact and_congr_right fun _ => attach_foldr_iff

theorem wfAst_cat_pair {x y : Ast} (hx : WfAst x) (hy : WfAst y) :
    WfAst (.cat [x, y]) := by
  rw [wfAst_cat]
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact hx
  · rcases List.mem_cons.mp hk with rfl | hk
    · exact hy
    · cases hk

theorem wfAst_copies {b t : Ast} (hb : WfAst b) (ht : WfAst t) :
    ∀ n : Nat, WfAst (copies b t n)
  | 0 => by rw [copies]; exact ht
  | n + 1 => by
      rw [copies]
      exact wfAst_cat_pair hb (wfAst_copies hb ht n)

theorem wfAst_optionals {b : Ast} (hb : WfAst b) (g : Bool) :
    ∀ m : Nat, WfAst (optionals b g m)
  | 0 => by rw [optionals]; simp [WfAst]
  | m + 1 => by
      rw [optionals, WfAst]
      refine ⟨⟨by simp [maxQuant], ?_⟩, ?_⟩
      · intro h hh
        simp only [Option.some.injEq] at hh
        subst hh
        simp [maxQuant]
      · exact wfAst_cat_pair hb (wfAst_optionals hb g m)

theorem wfAst_lowerRep {lo : Nat} {hi : Option Nat} {g : Bool} {b : Ast}
    (h : WfAst (.rep lo hi g b)) : WfAst (lowerRep lo hi g b) := by
  rw [WfAst] at h
  match hi, lo with
  | some 0, _ => rw [lowerRep, WfAst]; exact h
  | some 1, _ => rw [lowerRep, WfAst]; exact h
  | none, 0 => rw [lowerRep, if_pos rfl, WfAst]; exact ⟨⟨by simp [maxQuant], by simp⟩, h.2⟩
  | none, lo + 1 =>
      rw [lowerRep, if_neg (by omega)]
      refine wfAst_copies h.2 ?_ _
      rw [WfAst]
      exact ⟨⟨by simp [maxQuant], by simp⟩, h.2⟩
  | some (hh + 2), _ =>
      rw [lowerRep]
      exact wfAst_copies h.2 (wfAst_optionals h.2 g _) _

theorem wfAst_lowerList {kids : List Ast}
    (h : ∀ k ∈ kids, WfAst (lower k)) : ∀ k ∈ lowerList kids, WfAst k := by
  induction kids with
  | nil => intro k hk; rw [lowerList] at hk; cases hk
  | cons x xs ih =>
      intro k hk
      rw [lowerList] at hk
      rcases List.mem_cons.mp hk with rfl | hk'
      · exact h x (by simp)
      · exact ih (fun y hy => h y (by simp [hy])) k hk'

theorem lowerList_ne_nil {arms : List Ast} (h : arms ≠ []) :
    lowerList arms ≠ [] := by
  cases arms with
  | nil => exact absurd rfl h
  | cons x xs => rw [lowerList]; simp

theorem wfAst_lower (a : Ast) : WfAst a → WfAst (lower a) := by
  match a with
  | .cat kids =>
      intro h
      rw [wfAst_cat] at h
      rw [lower, wfAst_cat]
      exact wfAst_lowerList fun k hk => wfAst_lower k (h k hk)
  | .alt arms =>
      intro h
      rw [wfAst_alt] at h
      rw [lower, wfAst_alt]
      exact ⟨lowerList_ne_nil h.1,
        wfAst_lowerList fun k hk => wfAst_lower k (h.2 k hk)⟩
  | .grp cap body =>
      intro h
      rw [WfAst] at h
      rw [lower, WfAst]
      exact wfAst_lower body h
  | .rep lo hi greedy body =>
      intro h
      rw [WfAst] at h
      rw [lower]
      refine wfAst_lowerRep ?_
      rw [WfAst]
      exact ⟨h.1, wfAst_lower body h.2⟩
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => intro h; exact h
termination_by sizeOf a
decreasing_by
  all_goals
    simp only [Ast.cat.sizeOf_spec, Ast.alt.sizeOf_spec, Ast.grp.sizeOf_spec,
      Ast.rep.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem hk; omega)

/-! ## Capture slots -/

theorem capsBelow_cat {novec : Nat} {kids : List Ast} :
    CapsBelow novec (.cat kids) ↔ ∀ k ∈ kids, CapsBelow novec k := by
  rw [CapsBelow]; exact attach_foldr_iff

theorem capsBelow_alt {novec : Nat} {arms : List Ast} :
    CapsBelow novec (.alt arms) ↔ ∀ a ∈ arms, CapsBelow novec a := by
  rw [CapsBelow]; exact attach_foldr_iff

theorem capsBelow_cat_pair {novec : Nat} {x y : Ast}
    (hx : CapsBelow novec x) (hy : CapsBelow novec y) :
    CapsBelow novec (.cat [x, y]) := by
  rw [capsBelow_cat]
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact hx
  · rcases List.mem_cons.mp hk with rfl | hk
    · exact hy
    · cases hk

theorem capsBelow_copies {novec : Nat} {b t : Ast} (hb : CapsBelow novec b)
    (ht : CapsBelow novec t) : ∀ n : Nat, CapsBelow novec (copies b t n)
  | 0 => by rw [copies]; exact ht
  | n + 1 => by
      rw [copies]
      exact capsBelow_cat_pair hb (capsBelow_copies hb ht n)

theorem capsBelow_optionals {novec : Nat} {b : Ast} (hb : CapsBelow novec b)
    (g : Bool) : ∀ m : Nat, CapsBelow novec (optionals b g m)
  | 0 => by rw [optionals]; simp [CapsBelow]
  | m + 1 => by
      rw [optionals, CapsBelow]
      exact capsBelow_cat_pair hb (capsBelow_optionals hb g m)

theorem capsBelow_lowerRep {novec lo : Nat} {hi : Option Nat} {g : Bool}
    {b : Ast} (h : CapsBelow novec b) : CapsBelow novec (lowerRep lo hi g b) := by
  match hi, lo with
  | some 0, _ => rw [lowerRep, CapsBelow]; exact h
  | some 1, _ => rw [lowerRep, CapsBelow]; exact h
  | none, 0 => rw [lowerRep, if_pos rfl, CapsBelow]; exact h
  | none, lo + 1 =>
      rw [lowerRep, if_neg (by omega)]
      refine capsBelow_copies h ?_ _
      rw [CapsBelow]
      exact h
  | some (hh + 2), _ =>
      rw [lowerRep]
      exact capsBelow_copies h (capsBelow_optionals h g _) _

theorem capsBelow_lowerList {novec : Nat} {kids : List Ast}
    (h : ∀ k ∈ kids, CapsBelow novec (lower k)) :
    ∀ k ∈ lowerList kids, CapsBelow novec k := by
  induction kids with
  | nil => intro k hk; rw [lowerList] at hk; cases hk
  | cons x xs ih =>
      intro k hk
      rw [lowerList] at hk
      rcases List.mem_cons.mp hk with rfl | hk'
      · exact h x (by simp)
      · exact ih (fun y hy => h y (by simp [hy])) k hk'

theorem capsBelow_lower (novec : Nat) (a : Ast) :
    CapsBelow novec a → CapsBelow novec (lower a) := by
  match a with
  | .cat kids =>
      intro h
      rw [capsBelow_cat] at h
      rw [lower, capsBelow_cat]
      exact capsBelow_lowerList fun k hk => capsBelow_lower novec k (h k hk)
  | .alt arms =>
      intro h
      rw [capsBelow_alt] at h
      rw [lower, capsBelow_alt]
      exact capsBelow_lowerList fun k hk => capsBelow_lower novec k (h k hk)
  | .grp cap body =>
      intro h
      rw [CapsBelow] at h
      rw [lower, CapsBelow]
      exact ⟨h.1, capsBelow_lower novec body h.2⟩
  | .rep lo hi greedy body =>
      intro h
      rw [CapsBelow] at h
      rw [lower]
      exact capsBelow_lowerRep (capsBelow_lower novec body h)
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => intro h; exact h
termination_by sizeOf a
decreasing_by
  all_goals
    simp only [Ast.cat.sizeOf_spec, Ast.alt.sizeOf_spec, Ast.grp.sizeOf_spec,
      Ast.rep.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem hk; omega)

/-- `Covered`, which section 6's obligation list also names, comes along for
free rather than by a preservation lemma of its own: it is a consequence of
`WfAst`, and nothing asks it of a tree that is not well formed. -/
theorem covered_lower {a : Ast} (h : WfAst a) : Covered (lower a) :=
  WfAst.covered (wfAst_lower a h)

/-- L-3, gathered at the pattern: a well-formed tree lowers to a well-formed
one. Only that direction — the converse is false, since a quantifier whose
high sits past `maxQuant` is not well formed while the chain of `{0,1}`
repetitions it would lower to is. -/
theorem wf_lowered {p : Pat} (h : Wf p) : Wf p.lowered := by
  obtain ⟨hwf, hcaps⟩ := h
  refine ⟨wfAst_lower p.root hwf, ?_⟩
  rw [show p.lowered.ncap = p.ncap from lowered_ncap p]
  exact capsBelow_lower _ p.root hcaps

end Pcrevera.Spec
