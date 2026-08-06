import Pcrevera.Proofs.LowerMatch
import Pcrevera.Proofs.CrFirst

/-!
# L-3: what the lowering leaves alone

The splices say the threads are the same. Other things the match loop reads
off the tree have to be the same too, or the equality at `Matches` would not
follow from the equality at `search`.

* `Ast.maxGroup`, because it is the capture count, and the fresh register
  array is sized from it. Copies duplicate group nodes and a maximum does not
  care, which is the whole argument — and no spelling the lowering rewrites
  ends up with zero copies of the body, so the count is never lost.
* `crWalk`, because the bumpalong refusal reads it. Here the argument is
  absorption: `x || (y && x)` is `x`, so a copy in front of a chain of copies
  says nothing the first copy did not already say.
* `WfAst` and `CapsBelow`, because the compiler and the refinement assume
  them, and L-5 hands them a lowered tree.
-/

namespace Pcrevera.Spec

open Pcrevera Pcrevera.CrFirst

/-! ## The capture count -/

theorem maxGroup_cat (kids : List Ast) :
    (Ast.cat kids).maxGroup = kids.foldl (fun acc k => max acc k.maxGroup) 0 := by
  simp only [Ast.maxGroup]
  rw [← List.foldl_attach (f := fun acc k => max acc (Ast.maxGroup k))
    (l := kids) (b := 0)]

theorem maxGroup_alt (arms : List Ast) :
    (Ast.alt arms).maxGroup = arms.foldl (fun acc a => max acc a.maxGroup) 0 := by
  simp only [Ast.maxGroup]
  rw [← List.foldl_attach (f := fun acc a => max acc (Ast.maxGroup a))
    (l := arms) (b := 0)]

private theorem maxFold_acc (l : List Ast) :
    ∀ acc : Nat, l.foldl (fun acc k => max acc k.maxGroup) acc
      = max acc (l.foldl (fun acc k => max acc k.maxGroup) 0) := by
  induction l with
  | nil => intro acc; simp
  | cons k ks ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, ih (max 0 k.maxGroup)]
      omega

theorem maxGroup_cat_nil : (Ast.cat ([] : List Ast)).maxGroup = 0 := by
  rw [maxGroup_cat]; rfl

theorem maxGroup_alt_nil : (Ast.alt ([] : List Ast)).maxGroup = 0 := by
  rw [maxGroup_alt]; rfl

theorem maxGroup_cat_cons (k : Ast) (kids : List Ast) :
    (Ast.cat (k :: kids)).maxGroup = max k.maxGroup (Ast.cat kids).maxGroup := by
  rw [maxGroup_cat, maxGroup_cat, List.foldl_cons, maxFold_acc]
  omega

theorem maxGroup_alt_cons (a : Ast) (arms : List Ast) :
    (Ast.alt (a :: arms)).maxGroup = max a.maxGroup (Ast.alt arms).maxGroup := by
  rw [maxGroup_alt, maxGroup_alt, List.foldl_cons, maxFold_acc]
  omega

theorem maxGroup_cat_pair (x y : Ast) :
    (Ast.cat [x, y]).maxGroup = max x.maxGroup y.maxGroup := by
  rw [maxGroup_cat_cons, maxGroup_cat_cons, maxGroup_cat_nil]
  omega

theorem maxGroup_copies_zero (b t : Ast) : (copies b t 0).maxGroup = t.maxGroup := by
  rw [copies]

theorem maxGroup_copies_succ (b t : Ast) : ∀ n : Nat,
    (copies b t (n + 1)).maxGroup = max b.maxGroup t.maxGroup
  | 0 => by rw [copies, maxGroup_cat_pair, maxGroup_copies_zero]
  | n + 1 => by
      rw [copies, maxGroup_cat_pair, maxGroup_copies_succ b t n]
      omega

theorem maxGroup_optionals_zero (b : Ast) (g : Bool) :
    (optionals b g 0).maxGroup = 0 := by
  rw [optionals]
  simp [Ast.maxGroup]

theorem maxGroup_optionals_succ (b : Ast) (g : Bool) : ∀ m : Nat,
    (optionals b g (m + 1)).maxGroup = b.maxGroup
  | 0 => by
      rw [optionals, Ast.maxGroup, maxGroup_cat_pair, maxGroup_optionals_zero]
      omega
  | m + 1 => by
      rw [optionals, Ast.maxGroup, maxGroup_cat_pair,
        maxGroup_optionals_succ b g m]
      omega

theorem maxGroup_lowerRep (lo : Nat) (hi : Option Nat) (g : Bool) (b : Ast) :
    (lowerRep lo hi g b).maxGroup = b.maxGroup := by
  match hi, lo with
  | some 0, _ => rw [lowerRep, Ast.maxGroup]
  | some 1, _ => rw [lowerRep, Ast.maxGroup]
  | none, 0 => rw [lowerRep, if_pos rfl, Ast.maxGroup]
  | none, lo + 1 =>
      rw [lowerRep, if_neg (by omega), maxGroup_copies_succ, Ast.maxGroup]
      omega
  | some (h + 2), 0 =>
      rw [lowerRep, maxGroup_copies_zero, Nat.sub_zero,
        maxGroup_optionals_succ]
  | some (h + 2), lo + 1 =>
      rw [lowerRep, maxGroup_copies_succ]
      match hd : h + 2 - (lo + 1) with
      | 0 => rw [maxGroup_optionals_zero]; omega
      | m + 1 => rw [maxGroup_optionals_succ]; omega

theorem maxGroup_cat_lowerList (kids : List Ast)
    (h : ∀ k ∈ kids, (lower k).maxGroup = k.maxGroup) :
    (Ast.cat (lowerList kids)).maxGroup = (Ast.cat kids).maxGroup := by
  induction kids with
  | nil => rw [lowerList]
  | cons x xs ih =>
      rw [lowerList, maxGroup_cat_cons, maxGroup_cat_cons, h x (by simp),
        ih fun k hk => h k (by simp [hk])]

theorem maxGroup_alt_lowerList (arms : List Ast)
    (h : ∀ a ∈ arms, (lower a).maxGroup = a.maxGroup) :
    (Ast.alt (lowerList arms)).maxGroup = (Ast.alt arms).maxGroup := by
  induction arms with
  | nil => rw [lowerList]
  | cons x xs ih =>
      rw [lowerList, maxGroup_alt_cons, maxGroup_alt_cons, h x (by simp),
        ih fun a ha => h a (by simp [ha])]

theorem maxGroup_lower (a : Ast) : (lower a).maxGroup = a.maxGroup := by
  match a with
  | .cat kids =>
      rw [lower]
      exact maxGroup_cat_lowerList kids fun k hk => maxGroup_lower k
  | .alt arms =>
      rw [lower]
      exact maxGroup_alt_lowerList arms fun k hk => maxGroup_lower k
  | .grp cap body =>
      rw [lower, Ast.maxGroup, Ast.maxGroup, maxGroup_lower body]
  | .rep lo hi greedy body =>
      rw [lower, maxGroup_lowerRep, Ast.maxGroup, maxGroup_lower body]
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => rfl
termination_by sizeOf a
decreasing_by
  all_goals
    simp only [Ast.cat.sizeOf_spec, Ast.alt.sizeOf_spec, Ast.grp.sizeOf_spec,
      Ast.rep.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem hk; omega)

/-! ## The bumpalong bit -/

theorem crWalk_cat_pair (x y : Ast) :
    crWalk (.cat [x, y]) =
      ((crWalk x).1 || ((crWalk x).2 && (crWalk y).1),
       (crWalk x).2 && (crWalk y).2) := by
  refine Prod.ext ?_ ?_
  · rw [crWalk_cat_cons₁, crWalk_cat_cons₁, crWalk_cat_nil]
    simp
  · rw [crWalk_cat_cons₂, crWalk_cat_cons₂, crWalk_cat_nil]
    simp

theorem crWalk_copies_zero (b t : Ast) : crWalk (copies b t 0) = crWalk t := by
  rw [copies]

theorem crWalk_copies_succ (b t : Ast) : ∀ n : Nat,
    crWalk (copies b t (n + 1)) =
      ((crWalk b).1 || ((crWalk b).2 && (crWalk t).1),
       (crWalk b).2 && (crWalk t).2)
  | 0 => by rw [copies, crWalk_cat_pair, crWalk_copies_zero]
  | n + 1 => by
      rw [copies, crWalk_cat_pair, crWalk_copies_succ b t n]
      obtain ⟨cb, tb⟩ := crWalk b
      obtain ⟨ct, tt⟩ := crWalk t
      cases cb <;> cases tb <;> cases ct <;> cases tt <;> rfl

theorem crWalk_optionals_zero (b : Ast) (g : Bool) :
    crWalk (optionals b g 0) = (false, true) := by
  rw [optionals]
  simp [crWalk]

theorem crWalk_optionals_succ (b : Ast) (g : Bool) : ∀ m : Nat,
    crWalk (optionals b g (m + 1)) = ((crWalk b).1, true)
  | 0 => by
      rw [optionals, crWalk_rep_opt (by simp), crWalk_cat_pair,
        crWalk_optionals_zero]
      obtain ⟨cb, tb⟩ := crWalk b
      cases cb <;> cases tb <;> rfl
  | m + 1 => by
      rw [optionals, crWalk_rep_opt (by simp), crWalk_cat_pair,
        crWalk_optionals_succ b g m]
      obtain ⟨cb, tb⟩ := crWalk b
      cases cb <;> cases tb <;> rfl

theorem crWalk_lowerRep (lo : Nat) (hi : Option Nat) (g : Bool) (b : Ast) :
    crWalk (lowerRep lo hi g b) = crWalk (.rep lo hi g b) := by
  match hi, lo with
  | some 0, _ => rw [lowerRep]
  | some 1, _ => rw [lowerRep]
  | none, 0 => rw [lowerRep, if_pos rfl]
  | none, lo + 1 =>
      rw [lowerRep, if_neg (by omega), crWalk_copies_succ,
        crWalk_rep_many (by simp) (by simp),
        crWalk_rep_many (by simp) (by simp)]
      obtain ⟨cb, tb⟩ := crWalk b
      cases cb <;> cases tb <;> rfl
  | some (h + 2), 0 =>
      rw [lowerRep, crWalk_copies_zero, Nat.sub_zero, crWalk_optionals_succ,
        crWalk_rep_many (by simp) (by simp)]
      simp
  | some (h + 2), lo + 1 =>
      rw [lowerRep, crWalk_copies_succ, crWalk_rep_many (by simp) (by simp)]
      match hd : h + 2 - (lo + 1) with
      | 0 =>
          rw [crWalk_optionals_zero]
          obtain ⟨cb, tb⟩ := crWalk b
          cases cb <;> cases tb <;> rfl
      | m + 1 =>
          rw [crWalk_optionals_succ]
          obtain ⟨cb, tb⟩ := crWalk b
          cases cb <;> cases tb <;> rfl

theorem crWalk_cat_lowerList (kids : List Ast)
    (h : ∀ k ∈ kids, crWalk (lower k) = crWalk k) :
    crWalk (.cat (lowerList kids)) = crWalk (.cat kids) := by
  induction kids with
  | nil => rw [lowerList]
  | cons x xs ih =>
      refine Prod.ext ?_ ?_
      · rw [lowerList, crWalk_cat_cons₁, crWalk_cat_cons₁, h x (by simp),
          ih fun k hk => h k (by simp [hk])]
      · rw [lowerList, crWalk_cat_cons₂, crWalk_cat_cons₂, h x (by simp),
          ih fun k hk => h k (by simp [hk])]

theorem crWalk_alt_lowerList (arms : List Ast)
    (h : ∀ a ∈ arms, crWalk (lower a) = crWalk a) :
    crWalk (.alt (lowerList arms)) = crWalk (.alt arms) := by
  induction arms with
  | nil => rw [lowerList]
  | cons x xs ih =>
      refine Prod.ext ?_ ?_
      · rw [lowerList, crWalk_alt_cons₁, crWalk_alt_cons₁, h x (by simp),
          ih fun a ha => h a (by simp [ha])]
      · rw [lowerList, crWalk_alt_cons₂, crWalk_alt_cons₂, h x (by simp),
          ih fun a ha => h a (by simp [ha])]

theorem crWalk_lower (a : Ast) : crWalk (lower a) = crWalk a := by
  match a with
  | .cat kids =>
      rw [lower]
      exact crWalk_cat_lowerList kids fun k hk => crWalk_lower k
  | .alt arms =>
      rw [lower]
      exact crWalk_alt_lowerList arms fun k hk => crWalk_lower k
  | .grp cap body =>
      rw [lower, crWalk_grp, crWalk_grp, crWalk_lower body]
  | .rep lo hi greedy body =>
      rw [lower, crWalk_lowerRep]
      match hi with
      | some 0 => rw [crWalk_rep_zero, crWalk_rep_zero]
      | some 1 =>
          match hlo : lo with
          | 1 => rw [crWalk_rep_one, crWalk_rep_one, crWalk_lower body]
          | 0 => rw [crWalk_rep_opt (by simp), crWalk_rep_opt (by simp),
                    crWalk_lower body]
          | l + 2 => rw [crWalk_rep_opt (by simp), crWalk_rep_opt (by simp),
                        crWalk_lower body]
      | none =>
          rw [crWalk_rep_many (by simp) (by simp),
            crWalk_rep_many (by simp) (by simp), crWalk_lower body]
      | some (h + 2) =>
          rw [crWalk_rep_many (by simp) (by simp),
            crWalk_rep_many (by simp) (by simp), crWalk_lower body]
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => rfl
termination_by sizeOf a
decreasing_by
  all_goals
    simp only [Ast.cat.sizeOf_spec, Ast.alt.sizeOf_spec, Ast.grp.sizeOf_spec,
      Ast.rep.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem hk; omega)

end Pcrevera.Spec
