import Pcrevera.Proofs.Refine

/-!
# Deciding the well-formedness the refinement assumes

`Wf` collects the shapes a parse never produces — an alternation with no
branches, a quantifier bound sitting on the u32 sentinel, a capture slot
outside the ovector window — and every refinement statement quantifies over
patterns that satisfy it. That is only an honest hypothesis if the parser
really does satisfy it, and the parser is a tested link until M10, so the
claim belongs where the other tested links live: the corpora.

This file makes `Wf` decidable so the corpus runner can ask it of every
tree the engine's own parser produced, rather than of a restatement that
could drift. The boolean is proved equivalent to the proposition, so a
green corpus run is evidence about the hypothesis the theorems carry.
-/

namespace Pcrevera.Refine

open Pcrevera

/-- The pointwise bridge both decision procedures need: a boolean that
agrees with a predicate on every element agrees with the conjunction the
well-formedness definitions fold up. -/
private theorem attach_iff {α : Type _} {f : α → Bool} {P : α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, (f x = true ↔ P x)) →
      ((l.attach.all (fun x => f x.1) = true) ↔
        l.attach.foldr (fun x acc => P x.1 ∧ acc) True) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons y ys ih =>
      intro h
      simp only [List.attach_cons, List.all_cons, List.all_map, List.foldr_cons,
        List.foldr_map, Bool.and_eq_true]
      have hy := h y (by simp)
      have hrest := ih (fun x hx => h x (by simp [hx]))
      constructor
      · intro hb; exact ⟨hy.mp hb.1, hrest.mp hb.2⟩
      · intro hp; exact ⟨hy.mpr hp.1, hrest.mpr hp.2⟩

/-- The quantifier-bound clause, decided on its own so the recursion below
never has to case on the bound. -/
private theorem hi_bound_iff (hi : Option Nat) :
    hi.all (fun h => h < Ref.none32) = true ↔
      ∀ h, hi = some h → h < Ref.none32 := by
  cases hi <;> simp

/-- `WfAst` as a decision procedure. -/
def wfAstB : Ast → Bool
  | .cat kids => kids.attach.all (fun ⟨k, _⟩ => wfAstB k)
  | .alt arms => !arms.isEmpty && arms.attach.all (fun ⟨a, _⟩ => wfAstB a)
  | .grp _ body => wfAstB body
  | .rep _ hi _ body => hi.all (fun h => h < Ref.none32) && wfAstB body
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => true

/-- `CapsBelow` as a decision procedure. -/
def capsBelowB (novec : Nat) : Ast → Bool
  | .cat kids => kids.attach.all (fun ⟨k, _⟩ => capsBelowB novec k)
  | .alt arms => arms.attach.all (fun ⟨a, _⟩ => capsBelowB novec a)
  | .grp cap body =>
      (cap == 0 || 2 * cap + 1 < novec) && capsBelowB novec body
  | .rep _ _ _ body => capsBelowB novec body
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => true

def wfB (p : Pat) : Bool :=
  wfAstB p.root && capsBelowB (2 * (p.ncap + 1)) p.root

theorem wfAstB_iff (a : Ast) : wfAstB a = true ↔ WfAst a := by
  match a with
  | .cat kids =>
      rw [wfAstB, WfAst]
      exact attach_iff (fun k hk => wfAstB_iff k)
  | .alt arms =>
      rw [wfAstB, WfAst, Bool.and_eq_true]
      have harms := attach_iff (f := wfAstB) (P := WfAst)
        (l := arms) (fun k hk => wfAstB_iff k)
      constructor
      · rintro ⟨hne, hall⟩
        refine ⟨?_, harms.mp hall⟩
        cases arms with
        | nil => simp at hne
        | cons _ _ => simp
      · rintro ⟨hne, hall⟩
        refine ⟨?_, harms.mpr hall⟩
        cases arms with
        | nil => exact absurd rfl hne
        | cons _ _ => simp
  | .grp _ body =>
      rw [wfAstB, WfAst]; exact wfAstB_iff body
  | .rep _ hi _ body =>
      rw [wfAstB, WfAst, Bool.and_eq_true]
      exact and_congr (hi_bound_iff hi) (wfAstB_iff body)
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => simp [wfAstB, WfAst]
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have h := List.sizeOf_lt_of_mem hk; omega)

theorem capsBelowB_iff (novec : Nat) (a : Ast) :
    capsBelowB novec a = true ↔ CapsBelow novec a := by
  match a with
  | .cat kids =>
      rw [capsBelowB, CapsBelow]
      exact attach_iff (fun k hk => capsBelowB_iff novec k)
  | .alt arms =>
      rw [capsBelowB, CapsBelow]
      exact attach_iff (fun k hk => capsBelowB_iff novec k)
  | .grp cap body =>
      rw [capsBelowB, CapsBelow, Bool.and_eq_true]
      have hb := capsBelowB_iff novec body
      constructor
      · rintro ⟨hcap, hbody⟩
        refine ⟨?_, hb.mp hbody⟩
        intro hne
        rcases Bool.or_eq_true .. ▸ hcap with h | h
        · exact absurd (by simpa using h) hne
        · simpa using h
      · rintro ⟨hcap, hbody⟩
        refine ⟨?_, hb.mpr hbody⟩
        by_cases hz : cap = 0
        · simp [hz]
        · simp [hcap hz]
  | .rep _ _ _ body =>
      rw [capsBelowB, CapsBelow]; exact capsBelowB_iff novec body
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB => simp [capsBelowB, CapsBelow]
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have h := List.sizeOf_lt_of_mem hk; omega)

theorem wfB_iff (p : Pat) : wfB p = true ↔ Wf p := by
  rw [wfB, Wf, Bool.and_eq_true, wfAstB_iff, capsBelowB_iff]

end Pcrevera.Refine
