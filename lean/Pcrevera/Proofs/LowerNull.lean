import Pcrevera.Proofs.LowerEval

/-!
# A non-nullable subtree consumes (L-2b's side condition)

The unbounded splice turns on one semantic fact. `x{3,}` stops the moment an
iteration past the minimum matches nothing — that is pcre2's empty-match rule,
and `searchRep` spells it `cnt + 1 ≥ lo` — while the `x x x x*` it lowers to
has no such rule to apply, because a pure star's own copy of the rule fires at
a different count. The two therefore agree exactly when the body cannot match
empty in the first place, and then the rule never fires on either side.

`Nullable` is the engine's syntactic over-approximation of "can match empty".
What has to be proved is the direction the splice leans on: a subtree it calls
non-nullable really does move the position forward, every thread, every time.
The `.rep` case is where the bounds have to be in order — `x{2,1}` would be
called non-nullable while the search offers the empty exit — which is why
`LowerSafe` carries that clause.
-/

namespace Pcrevera.Spec

open Pcrevera

/-- A concatenation is nullable only when every child is. -/
theorem nullableAll_cons {k : Ast} {rest : List Ast} :
    nullableAll (k :: rest) = (Nullable k && nullableAll rest) := by
  rw [nullableAll]

/-- An alternation is nullable as soon as one branch is. -/
theorem nullableAny_cons {a : Ast} {rest : List Ast} :
    nullableAny (a :: rest) = (Nullable a || nullableAny rest) := by
  rw [nullableAny]

theorem lowerSafeAll_cons {k : Ast} {rest : List Ast} :
    lowerSafeAll (k :: rest) = (LowerSafe k && lowerSafeAll rest) := by
  rw [lowerSafeAll]

/-- Every member of a safe list is safe. -/
theorem lowerSafe_of_mem {kids : List Ast} (h : lowerSafeAll kids = true)
    {k : Ast} (hk : k ∈ kids) : LowerSafe k = true := by
  induction kids with
  | nil => cases hk
  | cons x xs ih =>
      rw [lowerSafeAll_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hk with rfl | hmem
      · exact h.1
      · exact ih h.2 hmem

mutual

/-- What the splice needs: a subtree the engine calls non-nullable moves the
position on, whichever way it matched. -/
theorem search_lt_of_not_nullable {fuel : Nat} {c : SCtx} {a : Ast} {pos : Nat}
    {regs : Regs} {r : List Thread}
    (h : search fuel c a pos regs = some r) (hsafe : LowerSafe a = true)
    (hn : Nullable a = false) (hpos : pos ≤ c.s.size) :
    ∀ t ∈ r, pos < t.pos := by
  match a with
  | .cat kids =>
      rw [search.eq_def] at h
      rw [LowerSafe] at hsafe
      rw [Nullable] at hn
      exact searchCat_lt_of_not_nullable h hsafe hn hpos
  | .alt arms =>
      rw [search.eq_def] at h
      rw [LowerSafe] at hsafe
      rw [Nullable] at hn
      exact searchAlt_lt_of_not_nullable h hsafe hn hpos
  | .grp cap body =>
      rw [search.eq_def] at h
      rw [LowerSafe] at hsafe
      rw [Nullable] at hn
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨taken, htaken, rfl⟩ := h
      intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hb := search_lt_of_not_nullable htaken hsafe hn hpos u hu
      split <;> exact hb
  | .rep lo hi greedy body =>
      rw [Nullable] at hn
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn
      obtain ⟨⟨hzero, hone⟩, hbody⟩ := hn
      rw [LowerSafe] at hsafe
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hsafe
      replace hsafe := hsafe.resolve_left hzero
      rw [search.eq_def] at h
      match hi with
      | some 0 => exact absurd rfl hzero
      | some 1 =>
          have hlo : lo = 1 := by
            have := hsafe.1.1
            simp only [Option.all_some, decide_eq_true_eq] at this
            omega
          subst hlo
          simp only [] at h
          rw [if_pos (by simp)] at h
          exact search_lt_of_not_nullable h hsafe.2 hbody hpos
      | none =>
          exact searchRep_lt_of_not_nullable h hsafe.2 hbody
            (Nat.pos_of_ne_zero hone) hpos
      | some (_ + 2) =>
          exact searchRep_lt_of_not_nullable h hsafe.2 hbody
            (Nat.pos_of_ne_zero hone) hpos
  | .nul =>
      rw [Nullable] at hn
      exact absurd hn (by simp)
  | .chr _ | .chrCI _ | .cls _ | .anyNoNL =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        exact Nat.lt_succ_self pos
      · simp at ht
  | .any =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        exact Nat.lt_succ_self pos
      · simp at ht
  | .bsr =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht <;> rename_i hcond
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [bne_iff_ne, ne_eq] at hcond
        show pos < pos + bsrAt c.s pos c.bsr
        omega
      · simp at ht
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [Nullable] at hn
      exact absurd hn (by simp)
termination_by (fuel, sizeOf a)

theorem searchCat_lt_of_not_nullable {fuel : Nat} {c : SCtx} {kids : List Ast}
    {pos : Nat} {regs : Regs} {r : List Thread}
    (h : searchCat fuel c kids pos regs = some r)
    (hsafe : lowerSafeAll kids = true) (hn : nullableAll kids = false)
    (hpos : pos ≤ c.s.size) : ∀ t ∈ r, pos < t.pos := by
  match kids with
  | [] =>
      rw [nullableAll] at hn
      exact absurd hn (by simp)
  | k :: rest =>
      rw [searchCat.eq_def] at h
      rw [lowerSafeAll_cons, Bool.and_eq_true] at hsafe
      rw [nullableAll_cons] at hn
      simp only [Bool.and_eq_false_iff] at hn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨heads, hheads, tails, htails, rfl⟩ := h
      intro t ht
      simp only [List.mem_flatten] at ht
      obtain ⟨l, hl, htl⟩ := ht
      obtain ⟨u, hu, hul⟩ := mapM_mem htails hl
      have hhead := search_pos_le hheads hpos u hu
      rcases hn with hk | hrest
      · have h1 := search_lt_of_not_nullable hheads hsafe.1 hk hpos u hu
        have h2 := searchCat_pos_le hul hhead.2 t htl
        omega
      · have h2 := searchCat_lt_of_not_nullable hul hsafe.2 hrest hhead.2 t htl
        omega
termination_by (fuel, sizeOf kids)

theorem searchAlt_lt_of_not_nullable {fuel : Nat} {c : SCtx} {arms : List Ast}
    {pos : Nat} {regs : Regs} {r : List Thread}
    (h : searchAlt fuel c arms pos regs = some r)
    (hsafe : lowerSafeAll arms = true) (hn : nullableAny arms = false)
    (hpos : pos ≤ c.s.size) : ∀ t ∈ r, pos < t.pos := by
  match arms with
  | [] =>
      rw [searchAlt.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      simp at ht
  | arm :: rest =>
      rw [searchAlt.eq_def] at h
      rw [lowerSafeAll_cons, Bool.and_eq_true] at hsafe
      rw [nullableAny_cons] at hn
      simp only [Bool.or_eq_false_iff] at hn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := h
      intro t ht
      rcases List.mem_append.mp ht with hm | hm
      · exact search_lt_of_not_nullable hmine hsafe.1 hn.1 hpos t hm
      · exact searchAlt_lt_of_not_nullable htheirs hsafe.2 hn.2 hpos t hm
termination_by (fuel, sizeOf arms)

/-- Below the minimum a round has no exit to offer, so every thread it
returns went through the body at least once. -/
theorem searchRep_lt_of_not_nullable {fuel : Nat} {c : SCtx} {body : Ast}
    {lo : Nat} {hi : Option Nat} {greedy : Bool} {cnt pos : Nat} {regs : Regs}
    {r : List Thread}
    (h : searchRep fuel c body lo hi greedy cnt pos regs = some r)
    (hsafe : LowerSafe body = true) (hn : Nullable body = false)
    (hcnt : cnt < lo) (hpos : pos ≤ c.s.size) : ∀ t ∈ r, pos < t.pos := by
  match fuel with
  | 0 =>
      rw [searchRep.eq_def] at h
      exact absurd h (by simp)
  | fuel + 1 =>
      rw [searchRep.eq_def] at h
      simp only [] at h
      rw [if_pos hcnt] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨taken, htaken, onward, honward, rfl⟩ := h
      intro t ht
      simp only [List.mem_flatten] at ht
      obtain ⟨l, hl, htl⟩ := ht
      obtain ⟨u, hu, hul⟩ := mapM_mem honward hl
      have h1 := search_lt_of_not_nullable htaken hsafe hn hpos u hu
      have h2 := (search_pos_le htaken hpos u hu).2
      split at hul
      · simp only [Option.some.injEq] at hul
        subst hul
        simp only [List.mem_singleton] at htl
        subst htl
        exact h1
      · have h3 := searchRep_pos_le hul h2 t htl
        omega
termination_by (fuel, 1 + sizeOf body)

end

/-- The engine's syntactic test, cashed in as the semantic fact the splice
needs. -/
theorem consumes_of_not_nullable {c : SCtx} {b : Ast}
    (hsafe : LowerSafe b = true) (hn : Nullable b = false) : Consumes c b :=
  fun _ _ _ hpos hr t ht => search_lt_of_not_nullable hr hsafe hn hpos t ht

end Pcrevera.Spec
