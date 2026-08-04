import Pcrevera.Spec.Match

/-!
# Totality of the search (S-3, S-4)

The fuel-indexed search of `Match.lean` answers `none` only when fuel runs
out, and `suffFuel` was written to make that impossible. This file proves it:
the search is monotone in fuel — a `some` answer never changes when fuel
grows — and at the sufficient fuel every answer is `some`. Together they let
S-4 read the fuel out of the story: `Matches` is `matchesF` evaluated at the
sufficient fuel, total by construction, and `matches_stable` says any larger
fuel gives the same answer.

The proofs walk the same mutual recursion the search does. The one real
invariant is `searchRep_some`'s budget: a repetition round hands its tail a
strictly smaller `repRemaining`, because a round below the minimum raises the
count, a bounded round raises it toward the bound, and an unbounded round
past the minimum either consumed a byte or was ended on the spot by the
empty-match rule. Everything else is bookkeeping over `Option` and `mapM`.
-/


namespace Pcrevera.Spec

open Pcrevera

/-- `mapM` over `Option` keeps a `some` answer when every element does. -/
theorem mapM_mono {α β : Type} {f g : α → Option β} {l : List α} {r : List β}
    (hfg : ∀ x ∈ l, ∀ b, f x = some b → g x = some b)
    (h : l.mapM f = some r) : l.mapM g = some r := by
  induction l generalizing r with
  | nil => simpa using h
  | cons x xs ih =>
      rw [List.mapM_cons] at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      exact ⟨b, hfg x (by simp) b hb,
        bs, ih (fun y hy => hfg y (by simp [hy])) hbs, rfl⟩

/-- `mapM` over `Option` is `some` when every element is. -/
theorem mapM_isSome {α β : Type} {f : α → Option β} {l : List α}
    (h : ∀ x ∈ l, (f x).isSome) : (l.mapM f).isSome := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.mapM_cons]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x (by simp))
      obtain ⟨bs, hbs⟩ :=
        Option.isSome_iff_exists.mp (ih fun y hy => h y (by simp [hy]))
      simp [hb, hbs]

/-- Every element of a successful `mapM`'s answer came from some input. -/
theorem mapM_mem {α β : Type} {f : α → Option β} {l : List α} {r : List β}
    (h : l.mapM f = some r) {b : β} (hb : b ∈ r) : ∃ x ∈ l, f x = some b := by
  induction l generalizing r with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; simp at hb
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c, hc, bs, hbs, rfl⟩ := h
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact ⟨x, by simp, hc⟩
      · obtain ⟨y, hy, hyb⟩ := ih hbs hmem
        exact ⟨y, by simp [hy], hyb⟩

theorem le_foldl_add {α : Type} (f : α → Nat) (l : List α) (acc : Nat) :
    acc ≤ l.foldl (fun a y => a + f y) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => exact Nat.le_trans (Nat.le_add_right acc (f x)) (ih (acc + f x))

theorem mem_le_foldl_add {α : Type} (f : α → Nat) {x : α} {l : List α}
    (hx : x ∈ l) (acc : Nat) : f x ≤ l.foldl (fun a y => a + f y) acc := by
  induction l generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact Nat.le_trans (Nat.le_add_left _ _) (le_foldl_add f ys (acc + f x))
      · exact ih hmem _

/-- A concatenation's budget covers each child's. -/
theorem suffFuel_le_cat {n : Nat} {kids : List Ast} {k : Ast} (hk : k ∈ kids) :
    suffFuel n k ≤ suffFuel n (.cat kids) := by
  rw [suffFuel]
  exact mem_le_foldl_add (fun t => suffFuel n t.1) (List.mem_attach kids ⟨k, hk⟩) 0

/-- An alternation's budget covers each arm's. -/
theorem suffFuel_le_alt {n : Nat} {arms : List Ast} {a : Ast} (ha : a ∈ arms) :
    suffFuel n a ≤ suffFuel n (.alt arms) := by
  rw [suffFuel]
  exact mem_le_foldl_add (fun t => suffFuel n t.1) (List.mem_attach arms ⟨a, ha⟩) 0

/-- What `\R` eats never runs past the subject: every branch of `bsrAt`
guards the bytes it reads. -/
theorem bsrAt_le {s : ByteArray} {pos : Nat} (bsr : BsrType)
    (h : pos ≤ s.size) : pos + bsrAt s pos bsr ≤ s.size := by
  unfold bsrAt
  simp only []
  repeat' split
  all_goals first
    | omega
    | (rename_i hguard
       simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
       omega)

mutual

/-- More fuel never changes a `some` answer of `search`. -/
theorem search_mono {fuel fuel' : Nat} {c : SCtx} {a : Ast} {pos : Nat}
    {regs : Regs} {r : List Thread}
    (h : search fuel c a pos regs = some r) (hle : fuel ≤ fuel') :
    search fuel' c a pos regs = some r := by
  match a with
  | .cat kids =>
      rw [search.eq_def] at h ⊢
      exact searchCat_mono h hle
  | .alt arms =>
      rw [search.eq_def] at h ⊢
      exact searchAlt_mono h hle
  | .grp cap body =>
      rw [search.eq_def] at h ⊢
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨taken, htaken, rfl⟩ := h
      exact ⟨taken, search_mono htaken hle, rfl⟩
  | .rep lo hi greedy body =>
      rw [search.eq_def] at h ⊢
      match hi with
      | some 0 => exact h
      | some 1 =>
          simp only [] at h ⊢
          split at h <;> rename_i hlo
          · rw [if_pos hlo]
            exact search_mono h hle
          · rw [if_neg hlo]
            simp only [Option.map_eq_some_iff] at h ⊢
            obtain ⟨taken, htaken, rfl⟩ := h
            exact ⟨taken, search_mono htaken hle, rfl⟩
      | none => exact searchRep_mono h hle
      | some (_ + 2) => exact searchRep_mono h hle
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [search.eq_def] at h ⊢
      exact h
termination_by (fuel, sizeOf a)

/-- More fuel never changes a `some` answer of `searchCat`. -/
theorem searchCat_mono {fuel fuel' : Nat} {c : SCtx} {kids : List Ast}
    {pos : Nat} {regs : Regs} {r : List Thread}
    (h : searchCat fuel c kids pos regs = some r) (hle : fuel ≤ fuel') :
    searchCat fuel' c kids pos regs = some r := by
  match kids with
  | [] =>
      rw [searchCat.eq_def] at h ⊢
      exact h
  | k :: rest =>
      rw [searchCat.eq_def] at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨heads, hheads, tails, htails, rfl⟩ := h
      exact ⟨heads, search_mono hheads hle, tails,
        mapM_mono (fun t _ tl htl => searchCat_mono htl hle) htails, rfl⟩
termination_by (fuel, sizeOf kids)

/-- More fuel never changes a `some` answer of `searchAlt`. -/
theorem searchAlt_mono {fuel fuel' : Nat} {c : SCtx} {arms : List Ast}
    {pos : Nat} {regs : Regs} {r : List Thread}
    (h : searchAlt fuel c arms pos regs = some r) (hle : fuel ≤ fuel') :
    searchAlt fuel' c arms pos regs = some r := by
  match arms with
  | [] =>
      rw [searchAlt.eq_def] at h ⊢
      exact h
  | arm :: rest =>
      rw [searchAlt.eq_def] at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := h
      exact ⟨mine, search_mono hmine hle, theirs,
        searchAlt_mono htheirs hle, rfl⟩
termination_by (fuel, sizeOf arms)

/-- More fuel never changes a `some` answer of `searchRep`. -/
theorem searchRep_mono {fuel fuel' : Nat} {c : SCtx} {body : Ast} {lo : Nat}
    {hi : Option Nat} {greedy : Bool} {cnt pos : Nat} {regs : Regs}
    {r : List Thread}
    (h : searchRep fuel c body lo hi greedy cnt pos regs = some r)
    (hle : fuel ≤ fuel') :
    searchRep fuel' c body lo hi greedy cnt pos regs = some r := by
  match fuel with
  | 0 =>
      rw [searchRep.eq_def] at h
      exact absurd h (by simp)
  | fuel + 1 =>
      cases fuel' with
      | zero => exact absurd hle (by omega)
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          rw [searchRep.eq_def] at h ⊢
          simp only [] at h ⊢
          have henter : ∀ v,
              (do
                let taken ← search fuel c body pos regs
                let onward ← taken.mapM fun t =>
                  if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                    pure [t]
                  else
                    searchRep fuel c body lo hi greedy (cnt + 1) t.pos t.regs
                pure onward.flatten : Option (List Thread)) = some v →
              (do
                let taken ← search fuel' c body pos regs
                let onward ← taken.mapM fun t =>
                  if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                    pure [t]
                  else
                    searchRep fuel' c body lo hi greedy (cnt + 1) t.pos t.regs
                pure onward.flatten : Option (List Thread)) = some v := by
            intro v hv
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.pure_def, Option.some.injEq] at hv ⊢
            obtain ⟨taken, htaken, onward, honward, rfl⟩ := hv
            refine ⟨taken, search_mono htaken hle', onward, ?_, rfl⟩
            refine mapM_mono (fun t _ b hb => ?_) honward
            split at hb <;> rename_i hguard
            · rwa [if_pos hguard]
            · rw [if_neg hguard]
              exact searchRep_mono hb hle'
          split at h <;> rename_i h1
          · rw [if_pos h1]
            exact henter r h
          · split at h <;> rename_i h2
            · rw [if_neg h1, if_pos h2]
              exact h
            · rw [if_neg h1, if_neg h2]
              obtain ⟨taken, htaken, hres⟩ := Option.bind_eq_some_iff.mp h
              exact Option.bind_eq_some_iff.mpr ⟨taken, henter taken htaken, hres⟩
termination_by (fuel, 1 + sizeOf body)

end

mutual

/-- Threads of a `some` answer stay inside the subject: each leaf consumes
only under a `pos < n` guard, and never moves backward. -/
theorem search_pos_le {fuel : Nat} {c : SCtx} {a : Ast} {pos : Nat}
    {regs : Regs} {r : List Thread}
    (h : search fuel c a pos regs = some r) (hpos : pos ≤ c.s.size) :
    ∀ t ∈ r, pos ≤ t.pos ∧ t.pos ≤ c.s.size := by
  match a with
  | .cat kids =>
      rw [search.eq_def] at h
      exact searchCat_pos_le h hpos
  | .alt arms =>
      rw [search.eq_def] at h
      exact searchAlt_pos_le h hpos
  | .grp cap body =>
      rw [search.eq_def] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨taken, htaken, rfl⟩ := h
      intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hb := search_pos_le htaken hpos u hu
      split <;> exact hb
  | .rep lo hi greedy body =>
      rw [search.eq_def] at h
      match hi with
      | some 0 =>
          simp only [Option.some.injEq] at h
          subst h
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨Nat.le_refl _, hpos⟩
      | some 1 =>
          simp only [] at h
          split at h
          · exact search_pos_le h hpos
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨taken, htaken, rfl⟩ := h
            intro t ht
            have hmem : t ∈ taken ∨ t = ⟨pos, regs⟩ := by
              split at ht
              · simpa only [List.mem_append, List.mem_singleton] using ht
              · rcases List.mem_cons.mp ht with h' | h'
                · exact Or.inr h'
                · exact Or.inl h'
            rcases hmem with hmem | rfl
            · exact search_pos_le htaken hpos t hmem
            · exact ⟨Nat.le_refl _, hpos⟩
      | none => exact searchRep_pos_le h hpos
      | some (_ + 2) => exact searchRep_pos_le h hpos
  | .nul =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨Nat.le_refl _, hpos⟩
  | .chr _ | .chrCI _ | .cls _ | .anyNoNL =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht <;> rename_i hcond
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨Nat.le_add_right _ _, hcond.1⟩
      · simp at ht
  | .any =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht <;> rename_i hcond
      · simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨Nat.le_add_right _ _, hcond⟩
      · simp at ht
  | .bsr =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨Nat.le_add_right _ _, bsrAt_le c.bsr hpos⟩
      · simp at ht
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [search.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨Nat.le_refl _, hpos⟩
      · simp at ht
termination_by (fuel, sizeOf a)

theorem searchCat_pos_le {fuel : Nat} {c : SCtx} {kids : List Ast}
    {pos : Nat} {regs : Regs} {r : List Thread}
    (h : searchCat fuel c kids pos regs = some r) (hpos : pos ≤ c.s.size) :
    ∀ t ∈ r, pos ≤ t.pos ∧ t.pos ≤ c.s.size := by
  match kids with
  | [] =>
      rw [searchCat.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨Nat.le_refl _, hpos⟩
  | _ :: rest =>
      rw [searchCat.eq_def] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨heads, hheads, tails, htails, rfl⟩ := h
      intro t ht
      simp only [List.mem_flatten] at ht
      obtain ⟨l, hl, htl⟩ := ht
      obtain ⟨u, hu, hul⟩ := mapM_mem htails hl
      have h1 := search_pos_le hheads hpos u hu
      have h2 := searchCat_pos_le hul h1.2 t htl
      exact ⟨Nat.le_trans h1.1 h2.1, h2.2⟩
termination_by (fuel, sizeOf kids)

theorem searchAlt_pos_le {fuel : Nat} {c : SCtx} {arms : List Ast}
    {pos : Nat} {regs : Regs} {r : List Thread}
    (h : searchAlt fuel c arms pos regs = some r) (hpos : pos ≤ c.s.size) :
    ∀ t ∈ r, pos ≤ t.pos ∧ t.pos ≤ c.s.size := by
  match arms with
  | [] =>
      rw [searchAlt.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      simp at ht
  | _ :: rest =>
      rw [searchAlt.eq_def] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := h
      intro t ht
      rcases List.mem_append.mp ht with hm | hm
      · exact search_pos_le hmine hpos t hm
      · exact searchAlt_pos_le htheirs hpos t hm
termination_by (fuel, sizeOf arms)

theorem searchRep_pos_le {fuel : Nat} {c : SCtx} {body : Ast} {lo : Nat}
    {hi : Option Nat} {greedy : Bool} {cnt pos : Nat} {regs : Regs}
    {r : List Thread}
    (h : searchRep fuel c body lo hi greedy cnt pos regs = some r)
    (hpos : pos ≤ c.s.size) :
    ∀ t ∈ r, pos ≤ t.pos ∧ t.pos ≤ c.s.size := by
  match fuel with
  | 0 =>
      rw [searchRep.eq_def] at h
      exact absurd h (by simp)
  | fuel + 1 =>
      rw [searchRep.eq_def] at h
      simp only [] at h
      have henter : ∀ v,
          (do
            let taken ← search fuel c body pos regs
            let onward ← taken.mapM fun t =>
              if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                pure [t]
              else
                searchRep fuel c body lo hi greedy (cnt + 1) t.pos t.regs
            pure onward.flatten : Option (List Thread)) = some v →
          ∀ t ∈ v, pos ≤ t.pos ∧ t.pos ≤ c.s.size := by
        intro v hv
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hv
        obtain ⟨taken, htaken, onward, honward, rfl⟩ := hv
        intro t ht
        simp only [List.mem_flatten] at ht
        obtain ⟨l, hl, htl⟩ := ht
        obtain ⟨u, hu, hul⟩ := mapM_mem honward hl
        have h1 := search_pos_le htaken hpos u hu
        split at hul
        · simp only [Option.some.injEq] at hul
          subst hul
          simp only [List.mem_singleton] at htl
          subst htl
          exact h1
        · have h2 := searchRep_pos_le hul h1.2 t htl
          exact ⟨Nat.le_trans h1.1 h2.1, h2.2⟩
      split at h
      · exact henter r h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨Nat.le_refl _, hpos⟩
        · obtain ⟨taken, htaken, hres⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.pure_def, Option.some.injEq] at hres
          subst hres
          intro t ht
          have hmem : t ∈ taken ∨ t = ⟨pos, regs⟩ := by
            split at ht
            · simpa only [List.mem_append, List.mem_singleton] using ht
            · rcases List.mem_cons.mp ht with h' | h'
              · exact Or.inr h'
              · exact Or.inl h'
          rcases hmem with hmem | rfl
          · exact henter taken htaken t hmem
          · exact ⟨Nat.le_refl _, hpos⟩
termination_by (fuel, 1 + sizeOf body)

end

/-- The rounds a repetition can still recurse through from count `cnt` at
position `pos`: toward the bound when there is one, toward the minimum and
then the end of the subject when there is not. Every round of `searchRep`
that reaches its tail strictly shrinks it, which is the whole totality
argument. -/
def repRemaining (n lo : Nat) (hi : Option Nat) (cnt pos : Nat) : Nat :=
  match hi with
  | some h => max lo h + 1 - cnt
  | none => (lo - cnt) + (n + 1 - pos)

mutual

/-- S-3's heart: at the sufficient fuel the search always answers. -/
theorem search_some {fuel : Nat} {c : SCtx} {a : Ast} {pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size) (hfuel : suffFuel c.s.size a ≤ fuel) :
    (search fuel c a pos regs).isSome := by
  match a with
  | .cat kids =>
      rw [search.eq_def]
      exact searchCat_some hpos fun k hk =>
        Nat.le_trans (suffFuel_le_cat hk) hfuel
  | .alt arms =>
      rw [search.eq_def]
      exact searchAlt_some hpos fun arm ha =>
        Nat.le_trans (suffFuel_le_alt ha) hfuel
  | .grp cap body =>
      rw [search.eq_def]
      simp only [Option.isSome_map]
      exact search_some hpos (by rw [suffFuel] at hfuel; exact hfuel)
  | .rep lo hi greedy body =>
      match hi with
      | some 0 =>
          rw [search.eq_def]
          simp
      | some 1 =>
          rw [search.eq_def]
          simp only [suffFuel] at hfuel
          simp only []
          split
          · exact search_some hpos (by omega)
          · simp only [Option.isSome_map]
            exact search_some hpos (by omega)
      | none =>
          rw [search.eq_def]
          simp only [suffFuel] at hfuel
          exact searchRep_some hpos (by simp only [repRemaining]; omega)
      | some (_ + 2) =>
          rw [search.eq_def]
          simp only [suffFuel] at hfuel
          exact searchRep_some hpos (by simp only [repRemaining]; omega)
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [search.eq_def]
      simp
termination_by (fuel, sizeOf a)

theorem searchCat_some {fuel : Nat} {c : SCtx} {kids : List Ast} {pos : Nat}
    {regs : Regs} (hpos : pos ≤ c.s.size)
    (hfuel : ∀ k ∈ kids, suffFuel c.s.size k ≤ fuel) :
    (searchCat fuel c kids pos regs).isSome := by
  match kids with
  | [] =>
      rw [searchCat.eq_def]
      simp
  | k :: rest =>
      rw [searchCat.eq_def]
      obtain ⟨heads, hheads⟩ := Option.isSome_iff_exists.mp
        (search_some (a := k) (regs := regs) hpos (hfuel k (by simp)))
      have hb := search_pos_le hheads hpos
      have htails : (heads.mapM fun t =>
          searchCat fuel c rest t.pos t.regs).isSome :=
        mapM_isSome fun t ht =>
          searchCat_some (hb t ht).2 fun k' hk' => hfuel k' (by simp [hk'])
      obtain ⟨tails, htails⟩ := Option.isSome_iff_exists.mp htails
      simp [hheads, htails]
termination_by (fuel, sizeOf kids)

theorem searchAlt_some {fuel : Nat} {c : SCtx} {arms : List Ast} {pos : Nat}
    {regs : Regs} (hpos : pos ≤ c.s.size)
    (hfuel : ∀ x ∈ arms, suffFuel c.s.size x ≤ fuel) :
    (searchAlt fuel c arms pos regs).isSome := by
  match arms with
  | [] =>
      rw [searchAlt.eq_def]
      simp
  | arm :: rest =>
      rw [searchAlt.eq_def]
      obtain ⟨mine, hmine⟩ := Option.isSome_iff_exists.mp
        (search_some (a := arm) (regs := regs) hpos (hfuel arm (by simp)))
      obtain ⟨theirs, htheirs⟩ := Option.isSome_iff_exists.mp
        (searchAlt_some (arms := rest) (regs := regs) hpos
          fun x hx => hfuel x (by simp [hx]))
      simp [hmine, htheirs]
termination_by (fuel, sizeOf arms)

/-- The budget argument, one round: a continuation only runs at `cnt + 1`
with either the count still below the bound, or — unbounded — a strictly
advanced position or a below-the-minimum empty iteration, so `repRemaining`
strictly shrinks and the fuel spent on the round is covered. -/
theorem searchRep_some {fuel : Nat} {c : SCtx} {body : Ast} {lo : Nat}
    {hi : Option Nat} {greedy : Bool} {cnt pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size)
    (hfuel : repRemaining c.s.size lo hi cnt pos
      + suffFuel c.s.size body + 2 ≤ fuel) :
    (searchRep fuel c body lo hi greedy cnt pos regs).isSome := by
  match fuel with
  | 0 => exact absurd hfuel (by omega)
  | fuel + 1 =>
      rw [searchRep.eq_def]
      simp only []
      have hbody : suffFuel c.s.size body ≤ fuel := by omega
      have henter : (∀ h', hi = some h' → cnt < max lo h') →
          ∃ v, (do
            let taken ← search fuel c body pos regs
            let onward ← taken.mapM fun t =>
              if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                pure [t]
              else
                searchRep fuel c body lo hi greedy (cnt + 1) t.pos t.regs
            pure onward.flatten : Option (List Thread)) = some v := by
        intro hcommon
        obtain ⟨taken, htaken⟩ := Option.isSome_iff_exists.mp
          (search_some (a := body) (regs := regs) hpos hbody)
        have hb := search_pos_le htaken hpos
        have honward : (taken.mapM fun t =>
            if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
              some [t]
            else
              searchRep fuel c body lo hi greedy (cnt + 1) t.pos t.regs).isSome := by
          refine mapM_isSome fun t ht => ?_
          split
          · simp
          · rename_i hguard
            refine searchRep_some (hb t ht).2 ?_
            cases hi with
            | some h' =>
                have hcnt := hcommon h' rfl
                simp only [repRemaining] at hfuel ⊢
                omega
            | none =>
                have h1 := (hb t ht).1
                have h2 := (hb t ht).2
                simp only [Option.isNone_none, Bool.true_and, Bool.and_eq_true,
                  beq_iff_eq, decide_eq_true_eq, not_and] at hguard
                simp only [repRemaining] at hfuel ⊢
                by_cases hp : t.pos = pos
                · have := hguard hp
                  omega
                · omega
        obtain ⟨onward, honward⟩ := Option.isSome_iff_exists.mp honward
        exact ⟨onward.flatten, by
          simp only [Option.bind_eq_bind, htaken, Option.bind_some, honward,
            Option.pure_def]⟩
      split
      · rename_i h1
        obtain ⟨v, hv⟩ := henter fun h' hh => by
          subst hh
          exact Nat.lt_of_lt_of_le h1 (Nat.le_max_left lo h')
        rw [hv]
        simp
      · split
        · simp
        · rename_i h1 h2
          obtain ⟨v, hv⟩ := henter fun h' hh => by
            subst hh
            simp only [Option.any_some, decide_eq_true_eq] at h2
            omega
          rw [hv]
          simp
termination_by (fuel, 1 + sizeOf body)

end

/-- More fuel never changes a `some` list of attempt survivors. -/
theorem attemptThreads_mono {fuel fuel' : Nat} {p : Pat} {s : ByteArray}
    {mo : MOpts} {start attempt : Nat} {r : List Thread}
    (h : attemptThreads fuel p s mo start attempt = some r)
    (hle : fuel ≤ fuel') :
    attemptThreads fuel' p s mo start attempt = some r := by
  unfold attemptThreads at h ⊢
  obtain ⟨threads, hth, hres⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨threads, search_mono hth hle, hres⟩

/-- At the sufficient fuel every attempt answers. -/
theorem attemptThreads_some {fuel : Nat} {p : Pat} {s : ByteArray}
    {mo : MOpts} {start attempt : Nat} (hpos : attempt ≤ s.size)
    (hfuel : suffFuel s.size p.root ≤ fuel) :
    (attemptThreads fuel p s mo start attempt).isSome := by
  unfold attemptThreads
  obtain ⟨threads, hth⟩ := Option.isSome_iff_exists.mp
    (search_some (c := ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩)
      (a := p.root) (pos := attempt)
      (regs := Array.replicate (2 * (p.ncap + 1)) unset32) hpos hfuel)
  simp [hth]

/-- The bumpalong refusal only ever skips a position inside the subject. -/
theorem skipsAttempt_lt {p : Pat} {s : ByteArray} {pos : Nat}
    (h : skipsAttempt p s pos = true) : pos < s.size := by
  unfold skipsAttempt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- More fuel never changes a `some` scan answer. -/
theorem scan_mono {fuel fuel' : Nat} {p : Pat} {s : ByteArray} {mo : MOpts}
    {start : Nat} (hle : fuel ≤ fuel') :
    ∀ {attempt steps : Nat} {r : MatchAnswer},
      scan fuel p s mo start attempt steps = some r →
      scan fuel' p s mo start attempt steps = some r := by
  intro attempt steps
  induction steps generalizing attempt with
  | zero =>
      intro r h
      rw [scan.eq_def] at h
      simp at h
  | succ steps ih =>
      intro r h
      rw [scan.eq_def] at h ⊢
      simp only [] at h ⊢
      obtain ⟨survivors, hs, hrest⟩ := Option.bind_eq_some_iff.mp h
      refine Option.bind_eq_some_iff.mpr
        ⟨survivors, attemptThreads_mono hs hle, ?_⟩
      cases survivors with
      | cons t rest => exact hrest
      | nil =>
          simp only [] at hrest ⊢
          split at hrest <;> rename_i hcond
          · rw [if_pos hcond]
            exact hrest
          · rw [if_neg hcond]
            exact ih hrest

/-- The scan's own step bound is enough: starting inside the subject, an
answer arrives within `s.size + 1 - attempt` steps, because every recursive
call strictly advances the attempt and the loop stops at the far end. -/
theorem scan_some {fuel : Nat} {p : Pat} {s : ByteArray} {mo : MOpts}
    {start : Nat} (hfuel : suffFuel s.size p.root ≤ fuel) :
    ∀ {attempt steps : Nat}, attempt ≤ s.size →
      s.size + 1 - attempt ≤ steps →
      (scan fuel p s mo start attempt steps).isSome := by
  intro attempt steps
  induction steps generalizing attempt with
  | zero =>
      intro h1 h2
      exact absurd h2 (by omega)
  | succ steps ih =>
      intro h1 h2
      rw [scan.eq_def]
      simp only []
      obtain ⟨survivors, hs⟩ := Option.isSome_iff_exists.mp
        (attemptThreads_some (mo := mo) (start := start) h1 hfuel)
      rw [hs]
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases survivors with
      | cons t rest => simp
      | nil =>
          simp only []
          split
          · simp
          · rename_i hcond
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
            have hlt : attempt < s.size := Nat.lt_of_not_le hcond.2
            split <;> rename_i hskip
            · have := skipsAttempt_lt hskip
              exact ih (by omega) (by omega)
            · exact ih (by omega) (by omega)

/-- More fuel never changes a `some` answer of the whole call. -/
theorem matchesF_mono {fuel fuel' : Nat} {p : Pat} {s : ByteArray}
    {start : Nat} {mo : MOpts} {r : MatchAnswer}
    (h : matchesF fuel p s start mo = some r) (hle : fuel ≤ fuel') :
    matchesF fuel' p s start mo = some r := by
  unfold matchesF at h ⊢
  split at h <;> rename_i hcond
  · rw [if_pos hcond]
    exact h
  · rw [if_neg hcond]
    exact scan_mono hle h

/-- At the sufficient fuel the whole call always answers: bad inputs answer
`BadInput` outright, and a valid start is a position inside the subject. -/
theorem matchesF_some {fuel : Nat} {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} (hfuel : suffFuel s.size p.root ≤ fuel) :
    (matchesF fuel p s start mo).isSome := by
  unfold matchesF
  split
  · simp
  · rename_i hcond
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
    exact scan_some hfuel (by have := hcond.1; omega) (Nat.le_refl _)

/-- S-4: what a pattern means, total. The fuel-indexed search of S-2 read at
the sufficient fuel of S-3, which `matchesF_some` proves is always enough. -/
def Matches (p : Pat) (s : ByteArray) (start : Nat) (mo : MOpts) :
    MatchAnswer :=
  (matchesF (suffFuel s.size p.root) p s start mo).get
    (matchesF_some (Nat.le_refl _))

/-- S-3: beyond the sufficient fuel the answer no longer changes. -/
theorem matches_stable (p : Pat) (s : ByteArray) (start : Nat) (mo : MOpts) :
    ∀ fuel, suffFuel s.size p.root ≤ fuel →
      matchesF fuel p s start mo = some (Matches p s start mo) := by
  intro fuel hfuel
  exact matchesF_mono (Option.some_get _).symm hfuel

end Pcrevera.Spec
