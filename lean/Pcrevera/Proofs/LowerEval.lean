import Pcrevera.Spec.Lower

/-!
# The search read at its own sufficient fuel

Every statement about the lowering compares two trees that need different
amounts of fuel: `x{4,7}` spends a handful of rounds, and the copies it
unrolls to spend none at all but stand four bodies deep. So the fuel side of
L-2 is an implication — each tree gets a budget of its own — and carrying two
budgets through an induction is exactly the bookkeeping that makes such a
proof unreadable.

This file removes the bookkeeping instead of managing it. `ev` is the search
evaluated at the sufficient fuel of S-3, which `search_some` says always
answers and `search_mono` says nothing above it can change; `evRep` is the
same for one repetition's remaining rounds. Two lemmas say that any large
enough fuel agrees with them, and one unfolding lemma turns `evRep` into a
round expressed in `ev` and `evRep` again. After that, no proof about the
lowering mentions fuel.
-/

namespace Pcrevera.Spec

open Pcrevera

/-- `mapM` over `Option` respects pointwise equality on the list. -/
theorem mapM_congr {α β : Type} {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.mapM f = l.mapM g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih fun y hy => h y (by simp [hy])
      simp only [List.mapM_cons, hx, hxs]

/-- The flattening round that a concatenation and a repetition share: two
pointwise equal continuations give the same answer. -/
theorem mapM_flatten_congr {f g : Thread → Option (List Thread)}
    {l : List Thread} (h : ∀ x ∈ l, f x = g x) :
    ((l.mapM f).bind fun onward => (pure onward.flatten : Option (List Thread)))
      = (l.mapM g).bind fun onward => pure onward.flatten := by
  rw [mapM_congr h]

/-- The search of a subtree, at the fuel S-3 proves is always enough. -/
def ev (c : SCtx) (a : Ast) (pos : Nat) (regs : Regs) : Option (List Thread) :=
  search (suffFuel c.s.size a) c a pos regs

/-- One repetition's remaining rounds, at the fuel `searchRep_some` needs. -/
def evRep (c : SCtx) (body : Ast) (lo : Nat) (hi : Option Nat) (greedy : Bool)
    (cnt pos : Nat) (regs : Regs) : Option (List Thread) :=
  searchRep (repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 2)
    c body lo hi greedy cnt pos regs

theorem ev_isSome {c : SCtx} {a : Ast} {pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size) : (ev c a pos regs).isSome :=
  search_some hpos (Nat.le_refl _)

theorem evRep_isSome {c : SCtx} {body : Ast} {lo : Nat} {hi : Option Nat}
    {greedy : Bool} {cnt pos : Nat} {regs : Regs} (hpos : pos ≤ c.s.size) :
    (evRep c body lo hi greedy cnt pos regs).isSome :=
  searchRep_some hpos (Nat.le_refl _)

/-- Any fuel at or above the sufficient one gives `ev`'s answer. -/
theorem search_eq_ev {fuel : Nat} {c : SCtx} {a : Ast} {pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size) (hf : suffFuel c.s.size a ≤ fuel) :
    search fuel c a pos regs = ev c a pos regs := by
  obtain ⟨r, hr⟩ :=
    Option.isSome_iff_exists.mp (ev_isSome (a := a) (regs := regs) hpos)
  rw [hr]
  exact search_mono hr hf

/-- Any fuel at or above `searchRep_some`'s gives `evRep`'s answer. -/
theorem searchRep_eq_evRep {fuel : Nat} {c : SCtx} {body : Ast} {lo : Nat}
    {hi : Option Nat} {greedy : Bool} {cnt pos : Nat} {regs : Regs}
    (hpos : pos ≤ c.s.size)
    (hf : repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 2
      ≤ fuel) :
    searchRep fuel c body lo hi greedy cnt pos regs
      = evRep c body lo hi greedy cnt pos regs := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (evRep_isSome (c := c) (body := body) (lo := lo) (hi := hi)
      (greedy := greedy) (cnt := cnt) (regs := regs) hpos)
  rw [hr]
  exact searchRep_mono hr hf

/-- Every thread a subtree offers sits between the start and the far end. -/
theorem ev_pos_le {c : SCtx} {a : Ast} {pos : Nat} {regs : Regs}
    {r : List Thread} (h : ev c a pos regs = some r) (hpos : pos ≤ c.s.size) :
    ∀ t ∈ r, pos ≤ t.pos ∧ t.pos ≤ c.s.size :=
  search_pos_le h hpos

/-- One round of a repetition: the body, then whatever each of its threads
leads to, with pcre2's empty-match rule ending an unbounded iteration that
consumed nothing once the minimum is behind it. -/
def repEnter (c : SCtx) (body : Ast) (lo : Nat) (hi : Option Nat)
    (greedy : Bool) (cnt pos : Nat) (regs : Regs) : Option (List Thread) := do
  let taken ← ev c body pos regs
  let onward ← taken.mapM fun t =>
    if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then pure [t]
    else evRep c body lo hi greedy (cnt + 1) t.pos t.regs
  pure onward.flatten

/-- The round a repetition still has ahead of it strictly shrinks, whenever
it takes one.

Which is `searchRep_some`'s argument, kept apart because the unfolding lemma
and the congruence both need it: a continuation runs at a count one higher,
and either the bound is still ahead of that count, or — with no bound — the
empty-match rule's negation says the position advanced instead. -/
theorem repRemaining_descent {c : SCtx} {lo : Nat} {hi : Option Nat}
    {cnt pos : Nat} {t : Thread} (hlo : pos ≤ t.pos) (hhi : t.pos ≤ c.s.size)
    (hbranch : cnt < lo ∨ (¬ cnt < lo ∧ ¬ hi.any (cnt ≥ ·) = true))
    (hguard : ¬ (hi.isNone && t.pos == pos && decide (cnt + 1 ≥ lo)) = true) :
    repRemaining c.s.size lo hi (cnt + 1) t.pos
      < repRemaining c.s.size lo hi cnt pos := by
  cases hi with
  | some h =>
      simp only [repRemaining]
      rcases hbranch with h1 | ⟨_, h2⟩
      · omega
      · simp only [Option.any_some, decide_eq_true_eq] at h2
        omega
  | none =>
      simp only [Option.isNone_none, Bool.true_and, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, not_and] at hguard
      simp only [repRemaining]
      rcases hbranch with h1 | ⟨h1, _⟩
      · omega
      · have hne : t.pos ≠ pos := fun hEq =>
          absurd (show cnt + 1 ≥ lo by omega) (hguard hEq)
        omega

/-- The one unfolding everything downstream uses: a repetition's remaining
rounds, written as a round of its own plus the rounds after it.

Below the minimum the body is entered with no exit offered; at a spent
bounded count the exit is the only continuation; otherwise greediness orders
body against exit. -/
theorem evRep_eq {c : SCtx} {body : Ast} {lo : Nat} {hi : Option Nat}
    {greedy : Bool} {cnt pos : Nat} {regs : Regs} (hpos : pos ≤ c.s.size) :
    evRep c body lo hi greedy cnt pos regs =
      if cnt < lo then repEnter c body lo hi greedy cnt pos regs
      else if hi.any (cnt ≥ ·) then some [⟨pos, regs⟩]
      else (repEnter c body lo hi greedy cnt pos regs).map fun taken =>
        if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken := by
  have hbody : suffFuel c.s.size body
      ≤ repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 1 := by
    omega
  have hdrop : ∀ t : Thread, pos ≤ t.pos → t.pos ≤ c.s.size →
      (cnt < lo ∨ (¬ cnt < lo ∧ ¬ hi.any (cnt ≥ ·) = true)) →
      ¬ (hi.isNone && t.pos == pos && decide (cnt + 1 ≥ lo)) = true →
      repRemaining c.s.size lo hi (cnt + 1) t.pos + suffFuel c.s.size body + 2
        ≤ repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 1 :=
    fun t hlo hhi hbranch hguard => by
      have := repRemaining_descent (c := c) (lo := lo) (hi := hi) (cnt := cnt)
        (pos := pos) (t := t) hlo hhi hbranch hguard
      omega
  unfold evRep
  have hsplit : repRemaining c.s.size lo hi cnt pos
      + suffFuel c.s.size body + 2
      = (repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 1)
        + 1 := by omega
  rw [hsplit, searchRep.eq_def]
  simp only []
  have henter : ∀ (_ : cnt < lo ∨ (¬ cnt < lo ∧ ¬ hi.any (cnt ≥ ·) = true)),
      (do
        let taken ← search
          (repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 1)
          c body pos regs
        let onward ← taken.mapM fun t =>
          if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
            pure [t]
          else
            searchRep
              (repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 1)
              c body lo hi greedy (cnt + 1) t.pos t.regs
        pure onward.flatten : Option (List Thread))
        = repEnter c body lo hi greedy cnt pos regs := by
    intro hbranch
    unfold repEnter
    rw [search_eq_ev hpos hbody]
    obtain ⟨taken, htaken⟩ :=
      Option.isSome_iff_exists.mp (ev_isSome (c := c) (a := body)
        (pos := pos) (regs := regs) hpos)
    rw [htaken]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hmap : (taken.mapM fun t =>
        if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
          pure [t]
        else
          searchRep
            (repRemaining c.s.size lo hi cnt pos + suffFuel c.s.size body + 1)
            c body lo hi greedy (cnt + 1) t.pos t.regs)
        = taken.mapM fun t =>
            if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
              pure [t]
            else evRep c body lo hi greedy (cnt + 1) t.pos t.regs := by
      refine mapM_congr fun t ht => ?_
      have hb := ev_pos_le htaken hpos t ht
      split <;> rename_i hguard
      · rfl
      · exact searchRep_eq_evRep hb.2 (hdrop t hb.1 hb.2 hbranch hguard)
    rw [hmap]
  split <;> rename_i h1
  · exact henter (Or.inl h1)
  · split <;> rename_i h2
    · rfl
    · rw [henter (Or.inr ⟨h1, h2⟩)]
      generalize repEnter c body lo hi greedy cnt pos regs = e
      cases e <;> rfl

/-- Two subtrees the search cannot tell apart: same threads, same order,
same registers, from every position it could be asked about.

This is the relation the whole lowering proof is stated in. It is an
equivalence, it is a congruence for every constructor, and the two splices
are its two interesting instances. -/
def SearchEq (c : SCtx) (a b : Ast) : Prop :=
  ∀ (pos : Nat) (regs : Regs), pos ≤ c.s.size → ev c a pos regs = ev c b pos regs

theorem SearchEq.refl (c : SCtx) (a : Ast) : SearchEq c a a := fun _ _ _ => rfl

theorem SearchEq.symm {c : SCtx} {a b : Ast} (h : SearchEq c a b) :
    SearchEq c b a := fun pos regs hpos => (h pos regs hpos).symm

theorem SearchEq.trans {c : SCtx} {a b d : Ast} (h : SearchEq c a b)
    (h' : SearchEq c b d) : SearchEq c a d :=
  fun pos regs hpos => (h pos regs hpos).trans (h' pos regs hpos)

/-- A subtree that always moves the position on.

The unbounded splice needs exactly this of a body, and nothing syntactic:
stated on the answer rather than on the shape, it transfers across
`SearchEq` for free, which saves proving that the lowering preserves the
engine's syntactic nullability. -/
def Consumes (c : SCtx) (b : Ast) : Prop :=
  ∀ (pos : Nat) (regs : Regs) (r : List Thread), pos ≤ c.s.size →
    ev c b pos regs = some r → ∀ t ∈ r, pos < t.pos

theorem Consumes.congr {c : SCtx} {b b' : Ast} (heq : SearchEq c b b')
    (h : Consumes c b) : Consumes c b' := by
  intro pos regs r hpos hr t ht
  exact h pos regs r hpos ((heq pos regs hpos).trans hr) t ht

end Pcrevera.Spec
