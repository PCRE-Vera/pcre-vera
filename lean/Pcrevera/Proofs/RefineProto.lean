import Pcrevera.Ref.VM
import Pcrevera.Proofs.Meter
import Batteries.Tactic.OpenPrivate

/-!
# A refinement prototype for S-8 (chr, cat, alt)

The load-bearing shape of the compiler-correctness half of S-8, proven end
to end on the subset {`chr`, `cat`, non-empty `alt`} — the patterns whose
compiled form uses only chr, split, jump and the trailing accept. The full
theorem says: whenever the backtracking VM completes an attempt, its answer
is the spec's. This file validates the formulation that makes that
provable, so the real proof can scale it instead of searching for it.

The chain has four independently proven links:

* **An unmetered mirror.** `run`/`dispatch` restate `btStep`/`btFail` with
  the charges deleted: fuel-indexed, same dispatch, same stack discipline,
  same fuel hand-off. Judgments `Runs` and `Resumes` put the fuel under an
  existential, and monotonicity (`run_mono`) turns them into a
  deterministic partial semantics one can do algebra with.

* **The frame laws.** The single most load-bearing fact: a run over a
  composed stack `stk₁ ++ stk₂` either finds its match using `stk₁` alone
  or drains `stk₁` to nomatch and resumes `stk₂` (`runs_append`,
  `resumes_append`). Every piece of "first success of the concatenated
  candidate lists" reasoning — the spec's preference order — reduces to
  these two equivalences plus the one-step opcode lemmas.

* **The fragment theorem** (`frag_runs`, formulation A of the S-8 notes).
  `FragAt code a lo hi` pins the compiled shape of `a` on `[lo, hi)`; the
  theorem states that running from `lo` with any pending stack behaves
  exactly like queuing the spec's matches — `enum`, the search with fuel
  and registers stripped — at the exit `hi`, in front of that stack. The
  continuation stays abstract; accept enters only at the top level.
  `compileNode_facts` proves the compiler establishes `FragAt`, by
  induction on a size bound so `compileAlt`'s jump-accumulator can be
  handled by a strengthened list induction rather than a mutual proof.

* **The metered bridge** (`btStep_mirror`). On this subset nothing ever
  writes a register through the trail, so the trail stays empty, marks and
  replay are vacuous, and a backtrack entry means exactly a resume point:
  a completed `btStep` — found or exhausted, never exceeded — agrees with
  the mirror on the very same fuel. Refinement, not equality: the metered
  side can still stop early on any budget.

`attempt_refines` composes the links: a completed attempt on a compiled
covered pattern answers the head of `Spec.search`'s preference-ordered
list, or nomatch when that list is empty.

Two deliberate simplifications, to be discharged when scaling up: the
empty-match refusal at accept is assumed off (`mo.notempty = false`,
`mo.notemptyAtStart = false` — the statement "up to the accept filter"),
and the comparison stops at the attempt level (the scan loop, the ovector
delivery and the bumpalong rule are outside this file's scope).
-/

open private emit patch openRegion closeRegion from Pcrevera.Ref.Compile

namespace Pcrevera.RefineProto

open Pcrevera Pcrevera.Ref

/-- How a completed search ended: the two answers a run can commit to. -/
inductive Out where
  | found (pos : Nat)
  | nomatch
deriving DecidableEq, Repr

mutual

/-- The unmetered mirror of `btStep` on the proto's opcodes, fuel-indexed:
same dispatch, same stack discipline, no charges and no registers. On the
chr/split/jump/accept fragment the trail never grows, so a backtrack entry
is just a resume point and the whole mutable state is the pending list.
`none` is fuel running out; any opcode outside the fragment also answers
`none`, which keeps the mirror honest about what it covers. -/
def run (code : Array Inst) (s : ByteArray) :
    Nat → Nat → Nat → List (Nat × Nat) → Option Out
  | 0, _, _, _ => none
  | fuel + 1, pc, pos, stk =>
      match (code[pc]!).op with
      | .chr =>
          if pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg then
            run code s fuel (pc + 1) (pos + 1) stk
          else dispatch code s fuel stk
      | .split =>
          run code s fuel (code[pc]!).arg pos (((code[pc]!).alt, pos) :: stk)
      | .jump => run code s fuel (code[pc]!).arg pos stk
      | .accept => some (.found pos)
      | _ => none
termination_by fuel _ _ _ => (fuel, 0)

/-- Hand the next pending thread to `run`, or report the search over. -/
def dispatch (code : Array Inst) (s : ByteArray) (fuel : Nat) :
    List (Nat × Nat) → Option Out
  | [] => some .nomatch
  | (pc, pos) :: stk => run code s fuel pc pos stk
termination_by _ => (fuel, 1)

end

/-- The mirror completes from this configuration with this answer. Stating
runs with the fuel under an existential is what makes every later lemma an
equation between judgments instead of a fuel-arithmetic exercise. -/
def Runs (code : Array Inst) (s : ByteArray) (pc pos : Nat)
    (stk : List (Nat × Nat)) (r : Out) : Prop :=
  ∃ fuel, run code s fuel pc pos stk = some r

/-- Dispatching this pending list completes with this answer. -/
def Resumes (code : Array Inst) (s : ByteArray) (stk : List (Nat × Nat))
    (r : Out) : Prop :=
  ∃ fuel, dispatch code s fuel stk = some r

theorem run_mono {code : Array Inst} {s : ByteArray} :
    ∀ {fuel fuel' pc pos stk r}, fuel ≤ fuel' →
      run code s fuel pc pos stk = some r →
      run code s fuel' pc pos stk = some r := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [run] at h
  | succ n ih =>
      intro fuel' pc pos stk r hle h
      obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
      rw [run] at h ⊢
      cases hop : (code[pc]!).op <;> simp only [hop] at h ⊢
      case chr =>
        by_cases hc : (pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg) = true
        · rw [if_pos hc] at h ⊢; exact ih (by omega) h
        · rw [if_neg hc] at h ⊢
          cases stk with
          | nil => simpa [dispatch] using h
          | cons top rest =>
              obtain ⟨q, qp⟩ := top
              simp only [dispatch] at h ⊢
              exact ih (by omega) h
      case split => exact ih (by omega) h
      case jump => exact ih (by omega) h
      all_goals exact h

theorem dispatch_mono {code : Array Inst} {s : ByteArray}
    {fuel fuel' : Nat} {stk : List (Nat × Nat)} {r : Out}
    (hle : fuel ≤ fuel') (h : dispatch code s fuel stk = some r) :
    dispatch code s fuel' stk = some r := by
  cases stk with
  | nil => simpa [dispatch] using h
  | cons top rest =>
      obtain ⟨q, qp⟩ := top
      simp only [dispatch] at h ⊢
      exact run_mono hle h

theorem runs_det {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r r' : Out}
    (h : Runs code s pc pos stk r) (h' : Runs code s pc pos stk r') :
    r = r' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  have h1 := run_mono (Nat.le_max_left m m') hm
  have h2 := run_mono (Nat.le_max_right m m') hm'
  rw [h1] at h2
  exact Option.some.inj h2

theorem resumes_det {code : Array Inst} {s : ByteArray}
    {stk : List (Nat × Nat)} {r r' : Out}
    (h : Resumes code s stk r) (h' : Resumes code s stk r') : r = r' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  have h1 := dispatch_mono (Nat.le_max_left m m') hm
  have h2 := dispatch_mono (Nat.le_max_right m m') hm'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## One-step readings of the four opcodes

Each lemma peels or adds exactly one fuel unit, so the judgments can be
rewritten along the code without ever mentioning fuel again. -/

theorem resumes_nil {code : Array Inst} {s : ByteArray} {r : Out} :
    Resumes code s [] r ↔ r = .nomatch := by
  constructor
  · rintro ⟨fuel, h⟩
    simpa [dispatch] using h.symm
  · rintro rfl
    exact ⟨0, by rw [dispatch]⟩

theorem resumes_cons {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r : Out} :
    Resumes code s ((pc, pos) :: stk) r ↔ Runs code s pc pos stk r := by
  constructor
  · rintro ⟨fuel, h⟩
    rw [dispatch] at h
    exact ⟨fuel, h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨fuel, ?_⟩
    rw [dispatch]
    exact h

theorem runs_chr_yes {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r : Out}
    (hop : (code[pc]!).op = .chr)
    (hc : (pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg) = true) :
    Runs code s pc pos stk r ↔ Runs code s (pc + 1) (pos + 1) stk r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
        rw [run] at h
        simp only [hop, if_pos hc] at h
        exact ⟨n, h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨fuel + 1, ?_⟩
    rw [run]
    simp only [hop, if_pos hc]
    exact h

theorem runs_chr_no {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r : Out}
    (hop : (code[pc]!).op = .chr)
    (hc : ¬ (pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg) = true) :
    Runs code s pc pos stk r ↔ Resumes code s stk r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
        rw [run] at h
        simp only [hop, if_neg hc] at h
        exact ⟨n, h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨fuel + 1, ?_⟩
    rw [run]
    simp only [hop, if_neg hc]
    exact h

theorem runs_split {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r : Out}
    (hop : (code[pc]!).op = .split) :
    Runs code s pc pos stk r ↔
      Runs code s (code[pc]!).arg pos (((code[pc]!).alt, pos) :: stk) r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
        rw [run] at h
        simp only [hop] at h
        exact ⟨n, h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨fuel + 1, ?_⟩
    rw [run]
    simp only [hop]
    exact h

theorem runs_jump {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r : Out}
    (hop : (code[pc]!).op = .jump) :
    Runs code s pc pos stk r ↔ Runs code s (code[pc]!).arg pos stk r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
        rw [run] at h
        simp only [hop] at h
        exact ⟨n, h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨fuel + 1, ?_⟩
    rw [run]
    simp only [hop]
    exact h

theorem runs_accept {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk : List (Nat × Nat)} {r : Out}
    (hop : (code[pc]!).op = .accept) :
    Runs code s pc pos stk r ↔ r = .found pos := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
        rw [run] at h
        simp only [hop] at h
        exact (Option.some.inj h).symm
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [run]
    simp only [hop]

/-! ## The frame laws

The stack is the linearized search: what sits below the fragment's own
entries can only be reached after the fragment's search is over. The frame
laws turn that into algebra — a run over `stk₁ ++ stk₂` either finds a
match using `stk₁` alone, or drains `stk₁` to `nomatch` and hands the rest
of the search to `stk₂`. -/

theorem run_extend_found {code : Array Inst} {s : ByteArray} :
    ∀ {fuel pc pos stk stk₂ p},
      run code s fuel pc pos stk = some (.found p) →
      run code s fuel pc pos (stk ++ stk₂) = some (.found p) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [run] at h
  | succ n ih =>
      intro pc pos stk stk₂ p h
      rw [run] at h ⊢
      cases hop : (code[pc]!).op <;> simp only [hop] at h ⊢
      case chr =>
        by_cases hc : (pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg) = true
        · rw [if_pos hc] at h ⊢; exact ih h
        · rw [if_neg hc] at h ⊢
          cases stk with
          | nil => simp [dispatch] at h
          | cons top rest =>
              obtain ⟨q, qp⟩ := top
              simp only [dispatch, List.cons_append] at h ⊢
              exact ih h
      case split => exact ih h
      case jump => exact ih h
      all_goals exact h

theorem run_extend_nomatch {code : Array Inst} {s : ByteArray} :
    ∀ {fuel₁ fuel₂ pc pos stk stk₂ r},
      run code s fuel₁ pc pos stk = some .nomatch →
      dispatch code s fuel₂ stk₂ = some r →
      run code s (fuel₁ + fuel₂) pc pos (stk ++ stk₂) = some r := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro _ _ _ _ _ _ h _; simp [run] at h
  | succ n ih =>
      intro fuel₂ pc pos stk stk₂ r h h₂
      have hsucc : n + 1 + fuel₂ = (n + fuel₂) + 1 := by omega
      rw [hsucc, run]
      rw [run] at h
      cases hop : (code[pc]!).op <;> simp only [hop] at h ⊢
      case chr =>
        by_cases hc : (pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg) = true
        · rw [if_pos hc] at h ⊢; exact ih h h₂
        · rw [if_neg hc] at h ⊢
          cases stk with
          | nil =>
              simpa [List.nil_append] using
                dispatch_mono (Nat.le_add_left fuel₂ n) h₂
          | cons top rest =>
              obtain ⟨q, qp⟩ := top
              simp only [dispatch, List.cons_append] at h ⊢
              exact ih h h₂
      case split => exact ih h h₂
      case jump => exact ih h h₂
      all_goals simp at h

theorem run_frame {code : Array Inst} {s : ByteArray} :
    ∀ {fuel pc pos stk stk₂ r},
      run code s fuel pc pos (stk ++ stk₂) = some r →
      (∃ p, r = .found p ∧ Runs code s pc pos stk r) ∨
      (Runs code s pc pos stk .nomatch ∧ Resumes code s stk₂ r) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [run] at h
  | succ n ih =>
      intro pc pos stk stk₂ r h
      rw [run] at h
      cases hop : (code[pc]!).op <;> simp only [hop] at h
      case chr =>
        by_cases hc : (pos < s.size && byteAt s pos == UInt8.ofNat (code[pc]!).arg) = true
        · rw [if_pos hc] at h
          rcases ih h with ⟨p, rfl, hr⟩ | ⟨hn, hres⟩
          · exact .inl ⟨p, rfl, (runs_chr_yes hop hc).mpr hr⟩
          · exact .inr ⟨(runs_chr_yes hop hc).mpr hn, hres⟩
        · rw [if_neg hc] at h
          cases stk with
          | nil =>
              refine .inr ⟨(runs_chr_no hop hc).mpr (resumes_nil.mpr rfl), ?_⟩
              simp only [List.nil_append] at h
              exact ⟨n, h⟩
          | cons top rest =>
              obtain ⟨q, qp⟩ := top
              simp only [dispatch, List.cons_append] at h
              rcases ih h with ⟨p, rfl, hr⟩ | ⟨hn, hres⟩
              · exact .inl ⟨p, rfl, (runs_chr_no hop hc).mpr (resumes_cons.mpr hr)⟩
              · exact .inr ⟨(runs_chr_no hop hc).mpr (resumes_cons.mpr hn), hres⟩
      case split =>
        rw [show ((code[pc]!).alt, pos) :: (stk ++ stk₂) =
          (((code[pc]!).alt, pos) :: stk) ++ stk₂ from rfl] at h
        rcases ih h with ⟨p, rfl, hr⟩ | ⟨hn, hres⟩
        · exact .inl ⟨p, rfl, (runs_split hop).mpr hr⟩
        · exact .inr ⟨(runs_split hop).mpr hn, hres⟩
      case jump =>
        rcases ih h with ⟨p, rfl, hr⟩ | ⟨hn, hres⟩
        · exact .inl ⟨p, rfl, (runs_jump hop).mpr hr⟩
        · exact .inr ⟨(runs_jump hop).mpr hn, hres⟩
      case accept =>
        obtain rfl := (Option.some.inj h).symm
        exact .inl ⟨pos, rfl, (runs_accept hop).mpr rfl⟩
      all_goals simp at h

/-- The frame law at the judgment level: the run over a composed stack
either matches on the near half alone, or drains it and resumes the far
half. This single equivalence carries all the `firstAcceptable`-style
reasoning the spec side needs. -/
theorem runs_append {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {stk stk₂ : List (Nat × Nat)} {r : Out} :
    Runs code s pc pos (stk ++ stk₂) r ↔
      (∃ p, r = .found p ∧ Runs code s pc pos stk r) ∨
      (Runs code s pc pos stk .nomatch ∧ Resumes code s stk₂ r) := by
  constructor
  · rintro ⟨fuel, h⟩
    exact run_frame h
  · rintro (⟨p, rfl, ⟨fuel, h⟩⟩ | ⟨⟨fuel₁, h₁⟩, ⟨fuel₂, h₂⟩⟩)
    · exact ⟨fuel, run_extend_found h⟩
    · exact ⟨fuel₁ + fuel₂, run_extend_nomatch h₁ h₂⟩

theorem resumes_append {code : Array Inst} {s : ByteArray}
    {L₁ L₂ : List (Nat × Nat)} {r : Out} :
    Resumes code s (L₁ ++ L₂) r ↔
      (∃ p, r = .found p ∧ Resumes code s L₁ r) ∨
      (Resumes code s L₁ .nomatch ∧ Resumes code s L₂ r) := by
  cases L₁ with
  | nil =>
      simp only [List.nil_append]
      constructor
      · intro h
        exact .inr ⟨resumes_nil.mpr rfl, h⟩
      · rintro (⟨p, rfl, hr⟩ | ⟨_, hr⟩)
        · cases resumes_nil.mp hr
        · exact hr
  | cons top rest =>
      obtain ⟨q, qp⟩ := top
      simp only [List.cons_append, resumes_cons]
      exact runs_append

/-- Rewriting the far half of a pending list under a common near half. -/
theorem resumes_congr_tail {code : Array Inst} {s : ByteArray}
    {A L₁ L₂ : List (Nat × Nat)}
    (h : ∀ r, Resumes code s L₁ r ↔ Resumes code s L₂ r) {r : Out} :
    Resumes code s (A ++ L₁) r ↔ Resumes code s (A ++ L₂) r := by
  rw [resumes_append, resumes_append]
  exact or_congr Iff.rfl (and_congr Iff.rfl (h _))

/-- Swapping a whole pending stack for an equivalent one under a run. -/
theorem runs_congr_stack {code : Array Inst} {s : ByteArray} {pc pos : Nat}
    {L₁ L₂ : List (Nat × Nat)}
    (h : ∀ r, Resumes code s L₁ r ↔ Resumes code s L₂ r) {r : Out} :
    Runs code s pc pos L₁ r ↔ Runs code s pc pos L₂ r := by
  rw [← List.nil_append L₁, ← List.nil_append L₂, runs_append, runs_append]
  exact or_congr Iff.rfl (and_congr Iff.rfl (h _))

/-! ## The fragment relation and the enumeration

`FragAt code a lo hi` says the half-open range `[lo, hi)` of `code` is a
well-formed compilation of `a`: one chr cell, juxtaposed cat pieces, or a
split/branch/jump chain whose jumps all land on `hi`. The relation is only
inhabited for the proto's subset — chr, cat, and non-empty alt — so its
derivations double as the subset predicate, and `induction` on a derivation
is exactly the induction the compiled shape wants (an alternation peels one
branch at a time, the way `compileAlt` lays them down).

`enum` is the spec's search restated without fuel or registers: on this
subset `Spec.search` never spends fuel and never writes a register, so a
thread is just its end position and the result list is total. The bridge
back to `Spec.search` is `search_covered` below. -/

inductive FragAt (code : Array Inst) : Ast → Nat → Nat → Prop where
  | chr {b : UInt8} {lo : Nat}
      (hcell : code[lo]! = ⟨.chr, b.toNat, 0⟩) :
      FragAt code (.chr b) lo (lo + 1)
  | catNil {lo : Nat} : FragAt code (.cat []) lo lo
  | catCons {k : Ast} {kids : List Ast} {lo mid hi : Nat}
      (hk : FragAt code k lo mid)
      (hkids : FragAt code (.cat kids) mid hi) :
      FragAt code (.cat (k :: kids)) lo hi
  | altOne {a : Ast} {lo hi : Nat}
      (ha : FragAt code a lo hi) :
      FragAt code (.alt [a]) lo hi
  | altCons {a b : Ast} {rest : List Ast} {lo j hi : Nat}
      (hsplit : code[lo]! = ⟨.split, lo + 1, j + 1⟩)
      (ha : FragAt code a (lo + 1) j)
      (hjump : code[j]! = ⟨.jump, hi, 0⟩)
      (hrest : FragAt code (.alt (b :: rest)) (j + 1) hi) :
      FragAt code (.alt (a :: b :: rest)) lo hi

theorem FragAt.le {code : Array Inst} {a : Ast} {lo hi : Nat}
    (h : FragAt code a lo hi) : lo ≤ hi := by
  induction h <;> omega

/-- A fragment only pins cells inside its own range, so any code that
agrees with it there carries the same fragment — the stability fact that
lets a finished subfragment survive the rest of compilation. -/
theorem FragAt.mono {code code' : Array Inst} {a : Ast} {lo hi : Nat}
    (h : FragAt code a lo hi)
    (hag : ∀ pc, lo ≤ pc → pc < hi → code'[pc]! = code[pc]!) :
    FragAt code' a lo hi := by
  induction h with
  | chr hcell =>
      exact .chr ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | catNil => exact .catNil
  | catCons hk hkids ihk ihkids =>
      have h1 := hk.le
      have h2 := hkids.le
      exact .catCons
        (ihk fun pc h1' h2' => hag pc h1' (by omega))
        (ihkids fun pc h1' h2' => hag pc (by omega) h2')
  | altOne ha iha => exact .altOne (iha hag)
  | altCons hsplit ha hjump hrest iha ihrest =>
      have h1 := ha.le
      have h2 := hrest.le
      exact .altCons
        ((hag _ (by omega) (by omega)).trans hsplit)
        (iha fun pc h1' h2' => hag pc (by omega) (by omega))
        ((hag _ (by omega) (by omega)).trans hjump)
        (ihrest fun pc h1' h2' => hag pc (by omega) h2')

/-- Every match of a subset node from `pos`, in preference order, as bare
end positions: the spec search with the fuel and the registers stripped. -/
def enum (s : ByteArray) : Ast → Nat → List Nat
  | .chr b, pos => if pos < s.size && byteAt s pos == b then [pos + 1] else []
  | .cat [], pos => [pos]
  | .cat (k :: kids), pos =>
      (enum s k pos).flatMap fun p => enum s (.cat kids) p
  | .alt [], _ => []
  | .alt (a :: arms), pos => enum s a pos ++ enum s (.alt arms) pos
  | _, _ => []

/-! ## Two congruence helpers over pending lists -/

/-- Retargeting every pending thread through an equivalent pc. -/
theorem resumes_retarget {code : Array Inst} {s : ByteArray} {j hi : Nat}
    (hj : ∀ p stk r, Runs code s j p stk r ↔ Runs code s hi p stk r) :
    ∀ (ps : List Nat) (T : List (Nat × Nat)) (r : Out),
      Resumes code s (ps.map (fun p => (j, p)) ++ T) r ↔
      Resumes code s (ps.map (fun p => (hi, p)) ++ T) r := by
  intro ps
  induction ps with
  | nil => intro T r; exact Iff.rfl
  | cons p ps ihp =>
      intro T r
      simp only [List.map_cons, List.cons_append, resumes_cons]
      rw [hj]
      exact runs_congr_stack fun r' => ihp T r'

/-- Continuing every pending thread of a fragment into its continuation:
the list-level engine of the cat case. -/
theorem resumes_bind {code : Array Inst} {s : ByteArray} {mid hi : Nat}
    {f : Nat → List Nat}
    (hpt : ∀ p stk r, Runs code s mid p stk r ↔
      Resumes code s ((f p).map (fun q => (hi, q)) ++ stk) r) :
    ∀ (ps : List Nat) (stk : List (Nat × Nat)) (r : Out),
      Resumes code s (ps.map (fun p => (mid, p)) ++ stk) r ↔
      Resumes code s ((ps.flatMap f).map (fun q => (hi, q)) ++ stk) r := by
  intro ps
  induction ps with
  | nil => intro stk r; simp
  | cons p ps ihp =>
      intro stk r
      simp only [List.map_cons, List.cons_append, resumes_cons]
      rw [hpt]
      rw [resumes_congr_tail fun r' => ihp stk r']
      simp [List.flatMap_cons, List.map_append, List.append_assoc]

/-- The fragment theorem, formulation A: running the mirror from a
fragment's entry with any pending stack behaves exactly like queuing the
spec's matches — retargeted at the fragment's exit — in front of that
stack. The continuation and the ambient search stay abstract; `accept`
only enters the picture at the top level. -/
theorem frag_runs {code : Array Inst} {s : ByteArray} {a : Ast}
    {lo hi : Nat} (h : FragAt code a lo hi) :
    ∀ (pos : Nat) (stk : List (Nat × Nat)) (r : Out),
      Runs code s lo pos stk r ↔
      Resumes code s ((enum s a pos).map (fun p => (hi, p)) ++ stk) r := by
  induction h with
  | @chr b lo hcell =>
      intro pos stk r
      have hop : (code[lo]!).op = .chr := by rw [hcell]
      have harg : UInt8.ofNat (code[lo]!).arg = b := by
        rw [hcell]; exact UInt8.ofNat_toNat
      by_cases hc : (pos < s.size && byteAt s pos == b) = true
      · rw [runs_chr_yes hop (by rw [harg]; exact hc)]
        simp only [enum, if_pos hc, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, resumes_cons]
      · rw [runs_chr_no hop (by rw [harg]; exact hc)]
        simp only [enum, if_neg hc, List.map_nil, List.nil_append]
  | catNil =>
      intro pos stk r
      simp only [enum, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | @catCons k kids lo mid hi hk hkids ihk ihkids =>
      intro pos stk r
      rw [ihk pos stk r]
      have := resumes_bind (fun p stk' r' => ihkids p stk' r') (enum s k pos) stk r
      simpa only [enum] using this
  | altOne ha iha =>
      intro pos stk r
      rw [iha pos stk r]
      simp [enum]
  | @altCons a b rest lo j hi hsplit ha hjump hrest iha ihrest =>
      intro pos stk r
      have hops : (code[lo]!).op = .split := by rw [hsplit]
      rw [runs_split hops]
      rw [show (code[lo]!).arg = lo + 1 from by rw [hsplit]]
      rw [show (code[lo]!).alt = j + 1 from by rw [hsplit]]
      rw [iha pos ((j + 1, pos) :: stk) r]
      have hopj : (code[j]!).op = .jump := by rw [hjump]
      have hjt : ∀ p stk' r', Runs code s j p stk' r' ↔
          Runs code s hi p stk' r' := by
        intro p stk' r'
        rw [runs_jump hopj]
        rw [show (code[j]!).arg = hi from by rw [hjump]]
      rw [resumes_retarget hjt (enum s a pos) _ r]
      have hstep : ∀ r', Resumes code s ((j + 1, pos) :: stk) r' ↔
          Resumes code s
            (((enum s (Ast.alt (b :: rest)) pos).map fun p => (hi, p)) ++ stk)
            r' := by
        intro r'
        rw [resumes_cons]
        exact ihrest pos stk r'
      refine Iff.trans (resumes_congr_tail hstep) ?_
      simp [enum, List.map_append, List.append_assoc]

/-! ## The spec side: `enum` is `Spec.search` on this subset -/

/-- The proto's subset, code-free: exact bytes, concatenation, non-empty
alternation. An empty alternation is excluded on purpose — the compiler
emits nothing for it, which behaves like `nul`, while the spec's
`searchAlt []` matches nothing; the parser never produces one, and the
full proof will discharge the shape through `Pat.Wf` instead. -/
inductive Covered : Ast → Prop where
  | chr (b : UInt8) : Covered (.chr b)
  | catNil : Covered (.cat [])
  | catCons {k : Ast} {kids : List Ast} :
      Covered k → Covered (.cat kids) → Covered (.cat (k :: kids))
  | altOne {a : Ast} : Covered a → Covered (.alt [a])
  | altCons {a b : Ast} {rest : List Ast} :
      Covered a → Covered (.alt (b :: rest)) → Covered (.alt (a :: b :: rest))

/-- A fragment derivation is a subset witness. -/
theorem FragAt.covered {code : Array Inst} {a : Ast} {lo hi : Nat}
    (h : FragAt code a lo hi) : Covered a := by
  induction h with
  | chr _ => exact .chr _
  | catNil => exact .catNil
  | catCons _ _ ihk ihkids => exact .catCons ihk ihkids
  | altOne _ iha => exact .altOne iha
  | altCons _ _ _ _ iha ihrest => exact .altCons iha ihrest

/-- `mapM` over a list every element of which succeeds. -/
theorem mapM_eq_some {α β : Type _} {f : α → Option β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.mapM_cons, h x (List.mem_cons_self ..),
        mapM_eq_some xs fun y hy => h y (List.mem_cons_of_mem x hy)]
      rfl

/-- On the subset the spec search spends no fuel, writes no register, and
returns exactly the proto enumeration: every thread is the starting
registers at an `enum` position, in the same order. -/
theorem search_covered {c : Spec.SCtx} {a : Ast} (h : Covered a) :
    ∀ (fuel pos : Nat) (regs : Spec.Regs),
      Spec.search fuel c a pos regs =
        some ((enum c.s a pos).map fun p => ⟨p, regs⟩) := by
  induction h with
  | chr b =>
      intro fuel pos regs
      rw [Spec.search]
      simp only [enum]
      split <;> simp_all
  | catNil =>
      intro fuel pos regs
      rw [Spec.search, Spec.searchCat]
      simp [enum]
  | @catCons k kids ihkc ihkidsc ihk ihkids =>
      intro fuel pos regs
      have ihkids' : ∀ pos' (regs' : Spec.Regs),
          Spec.searchCat fuel c kids pos' regs' =
            some ((enum c.s (.cat kids) pos').map fun p => ⟨p, regs'⟩) := by
        intro pos' regs'
        have := ihkids fuel pos' regs'
        rwa [Spec.search] at this
      rw [Spec.search, Spec.searchCat, ihk fuel pos regs]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind]
      rw [mapM_eq_some _ fun (t : Spec.Thread) _ => ihkids' t.pos t.regs]
      simp only [Option.some.injEq]
      simp [enum, List.map_map, Function.comp_def, List.flatMap_def,
        List.map_flatten]
  | @altOne a hac iha =>
      intro fuel pos regs
      have iha' := iha fuel pos regs
      rw [Spec.search, Spec.searchAlt, iha']
      rw [Spec.searchAlt]
      simp [enum]
  | @altCons a b rest hac hrestc iha ihrest =>
      intro fuel pos regs
      have ihrest' : Spec.searchAlt fuel c (b :: rest) pos regs =
          some ((enum c.s (.alt (b :: rest)) pos).map fun p => ⟨p, regs⟩) := by
        have := ihrest fuel pos regs
        rwa [Spec.search] at this
      rw [Spec.search, Spec.searchAlt, iha fuel pos regs, ihrest']
      simp [enum, List.map_append]

/-! ## The compiler establishes the fragment relation

`compileNode` only ever appends to the code and patches cells it laid down
itself, so a finished subfragment survives the rest of the compilation
verbatim — that is `FragAt.mono` plus the prefix facts proven here. The
alternation chain needs its own strengthened statement, because the jump
cells of the earlier branches stay unpatched until the last branch closes:
`compileAlt`'s postcondition records that every collected jump ends up
pointing at the final stop, which is exactly the `hi` the chain's
`FragAt` wants. -/

private theorem getBang_push_lt (a : Array Inst) (x : Inst) {i : Nat}
    (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h]
  exact Array.getElem_push_lt h

private theorem getBang_push_eq (a : Array Inst) (x : Inst) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  exact Array.getElem_push_eq

private theorem getBang_modify_ne (a : Array Inst) (j : Nat)
    {f : Inst → Inst} {i : Nat} (h : i ≠ j) :
    (a.modify j f)[i]! = a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos (a.modify j f) i (by simpa using hi),
      getElem!_pos a i hi]
    exact Array.getElem_modify_of_ne (Ne.symm h) f
      (by simpa using hi)
  · rw [getElem!_neg (a.modify j f) i (by simpa using hi),
      getElem!_neg a i hi]

private theorem getBang_modify_eq (a : Array Inst) (j : Nat)
    {f : Inst → Inst} (h : j < a.size) :
    (a.modify j f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.modify j f) j (by simpa using h),
    getElem!_pos a j h]
  exact Array.getElem_modify_self f (by simpa using h)

/-- The state after an alternation's split is laid down and patched to
enter its branch: the two-step emit-then-patch of `compileAlt`, spelled as
one record so the proofs can name it. -/
private def altSplitSt (st : CState) : CState :=
  { st with code := ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
      (fun i => { i with arg := st.code.size + 1 })) }

/-- The branch region opened on top of it. -/
private def altBranchSt (inside : Nat) (st : CState) : CState :=
  { st with regions := (st.regions.push
      ⟨.branch, inside, st.code.size, st.code.size⟩) }

/-- The state right after a non-final branch's body: split, region, body. -/
private def altMid (arm : Ast) (inside : Nat) (st : CState) : CState :=
  compileNode arm st.regions.size (altBranchSt inside (altSplitSt st))

/-- And after its close: region shut, jump emitted, split's second arm
patched to the next link. -/
private def altOut (arm : Ast) (inside : Nat) (st : CState) : CState :=
  let stM := altMid arm inside st
  { stM with
    regions := (stM.regions.modify st.regions.size
      (fun r => { r with hi := stM.code.size }))
    code := ((stM.code.push ⟨.jump, 0, 0⟩).modify st.code.size
      (fun i => { i with alt := (stM.code.push ⟨.jump, 0, 0⟩).size })) }

private theorem compileAlt_cons_eq (arm next : Ast) (rest' : List Ast)
    (inside : Nat) (jumps : Array Nat) (st : CState) :
    compileAlt arm (next :: rest') inside jumps st =
      compileAlt next rest' inside
        (jumps.push (altMid arm inside st).code.size)
        (altOut arm inside st) := by
  rw [compileAlt]; rfl

private theorem compileAlt_nil_eq (arm : Ast) (inside : Nat)
    (jumps : Array Nat) (st : CState) :
    compileAlt arm [] inside jumps st =
      closeRegion
        (jumps.foldl
          (fun s pc => patch s pc fun i =>
            { i with arg := (compileNode arm st.regions.size
                (altBranchSt inside st)).code.size })
          (compileNode arm st.regions.size (altBranchSt inside st)))
        st.regions.size := by
  rw [compileAlt]; rfl

/-- Patching a batch of collected jumps: sizes stay put, untouched cells
stay put, and every named cell gets the new target — duplicates are
harmless because the patch is idempotent. -/
private theorem patchAll_facts (stop : Nat) :
    ∀ (js : List Nat) (st : CState),
      (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
        st).code.size = st.code.size ∧
      (∀ pc, pc ∉ js →
        (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
          st).code[pc]! = st.code[pc]!) ∧
      (∀ pc ∈ js, pc < st.code.size →
        (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
          st).code[pc]! = { st.code[pc]! with arg := stop })
  | [], st => by simp
  | j :: js', st => by
      obtain ⟨hsz, hpre, hhit⟩ := patchAll_facts stop js' (patch st j
        fun i => { i with arg := stop })
      have hpsz : (patch st j fun i => { i with arg := stop }).code.size =
          st.code.size := by
        simp [patch]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.foldl_cons, hsz, hpsz]
      · intro pc hpc
        simp only [List.mem_cons, not_or] at hpc
        rw [List.foldl_cons, hpre pc hpc.2]
        simp only [patch]
        exact getBang_modify_ne st.code j hpc.1
      · intro pc hpc hlt
        rw [List.foldl_cons]
        by_cases hj : pc = j
        · subst hj
          have hcell : (patch st pc fun i => { i with arg := stop }).code[pc]! =
              { st.code[pc]! with arg := stop } := by
            simp only [patch]
            exact getBang_modify_eq st.code pc hlt
          by_cases hin : pc ∈ js'
          · rw [hhit pc hin (by rw [hpsz]; exact hlt), hcell]
          · rw [hpre pc hin, hcell]
        · have hmem : pc ∈ js' := by
            rcases List.mem_cons.mp hpc with h' | h'
            · exact absurd h' hj
            · exact h'
          have hcell : (patch st j fun i => { i with arg := stop }).code[pc]! =
              st.code[pc]! := by
            simp only [patch]
            exact getBang_modify_ne st.code j hj
          rw [hhit pc hmem (by rw [hpsz]; exact hlt), hcell]

theorem covered_alt_mem : ∀ {arms : List Ast}, Covered (.alt arms) →
    ∀ x ∈ arms, Covered x := by
  intro arms
  induction arms with
  | nil => intro _ x hx; cases hx
  | cons y ys ihy =>
      intro h x hx
      cases h with
      | altOne hy =>
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hy
          · cases hx'
      | altCons hy hrest =>
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hy
          · exact ihy hrest x hx'

/-- What `compileAlt` does to the code, strengthened the way the chain
needs it: the collected jump cells — laid down by earlier links and still
blank — all end up pointing at the final stop, everything else below the
input size survives, and the new range is the chain's fragment. The node
recursion enters through `ih`, which `compileNode_facts` supplies. -/
private theorem compileAlt_facts {n : Nat}
    (ih : ∀ {a : Ast}, sizeOf a ≤ n → Covered a →
      ∀ (here : Nat) (st : CState),
        st.code.size ≤ (compileNode a here st).code.size ∧
        (∀ pc, pc < st.code.size →
          (compileNode a here st).code[pc]! = st.code[pc]!) ∧
        FragAt (compileNode a here st).code a st.code.size
          (compileNode a here st).code.size) :
    ∀ (rest : List Ast) (arm : Ast), sizeOf arm ≤ n → Covered arm →
      (∀ x ∈ rest, sizeOf x ≤ n ∧ Covered x) →
      ∀ (inside : Nat) (jumps : Array Nat) (st : CState),
        (∀ p ∈ jumps.toList, p < st.code.size) →
        st.code.size ≤ (compileAlt arm rest inside jumps st).code.size ∧
        (∀ pc, pc < st.code.size → pc ∉ jumps.toList →
          (compileAlt arm rest inside jumps st).code[pc]! = st.code[pc]!) ∧
        (∀ p ∈ jumps.toList,
          (compileAlt arm rest inside jumps st).code[p]! =
            { st.code[p]! with
                arg := (compileAlt arm rest inside jumps st).code.size }) ∧
        FragAt (compileAlt arm rest inside jumps st).code (.alt (arm :: rest))
          st.code.size (compileAlt arm rest inside jumps st).code.size := by
  intro rest
  induction rest with
  | nil =>
      intro arm hszarm hcarm _ inside jumps st hj
      obtain ⟨hle, hpre, hfrag⟩ :=
        ih hszarm hcarm st.regions.size (altBranchSt inside st)
      have hbc : (altBranchSt inside st).code = st.code := rfl
      rw [hbc] at hle hpre hfrag
      obtain ⟨hfsz, hfpre, hfhit⟩ :=
        patchAll_facts
          (compileNode arm st.regions.size (altBranchSt inside st)).code.size
          jumps.toList
          (compileNode arm st.regions.size (altBranchSt inside st))
      have hcode : (compileAlt arm [] inside jumps st).code =
          (jumps.toList.foldl (fun s pc => patch s pc fun i =>
            { i with arg := (compileNode arm st.regions.size
                (altBranchSt inside st)).code.size })
            (compileNode arm st.regions.size (altBranchSt inside st))).code := by
        rw [compileAlt_nil_eq, ← Array.foldl_toList]
        rfl
      have hsize : (compileAlt arm [] inside jumps st).code.size =
          (compileNode arm st.regions.size
            (altBranchSt inside st)).code.size := by
        rw [hcode, hfsz]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hsize]; exact hle
      · intro pc hpc hnotin
        rw [hcode, hfpre pc hnotin]
        exact hpre pc hpc
      · intro p hp
        have hplt := hj p hp
        rw [hcode, hfhit p hp (by omega), hpre p hplt, hfsz]
      · rw [hsize]
        refine .altOne (hfrag.mono ?_)
        intro pc h1 h2
        rw [hcode]
        exact hfpre pc fun hin => absurd (hj pc hin) (by omega)
  | cons bb rest' ihrest =>
      intro arm hszarm hcarm helems inside jumps st hj
      rw [compileAlt_cons_eq]
      -- The laid-down prefix: split cell, branch body, jump cell.
      have hsplitsz : (altSplitSt st).code.size = st.code.size + 1 := by
        simp [altSplitSt]
      obtain ⟨hle, hpre, hfrag⟩ :=
        ih hszarm hcarm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st))
      have hbc : (altBranchSt inside (altSplitSt st)).code =
          (altSplitSt st).code := rfl
      rw [hbc, hsplitsz] at hle hpre hfrag
      have hmid : compileNode arm (altSplitSt st).regions.size
            (altBranchSt inside (altSplitSt st)) = altMid arm inside st := rfl
      rw [hmid] at hle hpre hfrag
      -- Cells of the pre-split state.
      have hsplit_cell : (altSplitSt st).code[st.code.size]! =
          ⟨.split, st.code.size + 1, 0⟩ := by
        show ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
            (fun i => { i with arg := st.code.size + 1 }))[st.code.size]! =
          ⟨.split, st.code.size + 1, 0⟩
        rw [getBang_modify_eq _ st.code.size (by simp), getBang_push_eq]
      have hsplit_pre : ∀ pc, pc < st.code.size →
          (altSplitSt st).code[pc]! = st.code[pc]! := by
        intro pc hpc
        show ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
            (fun i => { i with arg := st.code.size + 1 }))[pc]! = st.code[pc]!
        rw [getBang_modify_ne _ st.code.size (by omega),
          getBang_push_lt _ _ hpc]
      -- Cells of the state handed to the rest of the chain.
      have houtc : (altOut arm inside st).code =
          ((altMid arm inside st).code.push ⟨.jump, 0, 0⟩).modify st.code.size
            (fun i => { i with
              alt := ((altMid arm inside st).code.push ⟨.jump, 0, 0⟩).size }) :=
        rfl
      have houtsz : (altOut arm inside st).code.size =
          (altMid arm inside st).code.size + 1 := by
        rw [houtc]; simp
      have hout_jump :
          (altOut arm inside st).code[(altMid arm inside st).code.size]! =
            ⟨.jump, 0, 0⟩ := by
        rw [houtc, getBang_modify_ne _ st.code.size (by omega),
          getBang_push_eq]
      have hout_split : (altOut arm inside st).code[st.code.size]! =
          ⟨.split, st.code.size + 1, (altMid arm inside st).code.size + 1⟩ := by
        rw [houtc, getBang_modify_eq _ st.code.size (by simp; omega),
          getBang_push_lt _ _ (by omega), hpre st.code.size (by omega),
          hsplit_cell]
        simp
      have hout_pre : ∀ pc, pc < (altMid arm inside st).code.size →
          pc ≠ st.code.size →
          (altOut arm inside st).code[pc]! =
            (altMid arm inside st).code[pc]! := by
        intro pc hpc hne
        rw [houtc, getBang_modify_ne _ st.code.size hne,
          getBang_push_lt _ _ hpc]
      -- The rest of the chain, one link shorter.
      obtain ⟨hszbb, hcbb⟩ := helems bb (List.mem_cons_self ..)
      obtain ⟨cle, cpre, chit, cfrag⟩ :=
        ihrest bb hszbb hcbb
          (fun x hx => helems x (List.mem_cons_of_mem bb hx))
          inside (jumps.push (altMid arm inside st).code.size)
          (altOut arm inside st)
          (by
            intro p hp
            rw [Array.toList_push] at hp
            rcases List.mem_append.mp hp with hp' | hp'
            · have := hj p hp'
              omega
            · rw [List.mem_singleton] at hp'
              omega)
      rw [houtsz] at cle cpre cfrag
      have hmem_push : ∀ p,
          p ∈ (jumps.push (altMid arm inside st).code.size).toList ↔
          (p ∈ jumps.toList ∨ p = (altMid arm inside st).code.size) := by
        intro p
        rw [Array.toList_push, List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_, ?_, ?_⟩
      · omega
      · intro pc hpc hnotin
        rw [cpre pc (by omega) (by
              rw [hmem_push]
              rintro (h' | rfl)
              · exact hnotin h'
              · omega),
          hout_pre pc (by omega) (by omega), hpre pc (by omega),
          hsplit_pre pc hpc]
      · intro p hp
        have hplt := hj p hp
        have hcell := chit p ((hmem_push p).mpr (.inl hp))
        rw [hcell, hout_pre p (by omega) (by omega), hpre p (by omega),
          hsplit_pre p hplt]
      · refine .altCons (j := (altMid arm inside st).code.size) ?_ ?_ ?_ ?_
        · rw [cpre st.code.size (by omega) (by
              rw [hmem_push]
              rintro (h' | h')
              · have := hj st.code.size h'; omega
              · omega)]
          exact hout_split
        · refine hfrag.mono ?_
          intro pc h1 h2
          rw [cpre pc (by omega) (by
                rw [hmem_push]
                rintro (h' | h')
                · have := hj pc h'; omega
                · omega),
            hout_pre pc (by omega) (by omega)]
        · have hcell := chit (altMid arm inside st).code.size
            ((hmem_push (altMid arm inside st).code.size).mpr (.inr rfl))
          rw [hcell, hout_jump]
        · exact cfrag

/-- Compiling a covered node grows the code, preserves what was already
there, and lays down a fragment of the node over the new range. The
induction is on a size bound rather than the `Covered` derivation so the
alternation case can hand single arms to `compileAlt_facts` without a
mutual proof. -/
theorem compileNode_facts :
    ∀ (n : Nat) {a : Ast}, sizeOf a ≤ n → Covered a →
    ∀ (here : Nat) (st : CState),
      st.code.size ≤ (compileNode a here st).code.size ∧
      (∀ pc, pc < st.code.size →
        (compileNode a here st).code[pc]! = st.code[pc]!) ∧
      FragAt (compileNode a here st).code a st.code.size
        (compileNode a here st).code.size := by
  intro n
  induction n with
  | zero =>
      intro a hsz hc
      exfalso
      cases hc <;> simp at hsz
  | succ n ih =>
      intro a hsz hc here st
      cases hc with
      | chr b =>
          have hcode : (compileNode (.chr b) here st).code =
              st.code.push ⟨.chr, b.toNat, 0⟩ := by
            rw [compileNode]; rfl
          refine ⟨?_, ?_, ?_⟩
          · rw [hcode, Array.size_push]; omega
          · intro pc hpc
            rw [hcode]
            exact getBang_push_lt _ _ hpc
          · rw [hcode, Array.size_push]
            exact .chr (getBang_push_eq st.code _)
      | catNil =>
          have hcode : compileNode (.cat []) here st = st := by
            rw [compileNode, compileCat]
          rw [hcode]
          exact ⟨Nat.le_refl _, fun _ _ => rfl, .catNil⟩
      | @catCons k kids hck hckids =>
          have hszk : sizeOf k ≤ n ∧ sizeOf (Ast.cat kids) ≤ n := by
            simp at hsz ⊢
            omega
          have hunfold : compileNode (Ast.cat kids) here
              (compileNode k here st) =
              compileCat kids here (compileNode k here st) := by
            rw [compileNode]
          have hstep : compileNode (.cat (k :: kids)) here st =
              compileNode (.cat kids) here (compileNode k here st) := by
            rw [compileNode, compileCat, hunfold]
          obtain ⟨hle1, hpre1, hfrag1⟩ := ih hszk.1 hck here st
          obtain ⟨hle2, hpre2, hfrag2⟩ :=
            ih hszk.2 hckids here (compileNode k here st)
          rw [hstep]
          refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
          · intro pc hpc
            rw [hpre2 pc (by omega), hpre1 pc hpc]
          · exact .catCons
              (hfrag1.mono fun pc _ h2 => hpre2 pc (by omega))
              hfrag2
      | @altOne a1 hca =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have hstep : compileNode (.alt [a1]) here st =
              compileNode a1 here st := by
            rw [compileNode]
          obtain ⟨hle, hpre, hfrag⟩ := ih hsza hca here st
          rw [hstep]
          exact ⟨hle, hpre, .altOne hfrag⟩
      | @altCons a1 b rest hca hcrest =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have helems : ∀ x ∈ b :: rest, sizeOf x ≤ n ∧ Covered x := by
            intro x hx
            refine ⟨?_, covered_alt_mem hcrest x hx⟩
            have := List.sizeOf_lt_of_mem hx
            simp at hsz this ⊢
            omega
          have hstep : compileNode (.alt (a1 :: b :: rest)) here st =
              closeRegion
                (compileAlt a1 (b :: rest) st.regions.size #[]
                  { st with regions := (st.regions.push
                      ⟨.alt, here, st.code.size, st.code.size⟩) })
                st.regions.size := by
            rw [compileNode] <;> first | rfl | simp
          obtain ⟨hle, hpre, _, hfrag⟩ :=
            compileAlt_facts (fun h hc => ih h hc) (b :: rest) a1 hsza hca
              helems st.regions.size #[]
              { st with regions := (st.regions.push
                  ⟨.alt, here, st.code.size, st.code.size⟩) }
              (by simp)
          rw [hstep]
          exact ⟨hle, fun pc hpc => hpre pc hpc (by simp), hfrag⟩

/-! ## The compiled pattern as a whole: fragment, accept, nothing else -/

/-- The opcodes the proto covers, as a predicate on cells. -/
def SubsetOp (op : Op) : Prop :=
  op = .chr ∨ op = .split ∨ op = .jump ∨ op = .accept

/-- Every cell a fragment pins is one of the covered opcodes. -/
theorem FragAt.ops {code : Array Inst} {a : Ast} {lo hi : Nat}
    (h : FragAt code a lo hi) :
    ∀ pc, lo ≤ pc → pc < hi → SubsetOp (code[pc]!).op := by
  induction h with
  | @chr b lo hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      exact .inl (by rw [hcell])
  | catNil =>
      intro pc h1 h2
      omega
  | @catCons k kids lo mid hi hk hkids ihk ihkids =>
      intro pc h1 h2
      by_cases hcut : pc < mid
      · exact ihk pc h1 hcut
      · exact ihkids pc (by omega) h2
  | altOne ha iha =>
      exact iha
  | @altCons a b rest lo j hi hsplit ha hjump hrest iha ihrest =>
      intro pc h1 h2
      have hb1 := ha.le
      have hb2 := hrest.le
      by_cases hlo : pc = lo
      · subst hlo
        exact .inr (.inl (by rw [hsplit]))
      · by_cases hltj : pc < j
        · exact iha pc (by omega) hltj
        · by_cases hjq : pc = j
          · subst hjq
            exact .inr (.inr (.inl (by rw [hjump])))
          · exact ihrest pc (by omega) h2

/-- The state `compile` hands the root node: empty program, root region
open. -/
private def rootSt : CState :=
  { code := #[], classes := #[], reps := #[],
    regions := #[(⟨.root, none32, 0, 0⟩ : Region)] }

private theorem compile_code {p : Pat} (hend : p.opts.endanchored = false) :
    (compile p).code =
      (compileNode p.root 0 rootSt).code.push ⟨.accept, 0, 0⟩ := by
  simp only [compile, hend]
  rfl

/-- The compiled form of a covered, end-open pattern: the root's fragment
from 0, one accept cell after it, and no other opcode anywhere — the reads
past the end answer the default cell, which is covered too. -/
theorem compile_shape {p : Pat} (hc : Covered p.root)
    (hend : p.opts.endanchored = false) :
    FragAt (compile p).code p.root 0 (compileNode p.root 0 rootSt).code.size ∧
    (compile p).code[(compileNode p.root 0 rootSt).code.size]! =
      ⟨.accept, 0, 0⟩ ∧
    (∀ pc : Nat, SubsetOp ((compile p).code[pc]!).op) := by
  obtain ⟨hle, hpre, hfrag⟩ :=
    compileNode_facts (sizeOf p.root) (Nat.le_refl _) hc 0 rootSt
  have hzero : rootSt.code.size = 0 := rfl
  rw [hzero] at hfrag
  have hfrag' : FragAt (compile p).code p.root 0
      (compileNode p.root 0 rootSt).code.size := by
    refine hfrag.mono ?_
    intro pc _ h2
    rw [compile_code hend]
    exact getBang_push_lt _ _ h2
  refine ⟨hfrag', ?_, ?_⟩
  · rw [compile_code hend]
    exact getBang_push_eq _ _
  · intro pc
    by_cases hlt : pc < (compileNode p.root 0 rootSt).code.size
    · exact hfrag'.ops pc (Nat.zero_le _) hlt
    · by_cases heq : pc = (compileNode p.root 0 rootSt).code.size
      · subst heq
        rw [compile_code hend, getBang_push_eq]
        exact .inr (.inr (.inr rfl))
      · rw [compile_code hend,
          getElem!_neg _ pc (by rw [Array.size_push]; omega)]
        exact .inl rfl

/-! ## From the metered VM to the mirror

On the covered opcodes the machine's mutable state collapses: no
instruction ever writes a register through the trail, so the trail stays
empty, every mark is vacuous, replay on backtrack is free and restores
nothing, and a backtrack entry means exactly a (pc, pos) resume point.
The bridge below runs on the metered VM's own fuel — `btStep` and
`btFail` pass fuel to each other precisely the way `run` and `dispatch`
do, so the mirrored run needs no fuel slack at all. -/

/-- The mirror's reading of the backtrack stack: resume points, newest
first. -/
def stackOf (bt : Array BtEntry) : List (Nat × Nat) :=
  (bt.toList.map fun e => (e.pc, e.pos)).reverse

theorem stackOf_push (bt : Array BtEntry) (e : BtEntry) :
    stackOf (bt.push e) = (e.pc, e.pos) :: stackOf bt := by
  simp [stackOf, Array.toList_push]

theorem stackOf_pop (bt : Array BtEntry) (h : bt.size ≠ 0) :
    stackOf bt = (bt.back!.pc, bt.back!.pos) :: stackOf bt.pop := by
  have hne : bt.toList ≠ [] := by
    intro he
    exact h (by simpa using congrArg List.length he)
  have hback : bt.toList.getLast hne = bt.back! := by
    rw [List.getLast_eq_getElem]
    show _ = bt[bt.size - 1]!
    rw [getElem!_pos bt (bt.size - 1) (by omega)]
    simp
  have hlast : bt.toList = bt.toList.dropLast ++ [bt.back!] := by
    rw [← hback]
    exact (List.dropLast_concat_getLast hne).symm
  unfold stackOf
  conv => lhs; rw [hlast]
  rw [List.map_append, List.reverse_append]
  simp [Array.toList_pop]

/-- What a successful `fork` did to the state: one entry pushed, the trail
untouched. -/
theorem fork_shape {st st' : BtSt} {lim : Limits} {target pos : Nat}
    (h : fork st lim target pos = some st') :
    st'.bt = st.bt.push ⟨target, pos, st.trail.size⟩ ∧
    st'.trail = st.trail := by
  rw [fork] at h
  cases hp : pushBt st lim target pos st.trail.size with
  | none => rw [hp] at h; cases h
  | some mid =>
      rw [hp] at h
      cases h
      rw [pushBt] at hp
      split at hp
      · cases hp
      · cases hg : chargeGrow st.btCap st.bt.size btSize maxStack st.m lim with
        | none => rw [hg] at hp; cases hp
        | some pr =>
            obtain ⟨m2, cap2⟩ := pr
            rw [hg] at hp
            cases hp
            exact ⟨rfl, rfl⟩

/-- Forget the machine state, keep the verdict; `none` is a budget stop. -/
def verdict : AttemptOut → Option Out
  | .found e _ => some (.found e)
  | .exhausted _ => some .nomatch
  | .exceeded _ => none

/-- One attempt of the metered VM, mirrored: whenever `btStep` completes —
found or exhausted, not exceeded — the unmetered mirror completes with the
same verdict from the mirrored configuration, on the same fuel. The
accept-refusal options are off, which is the proto's precise reading of
"up to the accept filter". -/
theorem btStep_mirror {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt : Nat}
    (hsub : ∀ pc : Nat, SubsetOp (re.code[pc]!).op)
    (hne : mo.notempty = false) (hnes : mo.notemptyAtStart = false) :
    ∀ (fuel : Nat) (pc pos : Nat) (st : BtSt), st.trail = #[] →
      ∀ r, verdict (btStep re s mo lim start attempt fuel pc pos st) = some r →
        run re.code s fuel pc pos (stackOf st.bt) = some r := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc pos st htrail r h
      rw [btStep] at h
      simp [verdict] at h
  | succ n ih =>
      intro pc pos st htrail r h
      have hfail : ∀ (st1 : BtSt), st1.trail = #[] → ∀ r',
          verdict (btFail re s mo lim start attempt n st1) = some r' →
          dispatch re.code s n (stackOf st1.bt) = some r' := by
        intro st1 htrail1 r' h'
        rw [btFail] at h'
        by_cases hsz : st1.bt.size = 0
        · rw [dif_pos hsz] at h'
          simp only [verdict, Option.some.injEq] at h'
          have hbt : st1.bt = #[] := Array.size_eq_zero_iff.mp hsz
          rw [hbt, ← h',
            show stackOf (#[] : Array BtEntry) = [] from rfl, dispatch]
        · rw [dif_neg hsz] at h'
          rw [htrail1] at h'
          simp only [Array.size_empty, Nat.zero_sub, Nat.zero_mul,
            gt_iff_lt, Nat.not_lt_zero, if_false] at h'
          rw [replayTrail] at h'
          simp only [Array.size_empty, Nat.zero_le, if_pos] at h'
          rw [stackOf_pop st1.bt hsz, dispatch]
          split at h'
          · exact ih st1.bt.back!.pc st1.bt.back!.pos _ rfl r' h'
          · exact ih st1.bt.back!.pc st1.bt.back!.pos _ rfl r' h'
      rw [btStep] at h
      split at h
      · simp [verdict] at h
      · rcases hsub pc with hop | hop | hop | hop
        · -- chr
          simp only [hop] at h
          rw [run]
          simp only [hop]
          by_cases hcond : (pos < s.size &&
              (byteAt s pos == UInt8.ofNat (re.code[pc]!).arg)) = true
          · rw [if_pos hcond] at h ⊢
            exact ih (pc + 1) (pos + 1)
              { st with m := { st.m with cost := st.m.cost + 1 } } htrail r h
          · rw [if_neg hcond] at h ⊢
            exact hfail
              { st with m := { st.m with cost := st.m.cost + 1 } } htrail r h
        · -- split
          simp only [hop] at h
          rw [run]
          simp only [hop]
          cases hf : fork { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.code[pc]!).alt pos with
          | none => rw [hf] at h; simp [verdict] at h
          | some st2 =>
              rw [hf] at h
              obtain ⟨hbt2, htr2⟩ := fork_shape hf
              have hrun := ih (re.code[pc]!).arg pos st2
                (by rw [htr2]; exact htrail) r h
              rw [hbt2, stackOf_push] at hrun
              exact hrun
        · -- jump
          simp only [hop] at h
          rw [run]
          simp only [hop]
          exact ih (re.code[pc]!).arg pos
            { st with m := { st.m with cost := st.m.cost + 1 } } htrail r h
        · -- accept
          simp only [hop] at h
          rw [hne, hnes] at h
          simp [verdict] at h
          subst h
          rw [run]
          simp only [hop]

/-! ## The composed statement, per attempt -/

/-- Dispatching a pending list of threads all parked on the accept cell:
the first one wins, an empty list is a no-match. -/
theorem resumes_accept {code : Array Inst} {s : ByteArray} {hi : Nat}
    (hop : (code[hi]!).op = .accept) :
    ∀ ps : List Nat, Resumes code s (ps.map fun p => (hi, p))
      (match ps with | [] => .nomatch | p :: _ => .found p)
  | [] => resumes_nil.mpr rfl
  | _ :: _ => resumes_cons.mpr ((runs_accept hop).mpr rfl)

/-- The proto's S-8, per attempt: on a covered, end-open pattern, with the
empty-match refusals off, a completed `btStep` attempt from the compiled
entry point answers exactly what the spec's search enumerates — found at
the head of the preference-ordered list, or no-match when the list is
empty. Resource questions never enter: `verdict ... = some r` is
precisely "the attempt completed", and the conclusion holds for every
budget that lets it complete. -/
theorem attempt_refines {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt fuel : Nat} {st : BtSt} {r : Out}
    (hc : Covered p.root) (hend : p.opts.endanchored = false)
    (hne : mo.notempty = false) (hnes : mo.notemptyAtStart = false)
    (hbt : st.bt = #[]) (htrail : st.trail = #[])
    (h : verdict (btStep (compile p) s mo lim start attempt fuel 0 attempt st) =
      some r) :
    ∀ (F : Nat) (regs : Spec.Regs),
      Spec.search F ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root
          attempt regs =
        some ((enum s p.root attempt).map fun q => ⟨q, regs⟩) ∧
      r = (match enum s p.root attempt with
           | [] => .nomatch
           | q :: _ => .found q) := by
  obtain ⟨hfrag, haccept, hsub⟩ := compile_shape hc hend
  have hrun := btStep_mirror hsub hne hnes fuel 0 attempt st htrail r h
  rw [hbt] at hrun
  have hruns : Runs (compile p).code s 0 attempt [] r := ⟨fuel, by
    rwa [show stackOf (#[] : Array BtEntry) = [] from rfl] at hrun⟩
  have hres := (frag_runs hfrag attempt [] r).mp hruns
  rw [List.append_nil] at hres
  have hacc := resumes_accept (s := s) (by rw [haccept])
    (enum s p.root attempt)
  intro F regs
  exact ⟨search_covered hc F attempt regs, resumes_det hres hacc⟩

end Pcrevera.RefineProto
