import Pcrevera.Ref.Compile
import Pcrevera.Proofs.PikeTermination
import Batteries.Tactic.OpenPrivate

/-!
# The bumpalong bit agrees between the layers (S-7 / R-1 seam)

`compile` closes codegen by asking `scanFirst` whether a match can begin
by consuming a CR; the spec asks `crWalk` the same question of the tree,
and `skipsAttempt` reads the answer. This file proves the two analyses
agree: `crFirst_agrees` says `(compile p).crfirst = p.crFirst` for every
pattern without an `.alt []` subterm, so the bumpalong rule skips the
same positions no matter which layer decides.

The proof goes through the ε-graph of the bytecode. `succs` restates
which pcs `markSeen` is handed when a given instruction pops, `crHead`
which instructions answer the scan by themselves, and the worklist is
characterized as reachability: `scanFirst` is true exactly when some
ε-reachable pc is a CR-capable head (`scanFirst_iff`). One direction
walks the fuel down carrying `Reach` witnesses, with PikeTermination's
variant showing the conservative fuel-zero `true` is never consulted;
the other maintains the processed set — marked, off the worklist, no
witness, successors all marked — and closes it under ε-steps.

The compiled side is then pinned by `Frag`, a relation reading each
construct's laid-down shape off `compileNode` the way RefineProto's
`FragAt` does, extended to the whole wave 1 AST, the class table and
the repetition table included. Two inductions over a derivation finish
the job: `Frag.closed` builds the fragment's ε-closure and reads
`crWalk` off it, and `Frag.reach` exhibits the walks `crWalk` promises.
`compileNode_facts` proves the compiler establishes the relation, and
the top-level assembly threads the trailing `eod`/`accept` cells, whose
reachability is exactly the transparency half of `crWalk`.
-/

open private emit patch openRegion closeRegion dropEmptyRegion from Pcrevera.Ref.Compile

namespace Pcrevera.CrFirst

open Pcrevera Pcrevera.Ref Pcrevera.Spec

/-! ## The well-formedness this file needs

The compiler emits nothing for an empty alternation, which ε-walks like
`nul`, while `crWalk` folds it to "matches nothing"; the two analyses
disagree on that shape and on nothing else. The engine's parser never
produces it — group bodies and branches always hold at least a `nul` —
so ruling it out is the whole well-formedness story here. -/

/-- No `.alt []` anywhere in the tree. -/
def NoEmptyAlt : Ast → Prop
  | .cat kids => ∀ k ∈ kids, NoEmptyAlt k
  | .alt arms => arms ≠ [] ∧ ∀ a ∈ arms, NoEmptyAlt a
  | .grp _ body => NoEmptyAlt body
  | .rep _ _ _ body => NoEmptyAlt body
  | _ => True
termination_by a => sizeOf a
decreasing_by
  all_goals simp
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)

/-! ## The ε-graph of a program

`scanFirst`'s worklist walks the non-consuming transitions. The two
functions below restate one instruction's contribution — the pcs it asks
`markSeen` to add, and whether it answers the scan on its own — so the
loop can be described as plain reachability. -/

/-- The ε-successors of one instruction: exactly the pcs `scanFirst`
marks when this one pops. Consuming heads and Accept expand to nothing;
the walk stops where a first byte would be read or a match would end. -/
def succs (code : Array Inst) (reps : Array RepInfo) (pc : Nat) : List Nat :=
  let inst := code[pc]!
  match inst.op with
  | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .accept => []
  | .split => [inst.arg, inst.alt]
  | .jump => [inst.arg]
  | .repLoop =>
      let rep := reps[inst.arg]!
      if rep.lo == 0 then [rep.body, rep.after] else [rep.body]
  | .repNext =>
      let rep := reps[inst.arg]!
      [rep.head, rep.after]
  | _ => [pc + 1]

/-- Does this instruction answer the scan by itself: a consuming head
whose first byte can be CR, or one of the conservative yeses — dot, \R,
Accept. -/
def crHead (code : Array Inst) (classes : Array UInt8) (pc : Nat) : Bool :=
  let inst := code[pc]!
  match inst.op with
  | .chr | .chrCI => inst.arg == 0x0D
  | .cls => classes[inst.arg * 32 + 1]! &&& 0x20 != 0
  | .any | .anyNoNL | .bsr | .accept => true
  | _ => false

/-- One ε-step, in range on both ends: an edge `markSeen` accepts. -/
def Step (code : Array Inst) (reps : Array RepInfo) (p q : Nat) : Prop :=
  p < code.size ∧ q < code.size ∧ q ∈ succs code reps p

/-- ε-reachability along `Step`. -/
inductive Reach (code : Array Inst) (reps : Array RepInfo) : Nat → Nat → Prop where
  | refl (pc : Nat) : Reach code reps pc pc
  | tail {p q r : Nat} : Reach code reps p q → Step code reps q r →
      Reach code reps p r

theorem Reach.trans {code : Array Inst} {reps : Array RepInfo} {p q r : Nat}
    (h₁ : Reach code reps p q) (h₂ : Reach code reps q r) :
    Reach code reps p r := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

theorem Reach.single {code : Array Inst} {reps : Array RepInfo} {p q : Nat}
    (h : Step code reps p q) : Reach code reps p q :=
  .tail (.refl p) h

theorem Reach.head {code : Array Inst} {reps : Array RepInfo} {p q r : Nat}
    (h : Step code reps p q) (h₂ : Reach code reps q r) :
    Reach code reps p r :=
  (Reach.single h).trans h₂

/-- A set closed under ε-steps swallows every walk that starts inside. -/
theorem Reach.mem_closed {code : Array Inst} {reps : Array RepInfo}
    {S : Nat → Prop}
    (hcl : ∀ x, S x → ∀ y, Step code reps x y → S y) {p q : Nat}
    (hp : S p) (h : Reach code reps p q) : S q := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact hcl _ ih _ hs

/-- The source of a proper walk is in range. -/
theorem Reach.src_lt {code : Array Inst} {reps : Array RepInfo} {p q : Nat}
    (h : Reach code reps p q) (hne : p ≠ q) : p < code.size := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail q r hr hs ih =>
      by_cases hpq : p = q
      · subst hpq
        exact hs.1
      · exact ih hpq

/-! ## Reading `markSeen` -/

private theorem getBang_set!_self {α : Type _} [Inhabited α] (a : Array α)
    (x : α) {i : Nat} (h : i < a.size) : (a.set! i x)[i]! = x := by
  rw [Array.set!_eq_setIfInBounds,
    getElem!_pos (a.setIfInBounds i x) i (by simpa using h)]
  exact Array.getElem_setIfInBounds_self _

private theorem getBang_set!_ne {α : Type _} [Inhabited α] (a : Array α)
    (x : α) {i j : Nat} (h : j ≠ i) : (a.set! i x)[j]! = a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.setIfInBounds i x) j (by simpa using hj),
      getElem!_pos a j hj]
    exact Array.getElem_setIfInBounds_ne hj fun he => h he.symm
  · rw [getElem!_neg (a.setIfInBounds i x) j (by simpa using hj),
      getElem!_neg a j hj]

theorem markSeen_size (code : Array Inst) (seen : Array Bool)
    (pending : List Nat) (pc : Nat) :
    (markSeen code seen pending pc).1.size = seen.size := by
  unfold markSeen
  split
  · rfl
  split
  · rfl
  · exact Array.size_set! ..

theorem markSeen_grows {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} (x : Nat) (hx : seen[x]! = true) :
    (markSeen code seen pending pc).1[x]! = true := by
  unfold markSeen
  split
  · exact hx
  split
  · exact hx
  · rename_i hin hnew
    by_cases hxpc : x = pc
    · subst hxpc
      exact absurd hx hnew
    · rw [getBang_set!_ne seen true hxpc]
      exact hx

theorem markSeen_marked {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} (hsz : seen.size = code.size)
    (h : pc < code.size) :
    (markSeen code seen pending pc).1[pc]! = true := by
  unfold markSeen
  split
  · omega
  split
  · assumption
  · exact getBang_set!_self seen true (by omega)

/-- What a mark did to the visited set, read backwards. -/
theorem markSeen_seen_of {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} {x : Nat}
    (hx : (markSeen code seen pending pc).1[x]! = true) :
    seen[x]! = true ∨ x = pc := by
  unfold markSeen at hx
  split at hx
  · exact .inl hx
  split at hx
  · exact .inl hx
  · by_cases hxpc : x = pc
    · exact .inr hxpc
    · rw [getBang_set!_ne seen true hxpc] at hx
      exact .inl hx

/-- What a mark did to the worklist, read backwards. -/
theorem markSeen_mem_of {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} {x : Nat}
    (hx : x ∈ (markSeen code seen pending pc).2) :
    x ∈ pending ∨ (x = pc ∧ pc < code.size ∧ seen[pc]! = false) := by
  unfold markSeen at hx
  split at hx
  · exact .inl hx
  split at hx
  · exact .inl hx
  · rename_i hin hnew
    rcases List.mem_cons.mp hx with h | h
    · exact .inr ⟨h, by omega, by simpa using hnew⟩
    · exact .inl h

theorem markSeen_mem_mono {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} {x : Nat} (hx : x ∈ pending) :
    x ∈ (markSeen code seen pending pc).2 := by
  unfold markSeen
  split
  · exact hx
  split
  · exact hx
  · exact List.mem_cons_of_mem _ hx

theorem markSeen_mem_self {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} (h : pc < code.size)
    (hf : ¬ seen[pc]! = true) :
    pc ∈ (markSeen code seen pending pc).2 := by
  unfold markSeen
  rw [if_neg (by omega), if_neg hf]
  exact List.mem_cons_self ..

/-! ## The worklist is reachability

The two directions of `scanFirst_iff`, each an induction down the fuel.
The completeness half carries the processed-set invariant `Done`; the
soundness half carries `Reach` witnesses for the whole worklist and
PikeTermination's variant, which rules the fuel-zero `true` out. -/

/-- The invariant of the completeness direction: worklist pcs are in
range, marked, and pairwise distinct. -/
structure WInv (code : Array Inst) (seen : Array Bool)
    (pending : List Nat) : Prop where
  size : seen.size = code.size
  mem : ∀ pc ∈ pending, pc < code.size ∧ seen[pc]! = true
  nodup : pending.Nodup

theorem WInv.mark {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} (h : WInv code seen pending) (pc : Nat) :
    WInv code (markSeen code seen pending pc).1
      (markSeen code seen pending pc).2 := by
  refine ⟨(markSeen_size ..).trans h.size, ?_, ?_⟩
  · intro x hx
    rcases markSeen_mem_of hx with h' | ⟨rfl, hlt, _⟩
    · obtain ⟨h1, h2⟩ := h.mem x h'
      exact ⟨h1, markSeen_grows x h2⟩
    · exact ⟨hlt, markSeen_marked h.size hlt⟩
  · unfold markSeen
    split
    · exact h.nodup
    split
    · exact h.nodup
    · rename_i hin hnew
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, h.nodup⟩
      have := (h.mem pc hmem).2
      simp [this] at hnew

/-- The processed pcs so far: marked, off the worklist, no witness, and
their ε-successors all marked or out of range. -/
def Done (code : Array Inst) (classes : Array UInt8) (reps : Array RepInfo)
    (seen : Array Bool) (pending : List Nat) : Prop :=
  ∀ pc, pc < code.size → seen[pc]! = true → pc ∉ pending →
    crHead code classes pc = false ∧
      ∀ q ∈ succs code reps pc, q < code.size → seen[q]! = true

/-- With the worklist drained, the processed set is ε-closed and holds
no witness, so nothing reachable from it is one either. -/
theorem done_no_witness {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {seen : Array Bool}
    (hdone : Done code classes reps seen []) {p q : Nat}
    (hp : seen[p]! = true) (hplt : p < code.size)
    (hreach : Reach code reps p q) : crHead code classes q = false := by
  have hcl : ∀ x, (x < code.size ∧ seen[x]! = true) →
      ∀ y, Step code reps x y → (y < code.size ∧ seen[y]! = true) := by
    rintro x ⟨hx1, hx2⟩ y ⟨_, hy, hmem⟩
    exact ⟨hy, (hdone x hx1 hx2 (List.not_mem_nil)).2 y hmem hy⟩
  have hq := Reach.mem_closed hcl ⟨hplt, hp⟩ hreach
  exact (hdone q hq.1 hq.2 (List.not_mem_nil)).1

/-- Popping `pc` and marking a cover of its successors keeps the
processed invariant, whatever mix of `markSeen` calls built the new
state. -/
theorem done_expand {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {seen seen' : Array Bool} {pc : Nat}
    {pending pending' : List Nat}
    (hdone : Done code classes reps seen (pc :: pending))
    (hpop : crHead code classes pc = false)
    (hsucc : ∀ q ∈ succs code reps pc, q < code.size → seen'[q]! = true)
    (hgrow : ∀ x : Nat, seen[x]! = true → seen'[x]! = true)
    (hback : ∀ x : Nat, seen'[x]! = true → seen[x]! = true ∨ x ∈ pending')
    (hkeep : ∀ x ∈ pending, x ∈ pending') :
    Done code classes reps seen' pending' := by
  intro p hp hpseen hpnot
  by_cases hppc : p = pc
  · subst hppc
    exact ⟨hpop, hsucc⟩
  · have hpold : seen[p]! = true := by
      rcases hback p hpseen with h | h
      · exact h
      · exact absurd h hpnot
    have hout : p ∉ pc :: pending := by
      intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hppc h
      · exact hpnot (hkeep _ h)
    obtain ⟨h1, h2⟩ := hdone p hp hpold hout
    exact ⟨h1, fun q hq hlt => hgrow _ (h2 q hq hlt)⟩

theorem WInv.tail {code : Array Inst} {seen : Array Bool} {pc : Nat}
    {rest : List Nat} (h : WInv code seen (pc :: rest)) :
    WInv code seen rest :=
  ⟨h.size, fun x hx => h.mem x (List.mem_cons_of_mem _ hx),
    (List.nodup_cons.mp h.nodup).2⟩

/-- What a mark added to the visited set is on the worklist. -/
theorem markSeen_new_mem {code : Array Inst} {seen : Array Bool}
    {pending : List Nat} {pc : Nat} {x : Nat}
    (hx : (markSeen code seen pending pc).1[x]! = true) :
    seen[x]! = true ∨ x ∈ (markSeen code seen pending pc).2 := by
  by_cases hge : pc ≥ code.size
  · left
    unfold markSeen at hx
    rwa [if_pos hge] at hx
  by_cases hseen : seen[pc]! = true
  · left
    unfold markSeen at hx
    rwa [if_neg hge, if_pos hseen] at hx
  by_cases hxpc : x = pc
  · subst hxpc
    exact .inr (markSeen_mem_self (by omega) hseen)
  · left
    unfold markSeen at hx
    rw [if_neg hge, if_neg hseen] at hx
    have hx' : (seen.set! pc true)[x]! = true := hx
    rwa [getBang_set!_ne seen true hxpc] at hx'

/-- Popping a pc with one successor and marking it keeps both worklist
invariants. -/
theorem invariants_one {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {seen : Array Bool} {pc : Nat} {rest : List Nat}
    {q1 : Nat}
    (hinv : WInv code seen (pc :: rest))
    (hdone : Done code classes reps seen (pc :: rest))
    (hpop : crHead code classes pc = false)
    (hsucc : ∀ q ∈ succs code reps pc, q = q1) :
    WInv code (markSeen code seen rest q1).1 (markSeen code seen rest q1).2 ∧
      Done code classes reps (markSeen code seen rest q1).1
        (markSeen code seen rest q1).2 := by
  refine ⟨hinv.tail.mark q1, ?_⟩
  refine done_expand hdone hpop ?_ (fun x hx => markSeen_grows x hx)
    (fun x hx => markSeen_new_mem hx) (fun x hx => markSeen_mem_mono hx)
  intro q hq hlt
  obtain rfl := hsucc q hq
  exact markSeen_marked hinv.size hlt

/-- The same for two successors marked in order. -/
theorem invariants_two {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {seen : Array Bool} {pc : Nat} {rest : List Nat}
    {q1 q2 : Nat}
    (hinv : WInv code seen (pc :: rest))
    (hdone : Done code classes reps seen (pc :: rest))
    (hpop : crHead code classes pc = false)
    (hsucc : ∀ q ∈ succs code reps pc, q = q1 ∨ q = q2) :
    WInv code
      (markSeen code (markSeen code seen rest q1).1
        (markSeen code seen rest q1).2 q2).1
      (markSeen code (markSeen code seen rest q1).1
        (markSeen code seen rest q1).2 q2).2 ∧
    Done code classes reps
      (markSeen code (markSeen code seen rest q1).1
        (markSeen code seen rest q1).2 q2).1
      (markSeen code (markSeen code seen rest q1).1
        (markSeen code seen rest q1).2 q2).2 := by
  have hM1 := hinv.tail.mark q1
  refine ⟨hM1.mark q2, ?_⟩
  refine done_expand hdone hpop ?_
    (fun x hx => markSeen_grows x (markSeen_grows x hx)) (fun x hx => ?_)
    (fun x hx => markSeen_mem_mono (markSeen_mem_mono hx))
  · intro q hq hlt
    rcases hsucc q hq with rfl | rfl
    · exact markSeen_grows _ (markSeen_marked hinv.size hlt)
    · exact markSeen_marked hM1.size hlt
  · rcases markSeen_new_mem hx with hx' | hx'
    · rcases markSeen_new_mem hx' with h'' | h''
      · exact .inl h''
      · exact .inr (markSeen_mem_mono h'')
    · exact .inr hx'

/-- The completeness direction: a `false` answer means nothing reachable
from any marked pc is a witness. -/
theorem go_false {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} :
    ∀ (fuel : Nat) (seen : Array Bool) (pending : List Nat),
      WInv code seen pending →
      Done code classes reps seen pending →
      scanFirst.go code classes reps fuel (seen, pending) = false →
      ∀ p q : Nat, seen[p]! = true → p < code.size →
        Reach code reps p q → crHead code classes q = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen pending hinv hdone hgo p q hp hplt hreach
      cases pending with
      | nil => exact done_no_witness hdone hp hplt hreach
      | cons pc rest => simp [scanFirst.go] at hgo
  | succ fuel ih =>
      intro seen pending hinv hdone hgo p q hp hplt hreach
      cases pending with
      | nil => exact done_no_witness hdone hp hplt hreach
      | cons pc rest =>
          cases hop : (code[pc]!).op
          case chr =>
            simp only [scanFirst.go, hop, Bool.or_eq_false_iff] at hgo
            obtain ⟨harg, hgo⟩ := hgo
            have hdone' : Done code classes reps seen rest :=
              done_expand hdone (by simp [crHead, hop, harg])
                (by simp [succs, hop]) (fun x hx => hx) (fun x hx => .inl hx)
                (fun x hx => hx)
            exact ih seen rest hinv.tail hdone' hgo p q hp hplt hreach
          case chrCI =>
            simp only [scanFirst.go, hop, Bool.or_eq_false_iff] at hgo
            obtain ⟨harg, hgo⟩ := hgo
            have hdone' : Done code classes reps seen rest :=
              done_expand hdone (by simp [crHead, hop, harg])
                (by simp [succs, hop]) (fun x hx => hx) (fun x hx => .inl hx)
                (fun x hx => hx)
            exact ih seen rest hinv.tail hdone' hgo p q hp hplt hreach
          case cls =>
            simp only [scanFirst.go, hop, Bool.or_eq_false_iff] at hgo
            obtain ⟨harg, hgo⟩ := hgo
            have hdone' : Done code classes reps seen rest :=
              done_expand hdone (by simp only [crHead, hop]; exact harg)
                (by simp [succs, hop]) (fun x hx => hx) (fun x hx => .inl hx)
                (fun x hx => hx)
            exact ih seen rest hinv.tail hdone' hgo p q hp hplt hreach
          case any =>
            simp [scanFirst.go, hop] at hgo
          case anyNoNL =>
            simp [scanFirst.go, hop] at hgo
          case bsr =>
            simp [scanFirst.go, hop] at hgo
          case accept =>
            simp [scanFirst.go, hop] at hgo
          case split =>
            simp only [scanFirst.go, hop] at hgo
            obtain ⟨hinv', hdone'⟩ :=
              invariants_two (q1 := (code[pc]!).arg) (q2 := (code[pc]!).alt)
                hinv hdone (by simp [crHead, hop])
                (by intro s hs; simpa [succs, hop] using hs)
            exact ih _ _ hinv' hdone' hgo p q (markSeen_grows p (markSeen_grows p hp)) hplt hreach
          case jump =>
            simp only [scanFirst.go, hop] at hgo
            obtain ⟨hinv', hdone'⟩ :=
              invariants_one (q1 := (code[pc]!).arg) hinv hdone
                (by simp [crHead, hop])
                (by intro s hs; simpa [succs, hop] using hs)
            exact ih _ _ hinv' hdone' hgo p q (markSeen_grows p hp) hplt hreach
          case repLoop =>
            simp only [scanFirst.go, hop] at hgo
            by_cases hlo : (reps[(code[pc]!).arg]!).lo == 0
            · rw [if_pos hlo] at hgo
              obtain ⟨hinv', hdone'⟩ :=
                invariants_two (q1 := (reps[(code[pc]!).arg]!).body)
                  (q2 := (reps[(code[pc]!).arg]!).after) hinv hdone
                  (by simp [crHead, hop])
                  (by intro s hs; simpa [succs, hop, hlo] using hs)
              exact ih _ _ hinv' hdone' hgo p q (markSeen_grows p (markSeen_grows p hp)) hplt hreach
            · rw [if_neg hlo] at hgo
              obtain ⟨hinv', hdone'⟩ :=
                invariants_one (q1 := (reps[(code[pc]!).arg]!).body) hinv hdone
                  (by simp [crHead, hop])
                  (by intro s hs; simpa [succs, hop, hlo] using hs)
              exact ih _ _ hinv' hdone' hgo p q (markSeen_grows p hp) hplt hreach
          case repNext =>
            simp only [scanFirst.go, hop] at hgo
            obtain ⟨hinv', hdone'⟩ :=
              invariants_two (q1 := (reps[(code[pc]!).arg]!).head)
                (q2 := (reps[(code[pc]!).arg]!).after) hinv hdone
                (by simp [crHead, hop])
                (by intro s hs; simpa [succs, hop] using hs)
            exact ih _ _ hinv' hdone' hgo p q (markSeen_grows p (markSeen_grows p hp)) hplt hreach
          all_goals
            simp only [scanFirst.go, hop] at hgo
          all_goals
            obtain ⟨hinv', hdone'⟩ :=
              invariants_one (q1 := pc + 1) hinv hdone
                (by simp [crHead, hop])
                (by intro s hs; simpa [succs, hop] using hs)
            exact ih _ _ hinv' hdone' hgo p q (markSeen_grows p hp) hplt hreach

/-- The soundness direction: under PikeTermination's variant, a `true`
answer names an ε-reachable witness — the fuel-zero fallback is out of
reach on the fuel `scanFirst` passes. The state stays one pair so the
recursive application never has to eta-expand a `markSeen` result. -/
theorem go_true {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} :
    ∀ (fuel : Nat) (mp : Array Bool × List Nat),
      mp.1.size = code.size →
      (∀ pc ∈ mp.2, pc < code.size ∧ Reach code reps 0 pc) →
      mp.2.length + 2 * unmarked mp.1 ≤ fuel →
      scanFirst.go code classes reps fuel mp = true →
      ∃ pc, pc < code.size ∧ Reach code reps 0 pc ∧
        crHead code classes pc = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro mp hsz hmem hvar hgo
      obtain ⟨seen, pending⟩ := mp
      cases pending with
      | nil => simp [scanFirst.go] at hgo
      | cons pc rest =>
          rw [List.length_cons] at hvar
          omega
  | succ fuel ih =>
      intro mp hsz hmem hvar hgo
      obtain ⟨seen, pending⟩ := mp
      cases pending with
      | nil => simp [scanFirst.go] at hgo
      | cons pc rest =>
          simp only at hsz hmem hvar
          rw [List.length_cons] at hvar
          have hpc := hmem pc (List.mem_cons_self ..)
          have hmem' := fun x hx => hmem x (List.mem_cons_of_mem _ hx)
          cases hop : (code[pc]!).op
          case chr =>
            simp only [scanFirst.go, hop, Bool.or_eq_true] at hgo
            rcases hgo with harg | hgo
            · exact ⟨pc, hpc.1, hpc.2, by simp [crHead, hop, harg]⟩
            · exact ih (seen, rest) hsz hmem' (by simp only; omega) hgo
          case chrCI =>
            simp only [scanFirst.go, hop, Bool.or_eq_true] at hgo
            rcases hgo with harg | hgo
            · exact ⟨pc, hpc.1, hpc.2, by simp [crHead, hop, harg]⟩
            · exact ih (seen, rest) hsz hmem' (by simp only; omega) hgo
          case cls =>
            simp only [scanFirst.go, hop, Bool.or_eq_true] at hgo
            rcases hgo with harg | hgo
            · exact ⟨pc, hpc.1, hpc.2, by simp only [crHead, hop]; exact harg⟩
            · exact ih (seen, rest) hsz hmem' (by simp only; omega) hgo
          case any =>
            exact ⟨pc, hpc.1, hpc.2, by simp [crHead, hop]⟩
          case anyNoNL =>
            exact ⟨pc, hpc.1, hpc.2, by simp [crHead, hop]⟩
          case bsr =>
            exact ⟨pc, hpc.1, hpc.2, by simp [crHead, hop]⟩
          case accept =>
            exact ⟨pc, hpc.1, hpc.2, by simp [crHead, hop]⟩
          case split =>
            simp only [scanFirst.go, hop] at hgo
            obtain ⟨hs1, hv1⟩ := markSeen_spec code seen rest (code[pc]!).arg hsz
            obtain ⟨hs2, hv2⟩ := markSeen_spec code
              (markSeen code seen rest (code[pc]!).arg).1
              (markSeen code seen rest (code[pc]!).arg).2 (code[pc]!).alt hs1
            refine ih (markSeen code (markSeen code seen rest (code[pc]!).arg).1
              (markSeen code seen rest (code[pc]!).arg).2 (code[pc]!).alt)
              hs2 ?_ (by omega) hgo
            intro x hx
            rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
            · rcases markSeen_mem_of hx' with hx'' | ⟨rfl, hlt, _⟩
              · exact hmem' x hx''
              · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt, by simp [succs, hop]⟩⟩
            · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt, by simp [succs, hop]⟩⟩
          case jump =>
            simp only [scanFirst.go, hop] at hgo
            obtain ⟨hs1, hv1⟩ := markSeen_spec code seen rest (code[pc]!).arg hsz
            refine ih (markSeen code seen rest (code[pc]!).arg) hs1 ?_
              (by omega) hgo
            intro x hx
            rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
            · exact hmem' x hx'
            · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt, by simp [succs, hop]⟩⟩
          case repLoop =>
            simp only [scanFirst.go, hop] at hgo
            by_cases hlo : (reps[(code[pc]!).arg]!).lo == 0
            · rw [if_pos hlo] at hgo
              obtain ⟨hs1, hv1⟩ :=
                markSeen_spec code seen rest (reps[(code[pc]!).arg]!).body hsz
              obtain ⟨hs2, hv2⟩ := markSeen_spec code
                (markSeen code seen rest (reps[(code[pc]!).arg]!).body).1
                (markSeen code seen rest (reps[(code[pc]!).arg]!).body).2
                (reps[(code[pc]!).arg]!).after hs1
              refine ih (markSeen code
                (markSeen code seen rest (reps[(code[pc]!).arg]!).body).1
                (markSeen code seen rest (reps[(code[pc]!).arg]!).body).2
                (reps[(code[pc]!).arg]!).after) hs2 ?_ (by omega) hgo
              intro x hx
              rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
              · rcases markSeen_mem_of hx' with hx'' | ⟨rfl, hlt, _⟩
                · exact hmem' x hx''
                · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt,
                    by simp [succs, hop, hlo]⟩⟩
              · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt,
                  by simp [succs, hop, hlo]⟩⟩
            · rw [if_neg hlo] at hgo
              obtain ⟨hs1, hv1⟩ :=
                markSeen_spec code seen rest (reps[(code[pc]!).arg]!).body hsz
              refine ih (markSeen code seen rest (reps[(code[pc]!).arg]!).body)
                hs1 ?_ (by omega) hgo
              intro x hx
              rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
              · exact hmem' x hx'
              · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt,
                  by simp [succs, hop, hlo]⟩⟩
          case repNext =>
            simp only [scanFirst.go, hop] at hgo
            obtain ⟨hs1, hv1⟩ :=
              markSeen_spec code seen rest (reps[(code[pc]!).arg]!).head hsz
            obtain ⟨hs2, hv2⟩ := markSeen_spec code
              (markSeen code seen rest (reps[(code[pc]!).arg]!).head).1
              (markSeen code seen rest (reps[(code[pc]!).arg]!).head).2
              (reps[(code[pc]!).arg]!).after hs1
            refine ih (markSeen code
              (markSeen code seen rest (reps[(code[pc]!).arg]!).head).1
              (markSeen code seen rest (reps[(code[pc]!).arg]!).head).2
              (reps[(code[pc]!).arg]!).after) hs2 ?_ (by omega) hgo
            intro x hx
            rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
            · rcases markSeen_mem_of hx' with hx'' | ⟨rfl, hlt, _⟩
              · exact hmem' x hx''
              · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt, by simp [succs, hop]⟩⟩
            · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt, by simp [succs, hop]⟩⟩
          all_goals
            simp only [scanFirst.go, hop] at hgo
          all_goals
            obtain ⟨hs1, hv1⟩ := markSeen_spec code seen rest (pc + 1) hsz
            refine ih (markSeen code seen rest (pc + 1)) hs1 ?_ (by omega) hgo
            intro x hx
            rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
            · exact hmem' x hx'
            · exact ⟨hlt, hpc.2.tail ⟨hpc.1, hlt, by simp [succs, hop]⟩⟩

/-- `scanFirst` answers exactly: some ε-reachable pc is a CR head. -/
theorem scanFirst_iff (code : Array Inst) (classes : Array UInt8)
    (reps : Array RepInfo) :
    scanFirst code classes reps = true ↔
      ∃ pc, pc < code.size ∧ Reach code reps 0 pc ∧
        crHead code classes pc = true := by
  have hsz0 : (Array.replicate code.size false).size = code.size := by simp
  constructor
  · intro h
    unfold scanFirst at h
    obtain ⟨hs0, hv0⟩ :=
      markSeen_spec code (Array.replicate code.size false) [] 0 hsz0
    refine go_true _ (markSeen code (Array.replicate code.size false) [] 0)
      hs0 ?_ ?_ h
    · intro x hx
      rcases markSeen_mem_of hx with hx' | ⟨rfl, hlt, _⟩
      · cases hx'
      · exact ⟨hlt, .refl 0⟩
    · have hle := unmarked_le_size (Array.replicate code.size false)
      rw [hsz0] at hle
      simp only [List.length_nil] at hv0
      omega
  · rintro ⟨pc, hlt, hreach, hcr⟩
    cases hgo : scanFirst code classes reps
    · exfalso
      unfold scanFirst at hgo
      have h0lt : (0 : Nat) < code.size := by
        by_cases h0 : (0 : Nat) = pc
        · omega
        · exact hreach.src_lt h0
      have hrep0 : (Array.replicate code.size false)[0]! = false := by
        rw [getElem!_pos (Array.replicate code.size false) 0 (by omega)]
        simp
      have hinv0 : WInv code
          (markSeen code (Array.replicate code.size false) [] 0).1
          (markSeen code (Array.replicate code.size false) [] 0).2 :=
        WInv.mark ⟨hsz0, fun x hx => absurd hx (List.not_mem_nil),
          List.nodup_nil⟩ 0
      have hdone0 : Done code classes reps
          (markSeen code (Array.replicate code.size false) [] 0).1
          (markSeen code (Array.replicate code.size false) [] 0).2 := by
        intro p hp hpseen hpnot
        exfalso
        rcases markSeen_seen_of hpseen with h' | rfl
        · rw [getElem!_pos (Array.replicate code.size false) p (by omega)]
            at h'
          simp at h'
        · exact hpnot (markSeen_mem_self h0lt (by rw [hrep0]; simp))
      have := go_false _ _ _ hinv0 hdone0 hgo 0 pc
        (markSeen_marked hsz0 h0lt) h0lt hreach
      rw [this] at hcr
      exact Bool.noConfusion hcr
    · rfl

/-! ## Reading `crWalk` one constructor at a time

`crWalk` folds its list children through `attach`; the lemmas here trade
that for plain folds and peel one child off, which is the shape the
fragment inductions below consume. -/

theorem crWalk_alt (arms : List Ast) :
    crWalk (.alt arms) =
      arms.foldl
        (fun acc a => (acc.1 || (crWalk a).1, acc.2 || (crWalk a).2))
        (false, false) := by
  simp only [crWalk]
  rw [← List.foldl_attach
    (f := fun acc a => (acc.1 || (crWalk a).1, acc.2 || (crWalk a).2))
    (l := arms) (b := ((false, false) : Bool × Bool))]

theorem crWalk_cat (kids : List Ast) :
    crWalk (.cat kids) =
      kids.foldl
        (fun acc k =>
          (acc.1 || (acc.2 && (crWalk k).1), acc.2 && (crWalk k).2))
        (false, true) := by
  simp only [crWalk]
  rw [← List.foldl_attach
    (f := fun acc k =>
      (acc.1 || (acc.2 && (crWalk k).1), acc.2 && (crWalk k).2))
    (l := kids) (b := ((false, true) : Bool × Bool))]

private theorem altFold_acc (arms : List Ast) :
    ∀ acc : Bool × Bool,
      arms.foldl
        (fun acc a => (acc.1 || (crWalk a).1, acc.2 || (crWalk a).2)) acc =
      (acc.1 ||
        (arms.foldl
          (fun acc a => (acc.1 || (crWalk a).1, acc.2 || (crWalk a).2))
          (false, false)).1,
       acc.2 ||
        (arms.foldl
          (fun acc a => (acc.1 || (crWalk a).1, acc.2 || (crWalk a).2))
          (false, false)).2) := by
  induction arms with
  | nil => intro acc; simp
  | cons a arms ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, ih ((false, false).1 || _, _)]
      obtain ⟨c, t⟩ := acc
      simp [Bool.or_assoc]

private theorem catFold_acc (kids : List Ast) :
    ∀ acc : Bool × Bool,
      kids.foldl
        (fun acc k =>
          (acc.1 || (acc.2 && (crWalk k).1), acc.2 && (crWalk k).2)) acc =
      (acc.1 ||
        (acc.2 &&
          (kids.foldl
            (fun acc k =>
              (acc.1 || (acc.2 && (crWalk k).1), acc.2 && (crWalk k).2))
            (false, true)).1),
       acc.2 &&
        (kids.foldl
          (fun acc k =>
            (acc.1 || (acc.2 && (crWalk k).1), acc.2 && (crWalk k).2))
          (false, true)).2) := by
  induction kids with
  | nil => intro acc; simp
  | cons k kids ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, ih ((false, true).1 || _, _)]
      obtain ⟨c, t⟩ := acc
      cases c <;> cases t <;>
        simp [Bool.and_or_distrib_left]

theorem crWalk_alt_nil : crWalk (.alt []) = (false, false) := by
  rw [crWalk_alt]
  rfl

theorem crWalk_cat_nil : crWalk (.cat []) = (false, true) := by
  rw [crWalk_cat]
  rfl

theorem crWalk_alt_cons₁ (a : Ast) (arms : List Ast) :
    (crWalk (.alt (a :: arms))).1 =
      ((crWalk a).1 || (crWalk (.alt arms)).1) := by
  rw [crWalk_alt, crWalk_alt, List.foldl_cons, altFold_acc]
  simp

theorem crWalk_alt_cons₂ (a : Ast) (arms : List Ast) :
    (crWalk (.alt (a :: arms))).2 =
      ((crWalk a).2 || (crWalk (.alt arms)).2) := by
  rw [crWalk_alt, crWalk_alt, List.foldl_cons, altFold_acc]
  simp

theorem crWalk_alt_one (a : Ast) : crWalk (.alt [a]) = crWalk a := by
  have h1 := crWalk_alt_cons₁ a []
  have h2 := crWalk_alt_cons₂ a []
  rw [crWalk_alt_nil] at h1 h2
  simp only [Bool.or_false] at h1 h2
  exact Prod.ext h1 h2

theorem crWalk_cat_cons₁ (k : Ast) (kids : List Ast) :
    (crWalk (.cat (k :: kids))).1 =
      ((crWalk k).1 || ((crWalk k).2 && (crWalk (.cat kids)).1)) := by
  rw [crWalk_cat, crWalk_cat, List.foldl_cons, catFold_acc]
  simp

theorem crWalk_cat_cons₂ (k : Ast) (kids : List Ast) :
    (crWalk (.cat (k :: kids))).2 =
      ((crWalk k).2 && (crWalk (.cat kids)).2) := by
  rw [crWalk_cat, crWalk_cat, List.foldl_cons, catFold_acc]
  simp

theorem crWalk_grp (cap : Nat) (body : Ast) :
    crWalk (.grp cap body) = crWalk body := by
  simp [crWalk]

theorem crWalk_rep_zero (rlo : Nat) (greedy : Bool) (body : Ast) :
    crWalk (.rep rlo (some 0) greedy body) = (false, true) := by
  simp [crWalk]

theorem crWalk_rep_one (greedy : Bool) (body : Ast) :
    crWalk (.rep 1 (some 1) greedy body) = crWalk body := by
  simp [crWalk]

theorem crWalk_rep_opt {rlo : Nat} (hne : (rlo == 1) = false)
    (greedy : Bool) (body : Ast) :
    crWalk (.rep rlo (some 1) greedy body) = ((crWalk body).1, true) := by
  rcases hw : crWalk body with ⟨cr, tr⟩
  simp [crWalk, hne, hw]

theorem crWalk_rep_many {rhi : Option Nat} (h0 : rhi ≠ some 0)
    (h1 : rhi ≠ some 1) (rlo : Nat) (greedy : Bool) (body : Ast) :
    crWalk (.rep rlo rhi greedy body) =
      ((crWalk body).1, rlo == 0 || (crWalk body).2) := by
  rcases hw : crWalk body with ⟨cr, tr⟩
  match rhi, h0, h1 with
  | none, _, _ => simp [crWalk, hw]
  | some (n + 2), _, _ => simp [crWalk, hw]
  | some 0, h0, _ => exact absurd rfl h0
  | some 1, _, h1 => exact absurd rfl h1

/-! ## The fragment relation

`Frag code classes reps r0 a lo hi` pins what `compileNode` laid down for
`a` on `[lo, hi)`: cells where the walk needs them, the class byte the
CR test reads, and the repetition record the two rep opcodes consult.
The shape mirrors RefineProto's `FragAt`, extended to the whole wave 1
AST; constructs that compile to nothing are all carried by `empty`,
which only remembers that `crWalk` calls them transparent. -/

/-- The opcodes the scan steps over: one mark at `pc + 1`, never a
witness — the assertions, `save`, `repZero`, `repEnter`. -/
def plainOp : Op → Bool
  | .save | .circ | .circM | .doll | .dollE | .dollM | .sod | .eod
  | .eodn | .wordB | .notWordB | .repZero | .repEnter => true
  | _ => false

theorem succs_plain {code : Array Inst} {reps : Array RepInfo} {pc : Nat}
    (h : plainOp (code[pc]!).op = true) :
    succs code reps pc = [pc + 1] := by
  cases hop : (code[pc]!).op <;>
    first
      | (simp only [succs, hop]; done)
      | (simp [plainOp, hop] at h)

theorem crHead_plain {code : Array Inst} {classes : Array UInt8} {pc : Nat}
    (h : plainOp (code[pc]!).op = true) :
    crHead code classes pc = false := by
  cases hop : (code[pc]!).op <;>
    first
      | (simp only [crHead, hop]; done)
      | (simp [plainOp, hop] at h)

inductive Frag (code : Array Inst) (classes : Array UInt8)
    (reps : Array RepInfo) (r0 : Nat) : Ast → Nat → Nat → Prop where
  | empty {a : Ast} {lo : Nat} (hw : crWalk a = (false, true)) :
      Frag code classes reps r0 a lo lo
  | chr {b : UInt8} {lo : Nat} (hcell : code[lo]! = ⟨.chr, b.toNat, 0⟩) :
      Frag code classes reps r0 (.chr b) lo (lo + 1)
  | chrCI {b : UInt8} {lo : Nat} (hcell : code[lo]! = ⟨.chrCI, b.toNat, 0⟩) :
      Frag code classes reps r0 (.chrCI b) lo (lo + 1)
  | cls {bits : ClassBits} {lo idx : Nat}
      (hcell : code[lo]! = ⟨.cls, idx, 0⟩)
      (hin : idx * 32 + 1 < classes.size)
      (hbyte : classes[idx * 32 + 1]! = bits.toArray[1]!) :
      Frag code classes reps r0 (.cls bits) lo (lo + 1)
  | wild {a : Ast} {lo : Nat}
      (hw : crWalk a = (true, false))
      (hcell : (code[lo]!).op = .any ∨ (code[lo]!).op = .anyNoNL ∨
        (code[lo]!).op = .bsr) :
      Frag code classes reps r0 a lo (lo + 1)
  | asrt {a : Ast} {lo : Nat} (hw : crWalk a = (false, true))
      (hcell : plainOp (code[lo]!).op = true) :
      Frag code classes reps r0 a lo (lo + 1)
  | catCons {k : Ast} {kids : List Ast} {lo mid hi : Nat}
      (h₁ : Frag code classes reps r0 k lo mid)
      (h₂ : Frag code classes reps r0 (.cat kids) mid hi) :
      Frag code classes reps r0 (.cat (k :: kids)) lo hi
  | altOne {a : Ast} {lo hi : Nat} (h : Frag code classes reps r0 a lo hi) :
      Frag code classes reps r0 (.alt [a]) lo hi
  | altCons {a b : Ast} {rest : List Ast} {lo j hi : Nat}
      (hsplit : code[lo]! = ⟨.split, lo + 1, j + 1⟩)
      (h₁ : Frag code classes reps r0 a (lo + 1) j)
      (hjump : code[j]! = ⟨.jump, hi, 0⟩)
      (h₂ : Frag code classes reps r0 (.alt (b :: rest)) (j + 1) hi) :
      Frag code classes reps r0 (.alt (a :: b :: rest)) lo hi
  | grpBody {cap : Nat} {body : Ast} {lo hi : Nat}
      (h : Frag code classes reps r0 body lo hi) :
      Frag code classes reps r0 (.grp cap body) lo hi
  | grpSaves {cap : Nat} {body : Ast} {lo m : Nat}
      (hopen : plainOp (code[lo]!).op = true)
      (h : Frag code classes reps r0 body (lo + 1) m)
      (hclose : plainOp (code[m]!).op = true) :
      Frag code classes reps r0 (.grp cap body) lo (m + 1)
  | repOne {greedy : Bool} {body : Ast} {lo hi : Nat}
      (h : Frag code classes reps r0 body lo hi) :
      Frag code classes reps r0 (.rep 1 (some 1) greedy body) lo hi
  | repOpt {rlo : Nat} {greedy : Bool} {body : Ast} {lo hi : Nat}
      (hne : (rlo == 1) = false)
      (hop : (code[lo]!).op = .split)
      (harm : (code[lo]!).arg = lo + 1 ∧ (code[lo]!).alt = hi ∨
        (code[lo]!).arg = hi ∧ (code[lo]!).alt = lo + 1)
      (h : Frag code classes reps r0 body (lo + 1) hi) :
      Frag code classes reps r0 (.rep rlo (some 1) greedy body) lo hi
  | repMany {rlo : Nat} {rhi : Option Nat} {greedy : Bool} {body : Ast}
      {r rhi32 lo m : Nat}
      (h0 : rhi ≠ some 0) (h1 : rhi ≠ some 1)
      (hz : plainOp (code[lo]!).op = true)
      (hloop : code[lo + 1]! = ⟨.repLoop, r, 0⟩)
      (henter : plainOp (code[lo + 2]!).op = true)
      (hb : Frag code classes reps r0 body (lo + 3) m)
      (hnext : code[m]! = ⟨.repNext, r, 0⟩)
      (hr0 : r0 ≤ r)
      (hr : r < reps.size)
      (hrep : reps[r]! = ⟨rlo, rhi32, greedy, lo + 1, lo + 2, m + 1⟩) :
      Frag code classes reps r0 (.rep rlo rhi greedy body) lo (m + 1)

theorem Frag.le {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : Frag code classes reps r0 a lo hi) : lo ≤ hi := by
  induction h <;> omega

/-- A fragment that spans no cells is transparent: every zero-width
compilation comes from a construct `crWalk` lets the walk through. -/
theorem Frag.zero_trans {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : Frag code classes reps r0 a lo hi) (heq : lo = hi) :
    (crWalk a).2 = true := by
  induction h with
  | empty hw => rw [hw]
  | chr hcell => omega
  | chrCI hcell => omega
  | cls hcell hin hbyte => omega
  | wild hw hcell => omega
  | asrt hw hcell => omega
  | catCons h₁ h₂ ih₁ ih₂ =>
      have l₁ := h₁.le
      have l₂ := h₂.le
      rw [crWalk_cat_cons₂, ih₁ (by omega), ih₂ (by omega)]
      rfl
  | altOne h ih =>
      rw [crWalk_alt_one]
      exact ih heq
  | altCons hsplit h₁ hjump h₂ ih₁ ih₂ =>
      have l₁ := h₁.le
      have l₂ := h₂.le
      omega
  | grpBody h ih =>
      rw [crWalk_grp]
      exact ih heq
  | grpSaves hopen h hclose ih =>
      have := h.le
      omega
  | repOne h ih =>
      rw [crWalk_rep_one]
      exact ih heq
  | repOpt hne hop harm h ih =>
      have := h.le
      omega
  | repMany h0 h1 hz hloop henter hb hnext hr0 hr hrep ih =>
      have := hb.le
      omega

/-- A fragment only pins cells inside its own range and table entries
below the sizes it saw, so it survives any later appends and patches
that leave those alone. -/
theorem Frag.mono {code code' : Array Inst} {classes classes' : Array UInt8}
    {reps reps' : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : Frag code classes reps r0 a lo hi)
    (hcode : ∀ pc, lo ≤ pc → pc < hi → code'[pc]! = code[pc]!)
    (hclsle : classes.size ≤ classes'.size)
    (hcls : ∀ i, i < classes.size → classes'[i]! = classes[i]!)
    (hrepsle : reps.size ≤ reps'.size)
    (hreps : ∀ i, r0 ≤ i → i < reps.size → reps'[i]! = reps[i]!) :
    Frag code' classes' reps' r0 a lo hi := by
  induction h with
  | empty hw => exact .empty hw
  | @chr b lo hcell =>
      exact .chr ((hcode lo (by omega) (by omega)).trans hcell)
  | @chrCI b lo hcell =>
      exact .chrCI ((hcode lo (by omega) (by omega)).trans hcell)
  | @cls bits lo idx hcell hin hbyte =>
      exact .cls ((hcode lo (by omega) (by omega)).trans hcell) (by omega)
        ((hcls _ hin).trans hbyte)
  | wild hw hcell =>
      refine .wild hw ?_
      rw [hcode _ (by omega) (by omega)]
      exact hcell
  | asrt hw hcell =>
      refine .asrt hw ?_
      rw [hcode _ (by omega) (by omega)]
      exact hcell
  | catCons h₁ h₂ ih₁ ih₂ =>
      have l₁ := h₁.le
      have l₂ := h₂.le
      exact .catCons (ih₁ fun pc hp1 hp2 => hcode pc hp1 (by omega))
        (ih₂ fun pc hp1 hp2 => hcode pc (by omega) hp2)
  | altOne h ih => exact .altOne (ih hcode)
  | @altCons a b rest lo j hi hsplit h₁ hjump h₂ ih₁ ih₂ =>
      have l₁ := h₁.le
      have l₂ := h₂.le
      exact .altCons ((hcode lo (by omega) (by omega)).trans hsplit)
        (ih₁ fun pc hp1 hp2 => hcode pc (by omega) (by omega))
        ((hcode j (by omega) (by omega)).trans hjump)
        (ih₂ fun pc hp1 hp2 => hcode pc (by omega) hp2)
  | grpBody h ih => exact .grpBody (ih hcode)
  | @grpSaves cap body lo m hopen h hclose ih =>
      have := h.le
      refine .grpSaves ?_ (ih fun pc hp1 hp2 => hcode pc (by omega) (by omega))
        ?_
      · rw [hcode _ (by omega) (by omega)]
        exact hopen
      · rw [hcode _ (by omega) (by omega)]
        exact hclose
  | repOne h ih => exact .repOne (ih hcode)
  | @repOpt rlo greedy body lo hi hne hop harm h ih =>
      have := h.le
      refine .repOpt hne ?_ ?_
        (ih fun pc hp1 hp2 => hcode pc (by omega) hp2)
      · rw [hcode _ (by omega) (by omega)]
        exact hop
      · rw [hcode _ (by omega) (by omega)]
        exact harm
  | @repMany rlo rhi greedy body r rhi32 lo m h0 h1 hz hloop henter hb hnext
      hr0 hr hrep ih =>
      have := hb.le
      refine .repMany h0 h1 ?_
        ((hcode _ (by omega) (by omega)).trans hloop) ?_
        (ih fun pc hp1 hp2 => hcode pc (by omega) (by omega))
        ((hcode m (by omega) (by omega)).trans hnext)
        hr0 (by omega) ((hreps r hr0 hr).trans hrep)
      · rw [hcode _ (by omega) (by omega)]
        exact hz
      · rw [hcode _ (by omega) (by omega)]
        exact henter

/-! ## Reading `crWalk` off a fragment

Two inductions over a `Frag` derivation. `Frag.closed` builds the
fragment's claimed ε-closure: a set that contains the entry, stays
inside `[lo, hi]`, is closed under `succs` away from the exit, admits a
CR head only when `crWalk` says the first byte can be CR, and holds the
exit exactly when `crWalk` calls the construct transparent. `Frag.reach`
is the converse: the walks `crWalk` promises really exist. -/

/-- The `crHead` test of a compiled `chr`/`chrCI` cell is the AST's. -/
private theorem toNat_beq_cr (b : UInt8) :
    (b.toNat == 0x0D) = (b == 0x0D) := by
  by_cases h : b = 0x0D
  · subst h
    decide
  · have h' : b.toNat ≠ 0x0D := fun hc => h (by
      apply UInt8.toNat_inj.mp
      rw [hc]
      rfl)
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

/-- The `crHead` bit test on a class blob is the spec's membership test
for CR: byte one, mask 0x20. -/
private theorem classBits_cr (bits : ClassBits) :
    (bits.toArray[1]! &&& 0x20 != 0) = bits.has 0x0D := by
  have h3 : bits.toArray[1]! = bits[1]! := by
    rw [getElem!_pos bits.toArray 1 (by simp),
      getElem!_pos bits 1 (by omega)]
    exact Vector.getElem_toArray _
  rw [ClassBits.has, h3]
  rfl

/-- What `Frag.closed` builds, named so the induction can pass it on. -/
def ClosedFor (code : Array Inst) (classes : Array UInt8)
    (reps : Array RepInfo) (a : Ast) (lo hi : Nat) (S : Nat → Prop) : Prop :=
  S lo ∧
  (∀ pc, S pc → lo ≤ pc ∧ pc ≤ hi) ∧
  (∀ pc, S pc → pc ≠ hi → ∀ q ∈ succs code reps pc, S q) ∧
  (∀ pc, S pc → pc ≠ hi → crHead code classes pc = true →
    (crWalk a).1 = true) ∧
  (S hi ↔ (crWalk a).2 = true)

private theorem closedFor_head {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {a : Ast} {lo : Nat}
    (hsuccs : succs code reps lo = [])
    (hcr : crHead code classes lo = true → (crWalk a).1 = true)
    (htrans : (crWalk a).2 = false) :
    ClosedFor code classes reps a lo (lo + 1) (· = lo) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rintro pc rfl
    omega
  · rintro pc rfl _ q hq
    rw [hsuccs] at hq
    cases hq
  · rintro pc rfl _ hh
    exact hcr hh
  · constructor
    · intro h'
      exact absurd h' (by omega)
    · intro h'
      rw [htrans] at h'
      cases h'

private theorem closedFor_eps {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {a : Ast} {lo : Nat}
    (hsuccs : succs code reps lo = [lo + 1])
    (hcr : crHead code classes lo = false)
    (hw : crWalk a = (false, true)) :
    ClosedFor code classes reps a lo (lo + 1)
      (fun pc => pc = lo ∨ pc = lo + 1) := by
  refine ⟨.inl rfl, ?_, ?_, ?_, ?_⟩
  · rintro pc (rfl | rfl) <;> omega
  · rintro pc (rfl | rfl) hne q hq
    · rw [hsuccs] at hq
      rcases List.mem_singleton.mp hq with rfl
      exact .inr rfl
    · exact absurd rfl hne
  · rintro pc (rfl | rfl) hne hh
    · rw [hcr] at hh
      cases hh
    · exact absurd rfl hne
  · simp [hw]

theorem Frag.closed {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : Frag code classes reps r0 a lo hi) :
    ∃ S : Nat → Prop, ClosedFor code classes reps a lo hi S := by
  induction h with
  | @empty a lo hw =>
      refine ⟨(· = lo), rfl, ?_, ?_, ?_, ?_⟩
      · rintro pc rfl
        omega
      · rintro pc rfl hne
        exact absurd rfl hne
      · rintro pc rfl hne
        exact absurd rfl hne
      · simp [hw]
  | @chr b lo hcell =>
      refine ⟨_, closedFor_head (by simp [succs, hcell]) ?_
        (by simp [crWalk])⟩
      intro hh
      simp only [crHead, hcell] at hh
      have hcw : (crWalk (Ast.chr b)).1 = (b == 0x0D) := by simp [crWalk]
      rw [hcw, ← toNat_beq_cr]
      exact hh
  | @chrCI b lo hcell =>
      refine ⟨_, closedFor_head (by simp [succs, hcell]) ?_
        (by simp [crWalk])⟩
      intro hh
      simp only [crHead, hcell] at hh
      have hcw : (crWalk (Ast.chrCI b)).1 = (b == 0x0D) := by simp [crWalk]
      rw [hcw, ← toNat_beq_cr]
      exact hh
  | @cls bits lo idx hcell hin hbyte =>
      refine ⟨_, closedFor_head (by simp [succs, hcell]) ?_
        (by simp [crWalk])⟩
      intro hh
      simp only [crHead, hcell] at hh
      rw [hbyte, classBits_cr] at hh
      have hcw : (crWalk (Ast.cls bits)).1 = bits.has 0x0D := by simp [crWalk]
      rw [hcw]
      exact hh
  | @wild a lo hw hcell =>
      refine ⟨_, closedFor_head ?_ (fun _ => by rw [hw]) (by rw [hw])⟩
      rcases hcell with h' | h' | h' <;> simp [succs, h']
  | asrt hw hcell =>
      exact ⟨_, closedFor_eps (succs_plain hcell) (crHead_plain hcell) hw⟩
  | @catCons k kids lo mid hi h₁ h₂ ih₁ ih₂ =>
      obtain ⟨S₁, hS₁0, hS₁bd, hS₁cl, hS₁cr, hS₁hi⟩ := ih₁
      obtain ⟨S₂, hS₂0, hS₂bd, hS₂cl, hS₂cr, hS₂hi⟩ := ih₂
      have l₁ := h₁.le
      have l₂ := h₂.le
      refine ⟨fun pc => S₁ pc ∨ ((crWalk k).2 = true ∧ S₂ pc),
        .inl hS₁0, ?_, ?_, ?_, ?_⟩
      · rintro pc (hm | ⟨_, hm⟩)
        · have := hS₁bd pc hm
          omega
        · have := hS₂bd pc hm
          omega
      · rintro pc (hm | ⟨htr, hm⟩) hne q hq
        · by_cases hpm : pc = mid
          · subst hpm
            have htr := hS₁hi.mp hm
            exact .inr ⟨htr, hS₂cl _ hS₂0 hne q hq⟩
          · exact .inl (hS₁cl pc hm hpm q hq)
        · exact .inr ⟨htr, hS₂cl pc hm hne q hq⟩
      · rintro pc (hm | ⟨htr, hm⟩) hne hh
        · rw [crWalk_cat_cons₁]
          by_cases hpm : pc = mid
          · subst hpm
            have htr := hS₁hi.mp hm
            have hc := hS₂cr _ hS₂0 hne hh
            simp [htr, hc]
          · have := hS₁cr pc hm hpm hh
            simp [this]
        · rw [crWalk_cat_cons₁]
          have := hS₂cr pc hm hne hh
          simp [htr, this]
      · rw [crWalk_cat_cons₂]
        constructor
        · rintro (hm | ⟨htr, hm⟩)
          · have hbd := hS₁bd hi hm
            have hmideq : mid = hi := by omega
            subst hmideq
            have htr₁ := hS₁hi.mp hm
            have htr₂ := h₂.zero_trans rfl
            simp [htr₁, htr₂]
          · have := hS₂hi.mp hm
            simp [htr, this]
        · intro hb
          rw [Bool.and_eq_true] at hb
          obtain ⟨htr₁, htr₂⟩ := hb
          exact .inr ⟨htr₁, hS₂hi.mpr htr₂⟩
  | altOne h ih =>
      obtain ⟨S, h0, hbd, hcl, hcr, hhi⟩ := ih
      exact ⟨S, h0, hbd, hcl,
        fun pc hm hne hh => by rw [crWalk_alt_one]; exact hcr pc hm hne hh,
        by rw [crWalk_alt_one]; exact hhi⟩
  | @altCons a b rest lo j hi hsplit h₁ hjump h₂ ih₁ ih₂ =>
      obtain ⟨S₁, hS₁0, hS₁bd, hS₁cl, hS₁cr, hS₁hi⟩ := ih₁
      obtain ⟨S₂, hS₂0, hS₂bd, hS₂cl, hS₂cr, hS₂hi⟩ := ih₂
      have hsu : succs code reps lo = [lo + 1, j + 1] := by
        simp [succs, hsplit]
      have hsj : succs code reps j = [hi] := by
        simp [succs, hjump]
      have l₁ := h₁.le
      have l₂ := h₂.le
      refine ⟨fun pc =>
          pc = lo ∨ S₁ pc ∨ S₂ pc ∨ ((crWalk a).2 = true ∧ pc = hi),
        .inl rfl, ?_, ?_, ?_, ?_⟩
      · rintro pc (rfl | hm | hm | ⟨_, rfl⟩)
        · omega
        · have := hS₁bd pc hm
          omega
        · have := hS₂bd pc hm
          omega
        · omega
      · rintro pc (rfl | hm | hm | ⟨_, rfl⟩) hne q hq
        · rw [hsu] at hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact .inr (.inl hS₁0)
          · exact .inr (.inr (.inl hS₂0))
        · by_cases hpj : pc = j
          · subst hpj
            have htr := hS₁hi.mp hm
            rw [hsj] at hq
            rcases List.mem_singleton.mp hq with rfl
            exact .inr (.inr (.inr ⟨htr, rfl⟩))
          · exact .inr (.inl (hS₁cl pc hm hpj q hq))
        · exact .inr (.inr (.inl (hS₂cl pc hm hne q hq)))
        · exact absurd rfl hne
      · rintro pc (rfl | hm | hm | ⟨_, rfl⟩) hne hh
        · simp [crHead, hsplit] at hh
        · rw [crWalk_alt_cons₁]
          by_cases hpj : pc = j
          · subst hpj
            simp [crHead, hjump] at hh
          · have := hS₁cr pc hm hpj hh
            simp [this]
        · rw [crWalk_alt_cons₁]
          have := hS₂cr pc hm hne hh
          simp [this]
        · exact absurd rfl hne
      · rw [crWalk_alt_cons₂]
        constructor
        · rintro (heq | hm | hm | ⟨htr, _⟩)
          · exact absurd heq (by omega)
          · have := hS₁bd hi hm
            exact absurd this.2 (by omega)
          · have := hS₂hi.mp hm
            simp [this]
          · simp [htr]
        · intro hb
          rw [Bool.or_eq_true] at hb
          rcases hb with h' | h'
          · exact .inr (.inr (.inr ⟨h', rfl⟩))
          · exact .inr (.inr (.inl (hS₂hi.mpr h')))
  | grpBody h ih =>
      obtain ⟨S, h0, hbd, hcl, hcr, hhi⟩ := ih
      exact ⟨S, h0, hbd, hcl,
        fun pc hm hne hh => by rw [crWalk_grp]; exact hcr pc hm hne hh,
        by rw [crWalk_grp]; exact hhi⟩
  | @grpSaves cap body lo m hopen h hclose ih =>
      obtain ⟨S, h0, hbd, hcl, hcr, hhi⟩ := ih
      have hsuo := succs_plain (reps := reps) hopen
      have hsuc := succs_plain (reps := reps) hclose
      have hl := h.le
      refine ⟨fun pc =>
          pc = lo ∨ S pc ∨ ((crWalk body).2 = true ∧ pc = m + 1),
        .inl rfl, ?_, ?_, ?_, ?_⟩
      · rintro pc (rfl | hm | ⟨_, rfl⟩)
        · omega
        · have := hbd pc hm
          omega
        · omega
      · rintro pc (rfl | hm | ⟨_, rfl⟩) hne q hq
        · rw [hsuo] at hq
          rcases List.mem_singleton.mp hq with rfl
          exact .inr (.inl h0)
        · by_cases hpm : pc = m
          · subst hpm
            have htr := hhi.mp hm
            rw [hsuc] at hq
            rcases List.mem_singleton.mp hq with rfl
            exact .inr (.inr ⟨htr, rfl⟩)
          · exact .inr (.inl (hcl pc hm hpm q hq))
        · exact absurd rfl hne
      · rintro pc (rfl | hm | ⟨_, rfl⟩) hne hh
        · rw [crHead_plain hopen] at hh
          cases hh
        · rw [crWalk_grp]
          by_cases hpm : pc = m
          · subst hpm
            rw [crHead_plain hclose] at hh
            cases hh
          · exact hcr pc hm hpm hh
        · exact absurd rfl hne
      · rw [crWalk_grp]
        constructor
        · rintro (heq | hm | ⟨htr, _⟩)
          · exact absurd heq (by omega)
          · have := hbd _ hm
            exact absurd this.2 (by omega)
          · exact htr
        · intro htr
          exact .inr (.inr ⟨htr, rfl⟩)
  | repOne h ih =>
      obtain ⟨S, h0, hbd, hcl, hcr, hhi⟩ := ih
      exact ⟨S, h0, hbd, hcl,
        fun pc hm hne hh => by rw [crWalk_rep_one]; exact hcr pc hm hne hh,
        by rw [crWalk_rep_one]; exact hhi⟩
  | @repOpt rlo greedy body lo hi hne hop harm h ih =>
      obtain ⟨S, h0, hbd, hcl, hcr, hhi⟩ := ih
      have hl := h.le
      have hsu : ∀ q ∈ succs code reps lo, q = lo + 1 ∨ q = hi := by
        intro q hq
        simp only [succs, hop] at hq
        rcases harm with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2] at hq
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using hq
        · rw [e1, e2] at hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          exact hq.symm
      refine ⟨fun pc => pc = lo ∨ S pc ∨ pc = hi, .inl rfl, ?_, ?_, ?_, ?_⟩
      · rintro pc (rfl | hm | rfl)
        · omega
        · have := hbd pc hm
          omega
        · omega
      · rintro pc (rfl | hm | rfl) hne' q hq
        · rcases hsu q hq with rfl | rfl
          · exact .inr (.inl h0)
          · exact .inr (.inr rfl)
        · exact .inr (.inl (hcl pc hm hne' q hq))
        · exact absurd rfl hne'
      · rintro pc (rfl | hm | rfl) hne' hh
        · simp [crHead, hop] at hh
        · rw [crWalk_rep_opt hne]
          exact hcr pc hm hne' hh
        · exact absurd rfl hne'
      · rw [crWalk_rep_opt hne]
        exact ⟨fun _ => rfl, fun _ => .inr (.inr rfl)⟩
  | @repMany rlo rhi greedy body r rhi32 lo m h0 h1 hz hloop henter hb hnext
      hr0 hr hrep ih =>
      obtain ⟨S, hS0, hbd, hcl, hcr, hhi⟩ := ih
      have hl := hb.le
      have hsz' := succs_plain (reps := reps) hz
      have hse := succs_plain (reps := reps) henter
      have hsl : succs code reps (lo + 1) =
          if rlo == 0 then [lo + 2, m + 1] else [lo + 2] := by
        simp [succs, hloop, hrep]
      have hsn : succs code reps m = [lo + 1, m + 1] := by
        simp [succs, hnext, hrep]
      refine ⟨fun pc => pc = lo ∨ pc = lo + 1 ∨ pc = lo + 2 ∨ S pc ∨
          ((rlo == 0 || (crWalk body).2) = true ∧ pc = m + 1),
        .inl rfl, ?_, ?_, ?_, ?_⟩
      · rintro pc (rfl | rfl | rfl | hm | ⟨_, rfl⟩)
        · omega
        · omega
        · omega
        · have := hbd pc hm
          omega
        · omega
      · rintro pc (rfl | rfl | rfl | hm | ⟨_, rfl⟩) hne q hq
        · rw [hsz'] at hq
          rcases List.mem_singleton.mp hq with rfl
          exact .inr (.inl rfl)
        · rw [hsl] at hq
          by_cases hz0 : rlo == 0
          · rw [if_pos hz0] at hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact .inr (.inr (.inl rfl))
            · exact .inr (.inr (.inr (.inr ⟨by simp [hz0], rfl⟩)))
          · rw [if_neg hz0] at hq
            rcases List.mem_singleton.mp hq with rfl
            exact .inr (.inr (.inl rfl))
        · rw [hse] at hq
          rcases List.mem_singleton.mp hq with rfl
          exact .inr (.inr (.inr (.inl hS0)))
        · by_cases hpm : pc = m
          · subst hpm
            have htr := hhi.mp hm
            rw [hsn] at hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact .inr (.inl rfl)
            · exact .inr (.inr (.inr (.inr ⟨by simp [htr], rfl⟩)))
          · exact .inr (.inr (.inr (.inl (hcl pc hm hpm q hq))))
        · exact absurd rfl hne
      · rintro pc (rfl | rfl | rfl | hm | ⟨_, rfl⟩) hne hh
        · rw [crHead_plain hz] at hh
          cases hh
        · simp [crHead, hloop] at hh
        · rw [crHead_plain henter] at hh
          cases hh
        · rw [crWalk_rep_many h0 h1]
          by_cases hpm : pc = m
          · subst hpm
            simp [crHead, hnext] at hh
          · exact hcr pc hm hpm hh
        · exact absurd rfl hne
      · rw [crWalk_rep_many h0 h1]
        constructor
        · rintro (heq | heq | heq | hm | ⟨htr, _⟩)
          · exact absurd heq (by omega)
          · exact absurd heq (by omega)
          · exact absurd heq (by omega)
          · have := hbd _ hm
            exact absurd this.2 (by omega)
          · exact htr
        · intro htr
          exact .inr (.inr (.inr (.inr ⟨htr, rfl⟩)))

theorem Frag.reach {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : Frag code classes reps r0 a lo hi) :
    hi < code.size →
      ((crWalk a).1 = true → ∃ pc, pc < code.size ∧
        Reach code reps lo pc ∧ crHead code classes pc = true) ∧
      ((crWalk a).2 = true → Reach code reps lo hi) := by
  induction h with
  | @empty a lo hw =>
      intro hhi
      refine ⟨fun h' => ?_, fun _ => .refl lo⟩
      simp [hw] at h'
  | @chr b lo hcell =>
      intro hhi
      constructor
      · intro h'
        refine ⟨lo, by omega, .refl lo, ?_⟩
        simp only [crHead, hcell]
        rw [toNat_beq_cr]
        have hcw : (crWalk (Ast.chr b)).1 = (b == 0x0D) := by simp [crWalk]
        rw [hcw] at h'
        exact h'
      · intro h'
        simp [crWalk] at h'
  | @chrCI b lo hcell =>
      intro hhi
      constructor
      · intro h'
        refine ⟨lo, by omega, .refl lo, ?_⟩
        simp only [crHead, hcell]
        rw [toNat_beq_cr]
        have hcw : (crWalk (Ast.chrCI b)).1 = (b == 0x0D) := by simp [crWalk]
        rw [hcw] at h'
        exact h'
      · intro h'
        simp [crWalk] at h'
  | @cls bits lo idx hcell hin hbyte =>
      intro hhi
      constructor
      · intro h'
        refine ⟨lo, by omega, .refl lo, ?_⟩
        simp only [crHead, hcell]
        rw [hbyte, classBits_cr]
        have hcw : (crWalk (Ast.cls bits)).1 = bits.has 0x0D := by
          simp [crWalk]
        rw [hcw] at h'
        exact h'
      · intro h'
        simp [crWalk] at h'
  | @wild a lo hw hcell =>
      intro hhi
      constructor
      · intro _
        refine ⟨lo, by omega, .refl lo, ?_⟩
        rcases hcell with h' | h' | h' <;> simp [crHead, h']
      · intro h'
        rw [hw] at h'
        cases h'
  | @asrt a lo hw hcell =>
      intro hhi
      constructor
      · intro h'
        simp [hw] at h'
      · intro _
        exact Reach.single ⟨by omega, hhi,
          by rw [succs_plain hcell]; exact List.mem_singleton.mpr rfl⟩
  | @catCons k kids lo mid hi h₁ h₂ ih₁ ih₂ =>
      intro hhi
      have l₂ := h₂.le
      obtain ⟨ihc₁, iht₁⟩ := ih₁ (by omega)
      obtain ⟨ihc₂, iht₂⟩ := ih₂ hhi
      constructor
      · intro h'
        rw [crWalk_cat_cons₁, Bool.or_eq_true] at h'
        rcases h' with h' | h'
        · exact ihc₁ h'
        · rw [Bool.and_eq_true] at h'
          obtain ⟨pc, hplt, hre, hch⟩ := ihc₂ h'.2
          exact ⟨pc, hplt, (iht₁ h'.1).trans hre, hch⟩
      · intro h'
        rw [crWalk_cat_cons₂, Bool.and_eq_true] at h'
        exact (iht₁ h'.1).trans (iht₂ h'.2)
  | altOne h ih =>
      intro hhi
      obtain ⟨ihc, iht⟩ := ih hhi
      constructor
      · intro h'
        rw [crWalk_alt_one] at h'
        exact ihc h'
      · intro h'
        rw [crWalk_alt_one] at h'
        exact iht h'
  | @altCons a b rest lo j hi hsplit h₁ hjump h₂ ih₁ ih₂ =>
      intro hhi
      have l₁ := h₁.le
      have l₂ := h₂.le
      obtain ⟨ihc₁, iht₁⟩ := ih₁ (by omega)
      obtain ⟨ihc₂, iht₂⟩ := ih₂ hhi
      have s1 : Step code reps lo (lo + 1) :=
        ⟨by omega, by omega, by simp [succs, hsplit]⟩
      have s2 : Step code reps lo (j + 1) :=
        ⟨by omega, by omega, by simp [succs, hsplit]⟩
      have s3 : Step code reps j hi := ⟨by omega, hhi, by simp [succs, hjump]⟩
      constructor
      · intro h'
        rw [crWalk_alt_cons₁, Bool.or_eq_true] at h'
        rcases h' with h' | h'
        · obtain ⟨pc, hplt, hre, hch⟩ := ihc₁ h'
          exact ⟨pc, hplt, Reach.head s1 hre, hch⟩
        · obtain ⟨pc, hplt, hre, hch⟩ := ihc₂ h'
          exact ⟨pc, hplt, Reach.head s2 hre, hch⟩
      · intro h'
        rw [crWalk_alt_cons₂, Bool.or_eq_true] at h'
        rcases h' with h' | h'
        · exact (Reach.head s1 (iht₁ h')).tail s3
        · exact Reach.head s2 (iht₂ h')
  | grpBody h ih =>
      intro hhi
      obtain ⟨ihc, iht⟩ := ih hhi
      constructor
      · intro h'
        rw [crWalk_grp] at h'
        exact ihc h'
      · intro h'
        rw [crWalk_grp] at h'
        exact iht h'
  | @grpSaves cap body lo m hopen h hclose ih =>
      intro hhi
      have hl := h.le
      obtain ⟨ihc, iht⟩ := ih (by omega)
      have s1 : Step code reps lo (lo + 1) := ⟨by omega, by omega,
        by rw [succs_plain hopen]; exact List.mem_singleton.mpr rfl⟩
      have s2 : Step code reps m (m + 1) := ⟨by omega, hhi,
        by rw [succs_plain hclose]; exact List.mem_singleton.mpr rfl⟩
      constructor
      · intro h'
        rw [crWalk_grp] at h'
        obtain ⟨pc, hplt, hre, hch⟩ := ihc h'
        exact ⟨pc, hplt, Reach.head s1 hre, hch⟩
      · intro h'
        rw [crWalk_grp] at h'
        exact (Reach.head s1 (iht h')).tail s2
  | repOne h ih =>
      intro hhi
      obtain ⟨ihc, iht⟩ := ih hhi
      constructor
      · intro h'
        rw [crWalk_rep_one] at h'
        exact ihc h'
      · intro h'
        rw [crWalk_rep_one] at h'
        exact iht h'
  | @repOpt rlo greedy body lo hi hne hop harm h ih =>
      intro hhi
      have hl := h.le
      obtain ⟨ihc, iht⟩ := ih hhi
      have hmem1 : (lo + 1) ∈ succs code reps lo := by
        rcases harm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [succs, hop, e1, e2]
      have hmemh : hi ∈ succs code reps lo := by
        rcases harm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [succs, hop, e1, e2]
      have s1 : Step code reps lo (lo + 1) := ⟨by omega, by omega, hmem1⟩
      constructor
      · intro h'
        rw [crWalk_rep_opt hne] at h'
        obtain ⟨pc, hplt, hre, hch⟩ := ihc h'
        exact ⟨pc, hplt, Reach.head s1 hre, hch⟩
      · intro _
        exact Reach.single ⟨by omega, hhi, hmemh⟩
  | @repMany rlo rhi greedy body r rhi32 lo m h0 h1 hz hloop henter hb hnext
      hr0 hr hrep ih =>
      intro hhi
      have hl := hb.le
      obtain ⟨ihc, iht⟩ := ih (by omega)
      have s0 : Step code reps lo (lo + 1) := ⟨by omega, by omega,
        by rw [succs_plain hz]; exact List.mem_singleton.mpr rfl⟩
      have s1 : Step code reps (lo + 1) (lo + 2) := by
        refine ⟨by omega, by omega, ?_⟩
        by_cases hz0 : rlo == 0 <;> simp [succs, hloop, hrep, hz0]
      have s2 : Step code reps (lo + 2) (lo + 3) := ⟨by omega, by omega,
        by rw [succs_plain henter]; exact List.mem_singleton.mpr rfl⟩
      have s3 : Step code reps m (m + 1) := ⟨by omega, hhi,
        by simp [succs, hnext, hrep]⟩
      have hentry : Reach code reps lo (lo + 3) :=
        ((Reach.single s0).tail s1).tail s2
      constructor
      · intro h'
        rw [crWalk_rep_many h0 h1] at h'
        obtain ⟨pc, hplt, hre, hch⟩ := ihc h'
        exact ⟨pc, hplt, hentry.trans hre, hch⟩
      · intro h'
        rw [crWalk_rep_many h0 h1] at h'
        have h'' : (rlo == 0 || (crWalk body).2) = true := h'
        rw [Bool.or_eq_true] at h''
        rcases h'' with hz0 | htr
        · have s4 : Step code reps (lo + 1) (m + 1) :=
            ⟨by omega, hhi, by simp [succs, hloop, hrep, hz0]⟩
          exact (Reach.single s0).tail s4
        · exact ((hentry.trans (iht htr)).tail s3)

theorem Frag.weaken {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 r0' : Nat} {a : Ast} {lo hi : Nat}
    (h : Frag code classes reps r0' a lo hi) (hle : r0 ≤ r0') :
    Frag code classes reps r0 a lo hi := by
  induction h with
  | empty hw => exact .empty hw
  | chr hcell => exact .chr hcell
  | chrCI hcell => exact .chrCI hcell
  | cls hcell hin hbyte => exact .cls hcell hin hbyte
  | wild hw hcell => exact .wild hw hcell
  | asrt hw hcell => exact .asrt hw hcell
  | catCons h₁ h₂ ih₁ ih₂ => exact .catCons ih₁ ih₂
  | altOne h ih => exact .altOne ih
  | altCons hsplit h₁ hjump h₂ ih₁ ih₂ => exact .altCons hsplit ih₁ hjump ih₂
  | grpBody h ih => exact .grpBody ih
  | grpSaves hopen h hclose ih => exact .grpSaves hopen ih hclose
  | repOne h ih => exact .repOne ih
  | repOpt hne hop harm h ih => exact .repOpt hne hop harm ih
  | repMany h0 h1 hz hloop henter hb hnext hr0 hr hrep ih =>
      exact .repMany h0 h1 hz hloop henter ih hnext (by omega) hr hrep

/-! ## The compiler establishes the relation

`compileNode` only ever appends code and classes, appends repetition
records, patches cells it laid down itself and finishes the one record
it opened — so a finished fragment survives the rest of compilation.
`Ext` is that no-clobber contract between two codegen states, floored at
the repetition watermark the construct started from, and
`compileNode_facts` proves each construct lays down its `Frag` and
honors the contract. The alternation chain gets the strengthened
statement its late jump patching needs, exactly like RefineProto's
`compileAlt_facts`. -/

private theorem getBang_push_lt {α : Type _} [Inhabited α] (a : Array α)
    (x : α) {i : Nat} (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp <;> omega), getElem!_pos a i h]
  exact Array.getElem_push_lt h

private theorem getBang_push_eq {α : Type _} [Inhabited α] (a : Array α)
    (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  exact Array.getElem_push_eq ..

private theorem getBang_modify_ne {α : Type _} [Inhabited α] (a : Array α)
    (j : Nat) {f : α → α} {i : Nat} (h : i ≠ j) :
    (a.modify j f)[i]! = a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos (a.modify j f) i (by simpa using hi),
      getElem!_pos a i hi]
    exact Array.getElem_modify_of_ne (Ne.symm h) f (by simpa using hi)
  · rw [getElem!_neg (a.modify j f) i (by simpa using hi),
      getElem!_neg a i hi]

private theorem getBang_modify_eq {α : Type _} [Inhabited α] (a : Array α)
    (j : Nat) {f : α → α} (h : j < a.size) :
    (a.modify j f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.modify j f) j (by simpa using h),
    getElem!_pos a j h]
  exact Array.getElem_modify_self f (by simpa using h)

private theorem getBang_append_lt {α : Type _} [Inhabited α] (a b : Array α)
    {i : Nat} (h : i < a.size) : (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp <;> omega), getElem!_pos a i h]
  exact Array.getElem_append_left h

private theorem getBang_append_right {α : Type _} [Inhabited α]
    (a b : Array α) {j : Nat} (h : j < b.size) :
    (a ++ b)[a.size + j]! = b[j]! := by
  rw [getElem!_pos (a ++ b) (a.size + j) (by simp <;> omega),
    getElem!_pos b j h]
  rw [Array.getElem_append_right (by omega)]
  congr 1
  omega

/-- The no-clobber contract between two codegen states: everything the
first state had already laid down survives into the second, repetition
records from the floor `r0` up included. -/
structure Ext (st st' : CState) : Prop where
  code_le : st.code.size ≤ st'.code.size
  code_at : ∀ pc, pc < st.code.size → st'.code[pc]! = st.code[pc]!
  cls_le : st.classes.size ≤ st'.classes.size
  cls_at : ∀ i, i < st.classes.size → st'.classes[i]! = st.classes[i]!
  reps_le : st.reps.size ≤ st'.reps.size
  reps_at : ∀ i, i < st.reps.size → st'.reps[i]! = st.reps[i]!

theorem Ext.refl (st : CState) : Ext st st :=
  ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl,
    Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {st₁ st₂ st₃ : CState} (h₁ : Ext st₁ st₂)
    (h₂ : Ext st₂ st₃) : Ext st₁ st₃ where
  code_le := Nat.le_trans h₁.code_le h₂.code_le
  code_at pc hpc := (h₂.code_at pc (by have := h₁.code_le; omega)).trans
    (h₁.code_at pc hpc)
  cls_le := Nat.le_trans h₁.cls_le h₂.cls_le
  cls_at i hi := (h₂.cls_at i (by have := h₁.cls_le; omega)).trans
    (h₁.cls_at i hi)
  reps_le := Nat.le_trans h₁.reps_le h₂.reps_le
  reps_at i hi := (h₂.reps_at i (by have := h₁.reps_le; omega)).trans
    (h₁.reps_at i hi)

/-- A fragment carried across the contract. -/
theorem Frag.ext {r0 : Nat} {st st' : CState} {a : Ast} {lo hi : Nat}
    (h : Frag st.code st.classes st.reps r0 a lo hi)
    (hhi : hi ≤ st.code.size) (he : Ext st st') :
    Frag st'.code st'.classes st'.reps r0 a lo hi :=
  h.mono (fun pc _ h2 => he.code_at pc (by omega)) he.cls_le he.cls_at
    he.reps_le (fun i _ hi => he.reps_at i hi)

private theorem ext_emit (st : CState) (i : Inst) :
    Ext st (emit st i).1 :=
  ⟨by simp [emit], fun pc hpc => getBang_push_lt st.code i hpc,
    Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl⟩

private theorem ext_openRegion (st : CState) (k : Rk) (p : Nat) :
    Ext st (openRegion st k p).1 :=
  ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl,
    Nat.le_refl _, fun _ _ => rfl⟩

private theorem ext_closeRegion (st : CState) (r : Nat) :
    Ext st (closeRegion st r) :=
  ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl,
    Nat.le_refl _, fun _ _ => rfl⟩

private theorem dropEmptyRegion_code (st : CState) (r : Nat) :
    (dropEmptyRegion st r).code = st.code ∧
    (dropEmptyRegion st r).classes = st.classes ∧
    (dropEmptyRegion st r).reps = st.reps := by
  unfold dropEmptyRegion
  split
  · split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

private theorem ext_dropEmptyRegion (st : CState) (r : Nat) :
    Ext st (dropEmptyRegion st r) := by
  obtain ⟨h1, h2, h3⟩ := dropEmptyRegion_code st r
  exact ⟨Nat.le_of_eq (by rw [h1]), fun pc _ => by rw [h1],
    Nat.le_of_eq (by rw [h2]), fun i _ => by rw [h2],
    Nat.le_of_eq (by rw [h3]), fun i _ => by rw [h3]⟩

/-- The state after an alternation's split is laid down and patched to
enter its branch, then the branch region and body: the shapes
`compileAlt` steps through, named so the equations below can too. -/
private def altSplitSt (st : CState) : CState :=
  { st with code := ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
      (fun i => { i with
                    arg := st.code.size + 1 })) }

private def altBranchSt (inside : Nat) (st : CState) : CState :=
  { st with regions := (st.regions.push
      ⟨.branch, inside, st.code.size, st.code.size⟩) }

private def altMid (arm : Ast) (inside : Nat) (st : CState) : CState :=
  compileNode arm st.regions.size (altBranchSt inside (altSplitSt st))

/-- And after the branch closes: region shut, jump emitted, the split's
second arm patched to the next link. -/
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
  rw [compileAlt]
  rfl

private theorem compileAlt_nil_eq (arm : Ast) (inside : Nat)
    (jumps : Array Nat) (st : CState) :
    compileAlt arm [] inside jumps st =
      closeRegion
        (jumps.foldl
          (fun s pc => patch s pc fun i =>
            { i with
                arg := (compileNode arm st.regions.size
                (altBranchSt inside st)).code.size })
          (compileNode arm st.regions.size (altBranchSt inside st)))
        st.regions.size := by
  rw [compileAlt]
  rfl

/-- Patching a batch of collected jumps: sizes stay put, the class and
repetition tables stay put, untouched cells stay put, and every named
cell gets the new target — duplicates are harmless because the patch is
idempotent. -/
private theorem patchAll_facts (stop : Nat) :
    ∀ (js : List Nat) (st : CState),
      (js.foldl (fun s pc => patch s pc fun i => { i with
                                                     arg := stop })
        st).code.size = st.code.size ∧
      (∀ pc, pc ∉ js →
        (js.foldl (fun s pc => patch s pc fun i => { i with
                                                       arg := stop })
          st).code[pc]! = st.code[pc]!) ∧
      (∀ pc ∈ js, pc < st.code.size →
        (js.foldl (fun s pc => patch s pc fun i => { i with
                                                       arg := stop })
          st).code[pc]! = { st.code[pc]! with arg := stop }) ∧
      (js.foldl (fun s pc => patch s pc fun i => { i with
                                                     arg := stop })
        st).classes = st.classes ∧
      (js.foldl (fun s pc => patch s pc fun i => { i with
                                                     arg := stop })
        st).reps = st.reps
  | [], st => by simp
  | j :: js', st => by
      obtain ⟨hsz, hpre, hhit, hcls, hreps⟩ := patchAll_facts stop js'
        (patch st j fun i => { i with
                                 arg := stop })
      have hpsz : (patch st j fun i => { i with
                                           arg := stop }).code.size =
          st.code.size := by
        simp [patch]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
          have hcell : (patch st pc fun i =>
              { i with
                  arg := stop }).code[pc]! =
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
          have hcell : (patch st j fun i =>
              { i with
                  arg := stop }).code[pc]! = st.code[pc]! := by
            simp only [patch]
            exact getBang_modify_ne st.code j hj
          rw [hhit pc hmem (by rw [hpsz]; exact hlt), hcell]
      · rw [List.foldl_cons, hcls]
        rfl
      · rw [List.foldl_cons, hreps]
        rfl

/-- What `compileNode_facts` proves, named because the alternation chain
consumes it for its branch bodies. -/
private def NodeIH (n : Nat) : Prop :=
  ∀ {a : Ast}, sizeOf a ≤ n → NoEmptyAlt a →
    ∀ (here : Nat) (st : CState), 32 ∣ st.classes.size →
      Ext st (compileNode a here st) ∧
      32 ∣ (compileNode a here st).classes.size ∧
      Frag (compileNode a here st).code (compileNode a here st).classes
        (compileNode a here st).reps st.reps.size a st.code.size
        (compileNode a here st).code.size

/-- What `compileAlt` does to the state, strengthened the way the chain
needs it: the collected jump cells — laid down by earlier links and
still blank — all end up pointing at the final stop, everything else
already laid down survives, the tables only grow, and the new range is
the chain's fragment. -/
private theorem compileAlt_facts {n : Nat} (ih : NodeIH n) :
    ∀ (rest : List Ast) (arm : Ast), sizeOf arm ≤ n → NoEmptyAlt arm →
      (∀ x ∈ rest, sizeOf x ≤ n ∧ NoEmptyAlt x) →
      ∀ (inside : Nat) (jumps : Array Nat) (st : CState),
        32 ∣ st.classes.size →
        (∀ p ∈ jumps.toList, p < st.code.size) →
        st.code.size ≤ (compileAlt arm rest inside jumps st).code.size ∧
        (∀ pc, pc < st.code.size → pc ∉ jumps.toList →
          (compileAlt arm rest inside jumps st).code[pc]! = st.code[pc]!) ∧
        (∀ p ∈ jumps.toList,
          (compileAlt arm rest inside jumps st).code[p]! =
            { st.code[p]! with
                arg := (compileAlt arm rest inside jumps st).code.size }) ∧
        st.classes.size ≤ (compileAlt arm rest inside jumps st).classes.size ∧
        (∀ i, i < st.classes.size →
          (compileAlt arm rest inside jumps st).classes[i]! =
            st.classes[i]!) ∧
        32 ∣ (compileAlt arm rest inside jumps st).classes.size ∧
        st.reps.size ≤ (compileAlt arm rest inside jumps st).reps.size ∧
        (∀ i, i < st.reps.size →
          (compileAlt arm rest inside jumps st).reps[i]! = st.reps[i]!) ∧
        Frag (compileAlt arm rest inside jumps st).code
          (compileAlt arm rest inside jumps st).classes
          (compileAlt arm rest inside jumps st).reps st.reps.size
          (.alt (arm :: rest)) st.code.size
          (compileAlt arm rest inside jumps st).code.size := by
  intro rest
  induction rest with
  | nil =>
      intro arm hszarm hwarm _ inside jumps st hdiv hj
      obtain ⟨he, hdiv', hfrag⟩ :=
        ih hszarm hwarm st.regions.size (altBranchSt inside st) hdiv
      have hb1 : (altBranchSt inside st).code.size = st.code.size := rfl
      have hb2 : (altBranchSt inside st).classes.size = st.classes.size := rfl
      have hb3 : (altBranchSt inside st).reps.size = st.reps.size := rfl
      obtain ⟨hfsz, hfpre, hfhit, hfcls, hfreps⟩ :=
        patchAll_facts
          (compileNode arm st.regions.size (altBranchSt inside st)).code.size
          jumps.toList
          (compileNode arm st.regions.size (altBranchSt inside st))
      have hout : compileAlt arm [] inside jumps st =
          closeRegion
            (jumps.toList.foldl
              (fun s pc => patch s pc fun i =>
                { i with
                    arg := (compileNode arm st.regions.size
                    (altBranchSt inside st)).code.size })
              (compileNode arm st.regions.size (altBranchSt inside st)))
            st.regions.size := by
        rw [compileAlt_nil_eq, ← Array.foldl_toList]
      have hPc : ∀ (X : CState) (r : Nat), (closeRegion X r).code = X.code :=
        fun _ _ => rfl
      have hPcl : ∀ (X : CState) (r : Nat),
          (closeRegion X r).classes = X.classes := fun _ _ => rfl
      have hPr : ∀ (X : CState) (r : Nat), (closeRegion X r).reps = X.reps :=
        fun _ _ => rfl
      rw [hout, hPc, hPcl, hPr, hfsz, hfcls, hfreps]
      refine ⟨he.code_le, ?_, ?_, he.cls_le, he.cls_at, hdiv',
        he.reps_le, he.reps_at, ?_⟩
      · intro pc hpc hnot
        rw [hfpre pc hnot]
        exact he.code_at pc hpc
      · intro p hp
        have hplt := hj p hp
        rw [hfhit p hp (by have := he.code_le; omega),
          he.code_at p hplt]
        rfl
      · refine .altOne (hfrag.mono ?_ (Nat.le_refl _) (fun i _ => rfl)
          (Nat.le_refl _) (fun i _ _ => rfl))
        intro pc h1 h2
        exact hfpre pc fun hin => absurd (hj pc hin) (by omega)
  | cons bb rest' ihrest =>
      intro arm hszarm hwarm helems inside jumps st hdiv hj
      rw [compileAlt_cons_eq]
      have hsplitsz : (altSplitSt st).code.size = st.code.size + 1 := by
        simp [altSplitSt]
      obtain ⟨he, hdiv', hfrag⟩ :=
        ih hszarm hwarm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st)) hdiv
      have hmid : compileNode arm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st)) = altMid arm inside st := rfl
      rw [hmid] at he hfrag hdiv'
      have hbc : (altBranchSt inside (altSplitSt st)).code.size =
          st.code.size + 1 := by
        rw [show (altBranchSt inside (altSplitSt st)).code.size =
          (altSplitSt st).code.size from rfl, hsplitsz]
      have hbcl : (altBranchSt inside (altSplitSt st)).classes.size =
          st.classes.size := rfl
      have hbr : (altBranchSt inside (altSplitSt st)).reps.size =
          st.reps.size := rfl
      have hfrag2 : Frag (altMid arm inside st).code
          (altMid arm inside st).classes (altMid arm inside st).reps
          st.reps.size arm (st.code.size + 1)
          (altMid arm inside st).code.size := by
        rw [← hbc, ← hbr]
        exact hfrag
      have hle : st.code.size + 1 ≤ (altMid arm inside st).code.size := by
        have := he.code_le
        rw [show (altBranchSt inside (altSplitSt st)).code.size =
          (altSplitSt st).code.size from rfl, hsplitsz] at this
        exact this
      have hpre : ∀ pc, pc < st.code.size + 1 →
          (altMid arm inside st).code[pc]! = (altSplitSt st).code[pc]! := by
        intro pc hpc
        have := he.code_at pc (by
          rw [show (altBranchSt inside (altSplitSt st)).code.size =
            (altSplitSt st).code.size from rfl, hsplitsz]
          exact hpc)
        exact this
      have hsplit_cell : (altSplitSt st).code[st.code.size]! =
          ⟨.split, st.code.size + 1, 0⟩ := by
        show ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
            (fun i => { i with
                          arg := st.code.size + 1 }))[st.code.size]! =
          ⟨.split, st.code.size + 1, 0⟩
        rw [getBang_modify_eq _ st.code.size (by simp), getBang_push_eq]
      have hsplit_pre : ∀ pc, pc < st.code.size →
          (altSplitSt st).code[pc]! = st.code[pc]! := by
        intro pc hpc
        show ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
            (fun i => { i with
                          arg := st.code.size + 1 }))[pc]! = st.code[pc]!
        rw [getBang_modify_ne _ st.code.size (by omega),
          getBang_push_lt _ _ hpc]
      have houtc : (altOut arm inside st).code =
          ((altMid arm inside st).code.push ⟨.jump, 0, 0⟩).modify st.code.size
            (fun i => { i with
                    alt := ((altMid arm inside st).code.push ⟨.jump, 0, 0⟩).size }) :=
        rfl
      have houtsz : (altOut arm inside st).code.size =
          (altMid arm inside st).code.size + 1 := by
        rw [houtc]
        simp
      have hout_jump :
          (altOut arm inside st).code[(altMid arm inside st).code.size]! =
            ⟨.jump, 0, 0⟩ := by
        rw [houtc, getBang_modify_ne _ st.code.size (by omega),
          getBang_push_eq]
      have hout_split : (altOut arm inside st).code[st.code.size]! =
          ⟨.split, st.code.size + 1, (altMid arm inside st).code.size + 1⟩ := by
        rw [houtc, getBang_modify_eq _ st.code.size (by simp <;> omega),
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
      have hout_cls : (altOut arm inside st).classes =
          (altMid arm inside st).classes := rfl
      have hout_reps : (altOut arm inside st).reps =
          (altMid arm inside st).reps := rfl
      obtain ⟨hszbb, hwbb⟩ := helems bb (List.mem_cons_self ..)
      obtain ⟨cle, cpre, chit, ccls_le, ccls_at, ccls_div, creps_le,
          creps_at, cfrag⟩ :=
        ihrest bb hszbb hwbb
          (fun x hx => helems x (List.mem_cons_of_mem bb hx))
          inside (jumps.push (altMid arm inside st).code.size)
          (altOut arm inside st)
          (by rw [hout_cls]; exact hdiv')
          (by
            intro p hp
            rw [Array.toList_push] at hp
            rcases List.mem_append.mp hp with hp' | hp'
            · have := hj p hp'
              omega
            · rw [List.mem_singleton] at hp'
              omega)
      rw [houtsz] at cle cpre cfrag
      rw [hout_cls] at ccls_le ccls_at
      rw [hout_reps] at creps_le creps_at
      have hmem_push : ∀ p,
          p ∈ (jumps.push (altMid arm inside st).code.size).toList ↔
          (p ∈ jumps.toList ∨ p = (altMid arm inside st).code.size) := by
        intro p
        rw [Array.toList_push, List.mem_append, List.mem_singleton]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ccls_div, ?_, ?_, ?_⟩
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
      · have h1 := he.cls_le
        exact Nat.le_trans h1 ccls_le
      · intro i hi
        rw [ccls_at i (by have := he.cls_le; omega), he.cls_at i hi]
        rfl
      · have h1 := he.reps_le
        exact Nat.le_trans h1 creps_le
      · intro i hi
        rw [creps_at i (by have := he.reps_le; omega), he.reps_at i hi]
        rfl
      · refine .altCons (j := (altMid arm inside st).code.size) ?_ ?_ ?_ ?_
        · rw [cpre st.code.size (by omega) (by
              rw [hmem_push]
              rintro (h' | h')
              · have := hj st.code.size h'
                omega
              · omega)]
          exact hout_split
        · refine hfrag2.mono ?_ ccls_le ?_ creps_le ?_
          · intro pc hp1 hp2
            rw [cpre pc (by omega) (by
                  rw [hmem_push]
                  rintro (h' | h')
                  · have := hj pc h'
                    omega
                  · omega),
              hout_pre pc (by omega) (by omega)]
          · intro i hi
            exact ccls_at i (by have := he.cls_le; omega)
          · intro i hi0 hi
            exact creps_at i hi
        · have hcell := chit (altMid arm inside st).code.size
            ((hmem_push (altMid arm inside st).code.size).mpr (.inr rfl))
          rw [hcell, hout_jump]
        · exact cfrag.weaken (by have := he.reps_le; exact this)

private theorem getBang_push_at {α : Type _} [Inhabited α] (a : Array α)
    (x : α) {i : Nat} (h : i = a.size) : (a.push x)[i]! = x := by
  subst h
  exact getBang_push_eq a x

private theorem ext_patch {base st : CState} (pc : Nat) (f : Inst → Inst)
    (hpc : base.code.size ≤ pc) (he : Ext base st) :
    Ext base (patch st pc f) where
  code_le := by
    have := he.code_le
    simp [patch]
    omega
  code_at q hq := by
    show (st.code.modify pc f)[q]! = base.code[q]!
    rw [getBang_modify_ne st.code pc (by omega)]
    exact he.code_at q hq
  cls_le := he.cls_le
  cls_at := he.cls_at
  reps_le := he.reps_le
  reps_at := he.reps_at

/-- One plain cell emitted for a transparent construct: the bundle for
every assertion. -/
private theorem plain_emit_bundle (st : CState) (i : Inst) {a : Ast}
    (hdiv : 32 ∣ st.classes.size)
    (hfrag : Frag (st.code.push i) st.classes st.reps st.reps.size a
      st.code.size (st.code.size + 1)) :
    Ext st (emit st i).1 ∧ 32 ∣ (emit st i).1.classes.size ∧
    Frag (emit st i).1.code (emit st i).1.classes (emit st i).1.reps
      st.reps.size a st.code.size (emit st i).1.code.size := by
  refine ⟨ext_emit st i, hdiv, ?_⟩
  have hsz' : (emit st i).1.code.size = st.code.size + 1 := by
    simp [emit]
  rw [hsz']
  exact hfrag

/-- The bundle for a capturing group's compiled shape, stated over
abstract states pinned by component equations, so the caller can hand
in the compiler's raw let-chain and prove the equations by `rfl` or a
size rewrite instead of fighting the full term syntactically. -/
private theorem grp_saves_bundle {n : Nat} (ihn : NodeIH n) {body : Ast}
    (hszb : sizeOf body ≤ n) (hwb : NoEmptyAlt body) (cap : Nat)
    (st st1 F : CState) (here' : Nat) (hdiv : 32 ∣ st.classes.size)
    (hc1 : st1.code = st.code.push ⟨.save, 2 * cap, 0⟩)
    (hcl1 : st1.classes = st.classes)
    (hr1 : st1.reps = st.reps)
    (hFc : F.code = (compileNode body here' st1).code.push
      ⟨.save, 2 * cap + 1, 0⟩)
    (hFcl : F.classes = (compileNode body here' st1).classes)
    (hFr : F.reps = (compileNode body here' st1).reps) :
    Ext st F ∧ 32 ∣ F.classes.size ∧
      Frag F.code F.classes F.reps st.reps.size (.grp cap body)
        st.code.size F.code.size := by
  obtain ⟨he, hdivB, hfragB⟩ := ihn hszb hwb here' st1 (by rw [hcl1]; exact hdiv)
  have e1 : st1.code.size = st.code.size + 1 := by
    rw [hc1]
    simp
  have hle2 : st.code.size + 1 ≤ (compileNode body here' st1).code.size := by
    have := he.code_le
    rw [e1] at this
    exact this
  have hFsz : F.code.size = (compileNode body here' st1).code.size + 1 := by
    rw [hFc]
    simp
  have hpre : ∀ pc, pc < (compileNode body here' st1).code.size →
      F.code[pc]! = (compileNode body here' st1).code[pc]! := by
    intro pc h
    rw [hFc, getBang_push_lt _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by rw [hFsz]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro pc hpc
      rw [hpre pc (by omega), he.code_at pc (by rw [e1]; omega), hc1,
        getBang_push_lt _ _ hpc]
    · rw [hFcl]
      have := he.cls_le
      rw [hcl1] at this
      exact this
    · intro i hi
      rw [hFcl, he.cls_at i (by rw [hcl1]; exact hi), hcl1]
    · rw [hFr]
      have := he.reps_le
      rw [hr1] at this
      exact this
    · intro i hi
      rw [hFr, he.reps_at i (by rw [hr1]; exact hi), hr1]
  · rw [hFcl]
    exact hdivB
  · rw [hFsz]
    refine Frag.grpSaves ?_ ?_ ?_
    · rw [hpre _ (by omega), he.code_at _ (by rw [e1]; omega), hc1,
        getBang_push_eq]
      rfl
    · have hbf := hfragB
      rw [e1, hr1] at hbf
      refine hbf.mono (fun pc h1 h2 => hpre pc h2)
        (Nat.le_of_eq (by rw [hFcl])) (fun i _ => by rw [hFcl])
        (Nat.le_of_eq (by rw [hFr])) (fun i _ _ => by rw [hFr])
    · rw [hFc, getBang_push_eq]
      rfl
/-- The same style for the optional item's split block. -/
private theorem rep_opt_bundle {n : Nat} (ihn : NodeIH n) {body : Ast}
    (hszb : sizeOf body ≤ n) (hwb : NoEmptyAlt body) (rlo : Nat)
    (greedy : Bool) (hne : (rlo == 1) = false)
    (st st1 F : CState) (here' : Nat) (hdiv : 32 ∣ st.classes.size)
    (hc1 : st1.code = st.code.push ⟨.split, 0, 0⟩)
    (hcl1 : st1.classes = st.classes)
    (hr1 : st1.reps = st.reps)
    (hFc : F.code = (compileNode body here' st1).code.modify st.code.size
      (fun i =>
        if greedy then
          { i with
              arg := st.code.size + 1,
              alt := (compileNode body here' st1).code.size }
        else
          { i with
              arg := (compileNode body here' st1).code.size,
              alt := st.code.size + 1 }))
    (hFcl : F.classes = (compileNode body here' st1).classes)
    (hFr : F.reps = (compileNode body here' st1).reps) :
    Ext st F ∧ 32 ∣ F.classes.size ∧
      Frag F.code F.classes F.reps st.reps.size
        (.rep rlo (some 1) greedy body) st.code.size F.code.size := by
  obtain ⟨he, hdivB, hfragB⟩ := ihn hszb hwb here' st1 (by rw [hcl1]; exact hdiv)
  have e1 : st1.code.size = st.code.size + 1 := by
    rw [hc1]
    simp
  have hle2 : st.code.size + 1 ≤ (compileNode body here' st1).code.size := by
    have := he.code_le
    rw [e1] at this
    exact this
  have hFsz : F.code.size = (compileNode body here' st1).code.size := by
    rw [hFc]
    simp
  have hpre : ∀ pc, pc ≠ st.code.size →
      F.code[pc]! = (compileNode body here' st1).code[pc]! := by
    intro pc h
    rw [hFc, getBang_modify_ne _ _ h]
  have hcell : F.code[st.code.size]! =
      if greedy then
        (⟨.split, st.code.size + 1,
          (compileNode body here' st1).code.size⟩ : Inst)
      else
        ⟨.split, (compileNode body here' st1).code.size,
          st.code.size + 1⟩ := by
    rw [hFc, getBang_modify_eq _ _ (by omega),
      he.code_at st.code.size (by rw [e1]; omega), hc1, getBang_push_eq]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by rw [hFsz]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro pc hpc
      rw [hpre pc (by omega), he.code_at pc (by rw [e1]; omega), hc1,
        getBang_push_lt _ _ hpc]
    · rw [hFcl]
      have := he.cls_le
      rw [hcl1] at this
      exact this
    · intro i hi
      rw [hFcl, he.cls_at i (by rw [hcl1]; exact hi), hcl1]
    · rw [hFr]
      have := he.reps_le
      rw [hr1] at this
      exact this
    · intro i hi
      rw [hFr, he.reps_at i (by rw [hr1]; exact hi), hr1]
  · rw [hFcl]
    exact hdivB
  · rw [hFsz]
    refine Frag.repOpt hne ?_ ?_ ?_
    · rw [hcell]
      cases greedy <;> rfl
    · rw [hcell]
      cases greedy
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
    · have hbf := hfragB
      rw [e1, hr1] at hbf
      refine hbf.mono (fun pc h1 h2 => hpre pc (by omega))
        (Nat.le_of_eq (by rw [hFcl])) (fun i _ => by rw [hFcl])
        (Nat.le_of_eq (by rw [hFr])) (fun i _ _ => by rw [hFr])
/-- And for the counted repetition block: four fixed cells, the body in
the middle, and the repetition record finished with its exit. -/
private theorem rep_many_bundle {n : Nat} (ihn : NodeIH n) {body : Ast}
    (hszb : sizeOf body ≤ n) (hwb : NoEmptyAlt body) (rlo : Nat)
    (rhi : Option Nat) (greedy : Bool) (W : Nat)
    (h0 : rhi ≠ some 0) (h1 : rhi ≠ some 1)
    (st st4 F : CState) (here' : Nat) (hdiv : 32 ∣ st.classes.size)
    (hc4 : st4.code = ((st.code.push ⟨.repZero, st.reps.size, 0⟩).push
      ⟨.repLoop, st.reps.size, 0⟩).push ⟨.repEnter, st.reps.size, 0⟩)
    (hcl4 : st4.classes = st.classes)
    (hr4 : st4.reps = st.reps.push
      ⟨rlo, W, greedy, st.code.size + 1, st.code.size + 2, 0⟩)
    (hFc : F.code = (compileNode body here' st4).code.push
      ⟨.repNext, st.reps.size, 0⟩)
    (hFcl : F.classes = (compileNode body here' st4).classes)
    (hFr : F.reps = (compileNode body here' st4).reps.modify st.reps.size
      (fun rr => { rr with
        after := (compileNode body here' st4).code.size + 1 })) :
    Ext st F ∧ 32 ∣ F.classes.size ∧
      Frag F.code F.classes F.reps st.reps.size
        (.rep rlo rhi greedy body) st.code.size F.code.size := by
  obtain ⟨he, hdivB, hfragB⟩ := ihn hszb hwb here' st4 (by rw [hcl4]; exact hdiv)
  have e0 : st4.code.size = st.code.size + 3 := by
    rw [hc4]
    simp
  have er4 : st4.reps.size = st.reps.size + 1 := by
    rw [hr4]
    simp
  have hle : st.code.size + 3 ≤ (compileNode body here' st4).code.size := by
    have := he.code_le
    rw [e0] at this
    exact this
  have hFsz : F.code.size = (compileNode body here' st4).code.size + 1 := by
    rw [hFc]
    simp
  have hFrsz : F.reps.size = (compileNode body here' st4).reps.size := by
    rw [hFr]
    simp
  have hBr : st.reps.size < (compileNode body here' st4).reps.size := by
    have := he.reps_le
    rw [er4] at this
    omega
  have hST4at : ∀ pc, pc < st.code.size → st4.code[pc]! = st.code[pc]! := by
    intro pc h
    rw [hc4, getBang_push_lt _ _ (by simp <;> omega),
      getBang_push_lt _ _ (by simp <;> omega), getBang_push_lt _ _ h]
  have hcell0 : st4.code[st.code.size]! = ⟨.repZero, st.reps.size, 0⟩ := by
    rw [hc4, getBang_push_lt _ _ (by simp <;> omega),
      getBang_push_lt _ _ (by simp <;> omega), getBang_push_eq]
  have hcell1 : st4.code[st.code.size + 1]! =
      ⟨.repLoop, st.reps.size, 0⟩ := by
    rw [hc4, getBang_push_lt _ _ (by simp <;> omega),
      getBang_push_at _ _ (by simp)]
  have hcell2 : st4.code[st.code.size + 2]! =
      ⟨.repEnter, st.reps.size, 0⟩ := by
    rw [hc4, getBang_push_at _ _ (by simp)]
  have hentry : st4.reps[st.reps.size]! =
      ⟨rlo, W, greedy, st.code.size + 1, st.code.size + 2, 0⟩ := by
    rw [hr4, getBang_push_eq]
  have code_pres : ∀ pc, pc < (compileNode body here' st4).code.size →
      F.code[pc]! = (compileNode body here' st4).code[pc]! := by
    intro pc h
    rw [hFc, getBang_push_lt _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by rw [hFsz]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro pc hpc
      rw [code_pres pc (by omega), he.code_at pc (by rw [e0]; omega),
        hST4at pc hpc]
    · rw [hFcl]
      have := he.cls_le
      rw [hcl4] at this
      exact this
    · intro i hi
      rw [hFcl, he.cls_at i (by rw [hcl4]; exact hi), hcl4]
    · rw [hFrsz]
      have := he.reps_le
      rw [er4] at this
      omega
    · intro i hi
      rw [hFr, getBang_modify_ne _ _ (by omega : i ≠ st.reps.size),
        he.reps_at i (by rw [er4]; omega), hr4, getBang_push_lt _ _ hi]
  · rw [hFcl]
    exact hdivB
  · rw [hFsz]
    refine Frag.repMany (r := st.reps.size) (rhi32 := W)
      (m := (compileNode body here' st4).code.size) h0 h1 ?_ ?_ ?_ ?_ ?_
      (Nat.le_refl _) ?_ ?_
    · rw [code_pres _ (by omega), he.code_at _ (by rw [e0]; omega), hcell0]
      rfl
    · rw [code_pres _ (by omega), he.code_at _ (by rw [e0]; omega), hcell1]
    · rw [code_pres _ (by omega), he.code_at _ (by rw [e0]; omega), hcell2]
      rfl
    · have hbf := hfragB
      rw [e0, er4] at hbf
      refine (hbf.mono (fun pc h1 h2 => code_pres pc h2)
        (Nat.le_of_eq (by rw [hFcl])) (fun i _ => by rw [hFcl])
        (Nat.le_of_eq (by rw [hFrsz])) ?_).weaken (by omega)
      intro i hi0 hi
      rw [hFr, getBang_modify_ne _ _ (by omega : i ≠ st.reps.size)]
    · rw [hFc, getBang_push_eq]
    · rw [hFrsz]
      omega
    · rw [hFr, getBang_modify_eq _ _ hBr,
        he.reps_at st.reps.size (by rw [er4]; omega), hentry]

private theorem compileNode_facts : ∀ n : Nat, NodeIH n := by
  intro n
  induction n with
  | zero =>
      intro a hsz hw here st hdiv
      exfalso
      cases a <;> simp at hsz
  | succ n ihn =>
      intro a hsz hw here st hdiv
      cases a
      case nul =>
          rw [compileNode]
          exact ⟨Ext.refl st, hdiv, .empty (by simp [crWalk])⟩
      case chr b =>
          rw [compileNode]
          exact plain_emit_bundle st _ hdiv (.chr (getBang_push_eq st.code _))
      case chrCI b =>
          rw [compileNode]
          exact plain_emit_bundle st _ hdiv
            (.chrCI (getBang_push_eq st.code _))
      case cls bits =>
          have hstep : compileNode (Ast.cls bits) here st =
              (emit { st with classes := st.classes ++ bits.toArray }
                ⟨.cls, st.classes.size / 32, 0⟩).1 := by
            rw [compileNode]
          rw [hstep]
          have hsz32 : (st.classes ++ bits.toArray).size =
              st.classes.size + 32 := by
            simp
          have hidx : st.classes.size / 32 * 32 = st.classes.size :=
            Nat.div_mul_cancel hdiv
          refine ⟨?_, ?_, ?_⟩
          · refine Ext.trans
              (st₂ := { st with classes := st.classes ++ bits.toArray })
              ⟨Nat.le_refl _, fun _ _ => rfl, ?_,
                fun i hi => getBang_append_lt st.classes bits.toArray hi,
                Nat.le_refl _, fun _ _ => rfl⟩ (ext_emit _ _)
            rw [hsz32]
            omega
          · show 32 ∣ (st.classes ++ bits.toArray).size
            rw [hsz32]
            exact Nat.dvd_add hdiv (Nat.dvd_refl 32)
          · have hsz' : (emit { st with classes := st.classes ++ bits.toArray }
                ⟨.cls, st.classes.size / 32, 0⟩).1.code.size =
                st.code.size + 1 := by
              simp [emit]
            rw [hsz']
            refine Frag.cls (idx := st.classes.size / 32)
              (getBang_push_eq st.code _) ?_ ?_
            · show st.classes.size / 32 * 32 + 1 <
                (st.classes ++ bits.toArray).size
              rw [hidx, hsz32]
              omega
            · show (st.classes ++
                  bits.toArray)[st.classes.size / 32 * 32 + 1]! =
                bits.toArray[1]!
              rw [hidx]
              exact getBang_append_right st.classes bits.toArray (j := 1)
                (by simp)
      case any =>
          rw [compileNode]
          exact plain_emit_bundle st _ hdiv (.wild (by simp [crWalk])
            (.inl (by rw [getBang_push_eq])))
      case anyNoNL =>
          rw [compileNode]
          exact plain_emit_bundle st _ hdiv (.wild (by simp [crWalk])
            (.inr (.inl (by rw [getBang_push_eq]))))
      case bsr =>
          rw [compileNode]
          exact plain_emit_bundle st _ hdiv (.wild (by simp [crWalk])
            (.inr (.inr (by rw [getBang_push_eq]))))
      case cat kids =>
          cases kids with
          | nil =>
              have hstep : compileNode (.cat []) here st = st := by
                rw [compileNode, compileCat]
              rw [hstep]
              exact ⟨Ext.refl st, hdiv, .empty (by rw [crWalk_cat_nil])⟩
          | cons k rest =>
              have hunfold : compileNode (Ast.cat rest) here
                  (compileNode k here st) =
                  compileCat rest here (compileNode k here st) := by
                rw [compileNode]
              have hstep : compileNode (.cat (k :: rest)) here st =
                  compileNode (.cat rest) here (compileNode k here st) := by
                rw [compileNode, compileCat, hunfold]
              have hszk : sizeOf k ≤ n ∧ sizeOf (Ast.cat rest) ≤ n := by
                simp at hsz ⊢
                omega
              have hw' : ∀ x ∈ k :: rest, NoEmptyAlt x := by
                have := hw
                simp only [NoEmptyAlt] at this
                exact this
              have hwrest : NoEmptyAlt (.cat rest) := by
                simp only [NoEmptyAlt]
                exact fun x hx => hw' x (List.mem_cons_of_mem _ hx)
              obtain ⟨he₁, hdiv₁, hfrag₁⟩ :=
                ihn hszk.1 (hw' k (List.mem_cons_self ..)) here st hdiv
              obtain ⟨he₂, hdiv₂, hfrag₂⟩ :=
                ihn hszk.2 hwrest here (compileNode k here st) hdiv₁
              rw [hstep]
              refine ⟨he₁.trans he₂, hdiv₂, ?_⟩
              refine .catCons (hfrag₁.ext (Nat.le_refl _) he₂) ?_
              exact hfrag₂.weaken he₁.reps_le
      case alt arms =>
          have hw' := hw
          simp only [NoEmptyAlt] at hw'
          obtain ⟨hne, hmem⟩ := hw'
          cases arms with
          | nil => exact absurd rfl hne
          | cons first rest =>
            cases rest with
            | nil =>
                have hstep : compileNode (.alt [first]) here st =
                    compileNode first here st := by
                  rw [compileNode]
                have hszf : sizeOf first ≤ n := by
                  simp at hsz
                  omega
                obtain ⟨he, hdiv', hfrag⟩ :=
                  ihn hszf (hmem first (List.mem_cons_self ..)) here st hdiv
                rw [hstep]
                exact ⟨he, hdiv', .altOne hfrag⟩
            | cons second rest' =>
                have hstep :
                    compileNode (.alt (first :: second :: rest')) here st =
                    closeRegion
                      (compileAlt first (second :: rest')
                        (openRegion st .alt here).2 #[]
                        (openRegion st .alt here).1)
                      (openRegion st .alt here).2 := by
                  rw [compileNode]
                  all_goals first
                    | rfl
                    | simp
                have hL : sizeOf (Ast.alt (first :: second :: rest')) =
                    1 + sizeOf (first :: second :: rest') := by
                  simp
                have hszf : sizeOf first ≤ n := by
                  have h1 := List.sizeOf_lt_of_mem
                    (List.mem_cons_self (a := first) (l := second :: rest'))
                  omega
                have helems : ∀ x ∈ second :: rest',
                    sizeOf x ≤ n ∧ NoEmptyAlt x := by
                  intro x hx
                  have h1 := List.sizeOf_lt_of_mem
                    (List.mem_cons_of_mem first hx)
                  exact ⟨by omega, hmem x (List.mem_cons_of_mem _ hx)⟩
                obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
                  compileAlt_facts ihn (second :: rest') first hszf
                    (hmem first (List.mem_cons_self ..)) helems
                    (openRegion st .alt here).2 #[]
                    (openRegion st .alt here).1 hdiv
                    (by intro p hp; simp at hp)
                rw [hstep]
                refine ⟨⟨c1, ?_, c4, c5, c7, c8⟩, c6, c9⟩
                intro pc hpc
                exact c2 pc hpc (by simp)
      case grp cap body =>
          have hwb : NoEmptyAlt body := by
            have := hw
            simp only [NoEmptyAlt] at this
            exact this
          have hszb : sizeOf body ≤ n := by
            simp at hsz
            omega
          by_cases hc : (cap != 0) = true
          · exact grp_saves_bundle ihn hszb hwb cap st
              (emit (openRegion st .group here).1 ⟨.save, 2 * cap, 0⟩).1
              (compileNode (.grp cap body) here st)
              (openRegion st .group here).2 hdiv rfl rfl rfl
              (by rw [compileNode]
                  simp only [openRegion]
                  rw [if_pos hc, if_pos hc, (dropEmptyRegion_code _ _).1]
                  rfl)
              (by rw [compileNode]
                  simp only [openRegion]
                  rw [if_pos hc, if_pos hc, (dropEmptyRegion_code _ _).2.1]
                  rfl)
              (by rw [compileNode]
                  simp only [openRegion]
                  rw [if_pos hc, if_pos hc, (dropEmptyRegion_code _ _).2.2]
                  rfl)
          · have hstep : compileNode (.grp cap body) here st =
                dropEmptyRegion
                  (closeRegion
                    (compileNode body (openRegion st .group here).2
                      (openRegion st .group here).1)
                    (openRegion st .group here).2)
                  (openRegion st .group here).2 := by
              rw [compileNode]
              simp only [openRegion]
              rw [if_neg hc, if_neg hc]
            obtain ⟨he, hdivB, hfragB⟩ :=
              ihn hszb hwb (openRegion st .group here).2
                (openRegion st .group here).1 hdiv
            rw [hstep]
            have hEc := (dropEmptyRegion_code
              (closeRegion
                (compileNode body (openRegion st .group here).2
                  (openRegion st .group here).1)
                (openRegion st .group here).2)
              (openRegion st .group here).2).1
            have hEcl : (dropEmptyRegion
                (closeRegion
                  (compileNode body (openRegion st .group here).2
                    (openRegion st .group here).1)
                  (openRegion st .group here).2)
                (openRegion st .group here).2).classes =
                (compileNode body (openRegion st .group here).2
                  (openRegion st .group here).1).classes :=
              (dropEmptyRegion_code _ _).2.1
            have hEr : (dropEmptyRegion
                (closeRegion
                  (compileNode body (openRegion st .group here).2
                    (openRegion st .group here).1)
                  (openRegion st .group here).2)
                (openRegion st .group here).2).reps =
                (compileNode body (openRegion st .group here).2
                  (openRegion st .group here).1).reps :=
              (dropEmptyRegion_code _ _).2.2
            refine ⟨?_, ?_, ?_⟩
            · exact (ext_openRegion st .group here).trans
                (he.trans ((ext_closeRegion _ _).trans
                  (ext_dropEmptyRegion _ _)))
            · rw [hEcl]
              exact hdivB
            · have hEsz : (dropEmptyRegion
                  (closeRegion
                    (compileNode body (openRegion st .group here).2
                      (openRegion st .group here).1)
                    (openRegion st .group here).2)
                  (openRegion st .group here).2).code.size =
                  (compileNode body (openRegion st .group here).2
                    (openRegion st .group here).1).code.size := by
                rw [hEc]
                rfl
              rw [hEsz]
              refine Frag.grpBody (hfragB.mono ?_
                (Nat.le_of_eq (by rw [hEcl])) (fun i _ => by rw [hEcl])
                (Nat.le_of_eq (by rw [hEr])) (fun i _ _ => by rw [hEr]))
              intro pc hp1 hp2
              rw [hEc]
              rfl
      case rep rlo rhi greedy body =>
          have hwb : NoEmptyAlt body := by
            have := hw
            simp only [NoEmptyAlt] at this
            exact this
          have hszb : sizeOf body ≤ n := by
            simp at hsz
            omega
          rcases rhi with _ | k
          · exact rep_many_bundle ihn hszb hwb rlo none greedy none32
              nofun nofun st
              { (emit
                  (emit
                    (emit (openRegion st .«repeat» here).1
                      ⟨.repZero, st.reps.size, 0⟩).1
                    ⟨.repLoop, st.reps.size, 0⟩).1
                  ⟨.repEnter, st.reps.size, 0⟩).1 with
                reps := st.reps.push
                  ⟨rlo, none32, greedy,
                    (emit (openRegion st .«repeat» here).1
                      ⟨.repZero, st.reps.size, 0⟩).1.code.size,
                    (emit (openRegion st .«repeat» here).1
                      ⟨.repZero, st.reps.size, 0⟩).1.code.size + 1, 0⟩ }
              (compileNode (.rep rlo none greedy body) here st)
              (openRegion st .«repeat» here).2 hdiv
              (by simp [emit, openRegion]) rfl
              (by simp [emit, openRegion])
              (by rw [compileNode]; rfl)
              (by rw [compileNode]; rfl)
              (by rw [compileNode]
                  simp [emit, openRegion, closeRegion])
          · rcases k with _ | k1
            · have hstep :
                  compileNode (.rep rlo (some 0) greedy body) here st =
                  st := by
                rw [compileNode]
              rw [hstep]
              exact ⟨Ext.refl st, hdiv, .empty (crWalk_rep_zero ..)⟩
            · rcases k1 with _ | k2
              · by_cases hl1 : (rlo == 1) = true
                · obtain rfl : rlo = 1 := by simpa using hl1
                  have hstep :
                      compileNode (.rep 1 (some 1) greedy body) here st =
                      compileNode body here st := by
                    rw [compileNode]
                    rfl
                  obtain ⟨he, hdiv', hfrag⟩ := ihn hszb hwb here st hdiv
                  rw [hstep]
                  exact ⟨he, hdiv', .repOne hfrag⟩
                · have hne : (rlo == 1) = false := by
                    simpa using hl1
                  exact rep_opt_bundle ihn hszb hwb rlo greedy hne st
                    (emit (openRegion st .«repeat» here).1 ⟨.split, 0, 0⟩).1
                    (compileNode (.rep rlo (some 1) greedy body) here st)
                    (openRegion st .«repeat» here).2 hdiv rfl rfl rfl
                    (by rw [compileNode, if_neg hl1]; rfl)
                    (by rw [compileNode, if_neg hl1]; rfl)
                    (by rw [compileNode, if_neg hl1]; rfl)
              · exact rep_many_bundle ihn hszb hwb rlo (some (k2 + 2)) greedy
                  (k2 + 2) (by simp) (by simp) st
                  { (emit
                      (emit
                        (emit (openRegion st .«repeat» here).1
                          ⟨.repZero, st.reps.size, 0⟩).1
                        ⟨.repLoop, st.reps.size, 0⟩).1
                      ⟨.repEnter, st.reps.size, 0⟩).1 with
                    reps := st.reps.push
                      ⟨rlo, k2 + 2, greedy,
                        (emit (openRegion st .«repeat» here).1
                          ⟨.repZero, st.reps.size, 0⟩).1.code.size,
                        (emit (openRegion st .«repeat» here).1
                          ⟨.repZero, st.reps.size, 0⟩).1.code.size + 1, 0⟩ }
                  (compileNode (.rep rlo (some (k2 + 2)) greedy body) here st)
                  (openRegion st .«repeat» here).2 hdiv
                  (by simp [emit, openRegion]) rfl
                  (by simp [emit, openRegion])
                  (by rw [compileNode] <;> first | rfl | simp)
                  (by rw [compileNode] <;> first | rfl | simp)
                  (by rw [compileNode] <;>
                    simp [emit, openRegion, closeRegion])
      all_goals
        rw [compileNode]
        exact plain_emit_bundle st _ hdiv (.asrt (by simp [crWalk])
          (by rw [getBang_push_eq]; rfl))

/-! ## The top of the program

The compiled pattern is the root fragment followed by the optional `eod`
and the final `accept`. From the fragment's entry at pc 0, the scan can
reach a CR-capable consuming head exactly when `crWalk` says the first
byte can be CR, and it can reach the tail — whose `accept` answers yes —
exactly when the walk calls the whole tree transparent. That is
`p.crFirst` on the nose. -/

private theorem top_iff {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {a : Ast} {n : Nat}
    (hfrag : Frag code classes reps 0 a 0 n)
    (hn : n < code.size)
    (htail : ∀ x, n ≤ x → x < code.size →
      ∀ y ∈ succs code reps x, n ≤ y ∧ y < code.size)
    (hacc : ∃ pcA, pcA < code.size ∧ Reach code reps n pcA ∧
      crHead code classes pcA = true) :
    scanFirst code classes reps = true ↔
      ((crWalk a).1 || (crWalk a).2) = true := by
  obtain ⟨S, hS0, hSbd, hScl, hScr, hShi⟩ := hfrag.closed
  obtain ⟨hcr, htr⟩ := hfrag.reach hn
  rw [scanFirst_iff]
  constructor
  · rintro ⟨pc, hlt, hreach, hhead⟩
    have hclosed : ∀ x, (S x ∨ ((crWalk a).2 = true ∧ n ≤ x ∧ x < code.size)) →
        ∀ y, Step code reps x y →
          (S y ∨ ((crWalk a).2 = true ∧ n ≤ y ∧ y < code.size)) := by
      rintro x (hx | ⟨htrx, hx1, hx2⟩) y ⟨hs1, hs2, hs3⟩
      · by_cases hxn : x = n
        · subst hxn
          have htrx := hShi.mp hx
          exact .inr ⟨htrx, (htail x (Nat.le_refl _) hs1 y hs3).1, hs2⟩
        · exact .inl (hScl x hx hxn y hs3)
      · exact .inr ⟨htrx, (htail x hx1 hx2 y hs3).1, hs2⟩
    have hmem := Reach.mem_closed hclosed (.inl hS0) hreach
    rw [Bool.or_eq_true]
    rcases hmem with hmem | ⟨htrx, _, _⟩
    · by_cases hpn : pc = n
      · subst hpn
        exact .inr (hShi.mp hmem)
      · exact .inl (hScr pc hmem hpn hhead)
    · exact .inr htrx
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨pc, hlt, hreach, hhead⟩ := hcr h
      exact ⟨pc, hlt, hreach, hhead⟩
    · obtain ⟨pcA, hAlt, hAreach, hAhead⟩ := hacc
      exact ⟨pcA, hAlt, (htr h).trans hAreach, hAhead⟩

/-- The bumpalong bit agrees between the two layers: `scanFirst` on the
compiled program computes exactly what `crWalk` computes on the tree,
for every pattern without an `.alt []` subterm. `skipsAttempt` therefore
skips the same positions whether the spec or the engine decides. -/
theorem crFirst_agrees (p : Pat) (hw : NoEmptyAlt p.root) :
    (Ref.compile p).crfirst = p.crFirst := by
  obtain ⟨heB, hdivB, hfragB⟩ :=
    compileNode_facts (sizeOf p.root) (Nat.le_refl _) hw
      (openRegion {} .root none32).2 (openRegion {} .root none32).1
      ⟨0, rfl⟩
  have hfrag : Frag
      (compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code
      (compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).classes
      (compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).reps
      0 p.root 0
      (compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.size := hfragB
  have hcf : p.crFirst = ((crWalk p.root).1 || (crWalk p.root).2) := by
    unfold Pat.crFirst
    rcases crWalk p.root with ⟨cr, tr⟩
    rfl
  by_cases hea : p.opts.endanchored
  · have h1 : (Ref.compile p).crfirst = scanFirst
        (((compileNode p.root (openRegion {} .root none32).2
            (openRegion {} .root none32).1).code.push
          ⟨.eod, 0, 0⟩).push ⟨.accept, 0, 0⟩)
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).classes
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).reps := by
      unfold Ref.compile
      simp only [openRegion]
      rw [if_pos hea]
      rfl
    rw [h1, hcf]
    have hszF : (((compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.push
        ⟨.eod, 0, 0⟩).push ⟨.accept, 0, 0⟩).size =
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size + 2 := by
      simp
    have hpre : ∀ pc, pc < (compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.size →
        (((compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.push
          ⟨.eod, 0, 0⟩).push ⟨.accept, 0, 0⟩)[pc]! =
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code[pc]! := by
      intro pc h
      rw [getBang_push_lt _ _ (by simp; omega), getBang_push_lt _ _ h]
    have hcelln : (((compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.push
        ⟨.eod, 0, 0⟩).push ⟨.accept, 0, 0⟩)[(compileNode p.root
          (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size]! =
        ⟨.eod, 0, 0⟩ := by
      rw [getBang_push_lt _ _ (by simp), getBang_push_eq]
    have hcellA : (((compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.push
        ⟨.eod, 0, 0⟩).push ⟨.accept, 0, 0⟩)[(compileNode p.root
          (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size + 1]! =
        ⟨.accept, 0, 0⟩ := by
      rw [getBang_push_at _ _ (by simp)]
    refine Bool.eq_iff_iff.mpr (top_iff
      (hfrag.mono (fun pc h1' h2' => (hpre pc h2').symm ▸ rfl) (Nat.le_refl _)
        (fun i _ => rfl) (Nat.le_refl _) (fun i _ _ => rfl))
      (by rw [hszF]; omega) ?_ ?_)
    · intro x hx1 hx2 y hy
      rw [hszF] at hx2
      rcases Nat.lt_or_ge x ((compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size + 1) with hx | hx
      · have hxn : x = (compileNode p.root (openRegion {} .root none32).2
            (openRegion {} .root none32).1).code.size := by omega
        subst hxn
        rw [succs_plain (by rw [hcelln]; rfl)] at hy
        rcases List.mem_singleton.mp hy with rfl
        constructor
        · omega
        · rw [hszF]
          omega
      · have hxn : x = (compileNode p.root (openRegion {} .root none32).2
            (openRegion {} .root none32).1).code.size + 1 := by omega
        subst hxn
        simp only [succs, hcellA, List.not_mem_nil] at hy
    · refine ⟨(compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size + 1,
        by rw [hszF]; omega, ?_, ?_⟩
      · refine Reach.single ⟨?_, ?_, ?_⟩
        · rw [hszF]
          omega
        · rw [hszF]
          omega
        · rw [succs_plain (by rw [hcelln]; rfl)]
          exact List.mem_singleton.mpr rfl
      · simp only [crHead, hcellA]
  · have h1 : (Ref.compile p).crfirst = scanFirst
        ((compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.push ⟨.accept, 0, 0⟩)
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).classes
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).reps := by
      unfold Ref.compile
      simp only [openRegion]
      rw [if_neg hea]
      rfl
    rw [h1, hcf]
    have hszF : ((compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.push ⟨.accept, 0, 0⟩).size =
        (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size + 1 := by
      simp
    have hcellA : ((compileNode p.root (openRegion {} .root none32).2
        (openRegion {} .root none32).1).code.push
        ⟨.accept, 0, 0⟩)[(compileNode p.root
          (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size]! =
        ⟨.accept, 0, 0⟩ := by
      rw [getBang_push_eq]
    refine Bool.eq_iff_iff.mpr (top_iff
      (hfrag.mono (fun pc h1' h2' => getBang_push_lt _ _ h2') (Nat.le_refl _)
        (fun i _ => rfl) (Nat.le_refl _) (fun i _ _ => rfl))
      (by rw [hszF]; omega) ?_ ?_)
    · intro x hx1 hx2 y hy
      rw [hszF] at hx2
      have hxn : x = (compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size := by omega
      subst hxn
      simp only [succs, hcellA, List.not_mem_nil] at hy
    · exact ⟨(compileNode p.root (openRegion {} .root none32).2
          (openRegion {} .root none32).1).code.size,
        by rw [hszF]; omega, .refl _, by simp only [crHead, hcellA]⟩

end Pcrevera.CrFirst
