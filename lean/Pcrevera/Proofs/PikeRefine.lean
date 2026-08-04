import Pcrevera.Proofs.Refine
import Pcrevera.Proofs.Agreement

/-!
# Towards S-8, the lockstep half

The claim being built towards is the twin of `btRun_refines_matches`: on a
Pike-eligible program, whenever `pikeRun` reports matched or no-match its
answer is `Spec.Matches`, and the two layers call an input bad on the same
offsets — plus the refusal the lockstep matcher owns alone, an ineligible
program. `PikeRunRefinesMatches` at the end of the file states that target;
this file does not yet prove it. What is here is the foundation: what
eligibility buys, and the guards.

* **The flags, read back.** `pikeOk` is a conjunction over the repetition
  table and a sweep for `\R`; `pikeOk_rep` and `pikeOk_no_bsr` turn it
  back into the two facts the argument uses.

* **The shape behind the program.** `PikeShape` says the same thing about
  the AST the program was compiled from: no `\R`, and every repetition
  that reached the general block is a pure star. `FragAt.pikeShape` reads
  it off the fragment relation of `Refine.lean` — the repetition row a
  `repGen` fragment pins is the row eligibility inspected — and
  `compile_pikeShape` states it for a whole compiled pattern.

* **What `pike_hollow` decides.** The engine's worklist walks the
  non-consuming transitions out of a star's body and asks whether the
  star's own `repNext` is reachable. `pikeHollow_certificate` says a
  `false` verdict really is that absence: it exhibits a set of program
  counters closed under the non-consuming step, containing the body's
  entry and avoiding the goal, and `pikeHollow_no_path` reads the absence
  off it.

* **The loop that cannot close.** The closure walks a relation of its own,
  `epsTargets`, which differs from the walk's in one place: at a `repNext`
  it jumps straight at the body where the walk goes through the deciding
  head. `FragAt.rows` says the repetition table really describes the
  blocks it was emitted for, and with that the two relations reach the
  same places (`hollowReach_of_epsReach`). `pikeOk_no_eps_loop` states the
  acyclicity the visited set rests on: on an eligible program a star's
  loop-back edge can never be re-armed without consuming a byte, so no
  closure goes round the loop twice and depth-first in split order really
  is the backtracking preference order.

* **The empty iteration, ruled out.** `frag_empty_reach` says a construct
  that matched without moving spells a non-consuming path from its
  fragment's entry to its exit, one epsilon step per instruction the
  machine would have walked through. `frag_rep_body_consumes` reads the
  consequence: on an eligible program a star's body cannot match empty,
  because the path that would witness it is the one `pike_ok` refused. So
  the empty-match rule the backtracking matcher runs at `repNext` never
  fires here, and the lockstep matcher's want of one costs it nothing.

* **What a closure build marks.** `pikeAdd_go_marks` reads `pike_add`
  against `epsTargets`: the loop pops one thread at a time and replaces a
  fresh pc by the continuations its instruction defers to, so the
  reachability of the pcs on the stack is an invariant and the marks a
  build leaves are covered by it. `pikeAdd_no_reentry` is the matcher-level
  form of the acyclicity: a build seeded at a star's body entry never marks
  that star's `repNext`, so within one position the loop-back edge is taken
  at most once.

* **The guards.** `pikeRun_badInput` locates the two refusals in the call
  itself, and `pikeRun_badInput_agrees` matches them against the
  specification's own BadInput under the documented subject cap. That is
  S-8's third clause for this matcher, proved.
-/

namespace Pcrevera.Refine

open Pcrevera Pcrevera.Ref

/-! ## The eligibility flags, read back

`pike_ok` is two sweeps: one over the repetition table, refusing anything
that is not a pure star or whose body can complete an iteration emptily,
and one over the code, refusing `\R`. Both come back out as ordinary
facts about an index. -/

/-- Every repetition row of an eligible program is a pure star whose body
cannot finish an iteration without consuming. -/
theorem pikeOk_rep {code : Array Inst} {reps : Array RepInfo}
    (h : pikeOk code reps = true) {i : Nat} (hi : i < reps.size) :
    (reps[i]!).lo = 0 ∧ (reps[i]!).hi = none32 ∧
      pikeHollow code reps i = false := by
  rw [pikeOk, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1 i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hall
  exact ⟨hall.1.1, hall.1.2, hall.2⟩

/-- An eligible program spells no `\R`: nothing in it consumes a variable
number of bytes. -/
theorem pikeOk_no_bsr {code : Array Inst} {reps : Array RepInfo}
    (h : pikeOk code reps = true) {pc : Nat} (hpc : pc < code.size) :
    (code[pc]!).op ≠ .bsr := by
  rw [pikeOk, Bool.and_eq_true] at h
  have hall := Array.all_eq_true.mp h.2 pc hpc
  rw [getElem!_pos code pc hpc]
  simpa using hall

/-! ## The shape behind an eligible program

Eligibility is decided on the bytecode, but the refinement argument runs
over the AST, so the verdict has to travel back across the compiler. The
fragment relation of `Refine.lean` is the bridge: a `repGen` fragment
names the repetition row its block runs on, and that is the row `pike_ok`
inspected. -/

/-- What `pike_ok` says about the tree the program came from: no `\R`, and
every repetition that reached the general block is a pure star.

The three split-compiled forms claim no repetition row — `{0,0}` compiles
to nothing at all, `{1,1}` to its body, and the optional item to a single
split — so eligibility has nothing to say about their bounds, and neither
has this. `{0,0}` does not even compile its body, so nothing is said about
that either. -/
def PikeShape : Ast → Prop
  | .bsr => False
  | .cat kids => kids.attach.foldr (fun ⟨k, _⟩ acc => PikeShape k ∧ acc) True
  | .alt arms => arms.attach.foldr (fun ⟨a, _⟩ acc => PikeShape a ∧ acc) True
  | .grp _ body => PikeShape body
  | .rep lo hi _ body =>
      match hi with
      | some 0 => True
      | some 1 => PikeShape body
      | _ => lo = 0 ∧ hi = none ∧ PikeShape body
  | _ => True

theorem pikeShape_cat_nil : PikeShape (.cat []) := by rw [PikeShape]; simp

theorem pikeShape_alt_nil : PikeShape (.alt []) := by rw [PikeShape]; simp

/-- A concatenation's shape, one child at a time. -/
theorem pikeShape_cat_cons {k : Ast} {kids : List Ast} :
    PikeShape (.cat (k :: kids)) ↔ PikeShape k ∧ PikeShape (.cat kids) := by
  rw [PikeShape, PikeShape]
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map]

/-- An alternation's shape, one arm at a time. -/
theorem pikeShape_alt_cons {a : Ast} {arms : List Ast} :
    PikeShape (.alt (a :: arms)) ↔ PikeShape a ∧ PikeShape (.alt arms) := by
  rw [PikeShape, PikeShape]
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map]

/-- A cell that reads as an instruction the default is not sits inside the
program. `getElem!` hands back `Inhabited`'s `chr` past the end, so any
fragment that pinned another opcode pinned a real address. -/
theorem lt_size_of_cell {code : Array Inst} {pc : Nat} {i : Inst}
    (hcell : code[pc]! = i) (hne : i ≠ ⟨.chr, 0, 0⟩) : pc < code.size := by
  rcases Nat.lt_or_ge pc code.size with hlt | hge
  · exact hlt
  · rw [getElem!_neg code pc (by omega)] at hcell
    exact absurd hcell.symm hne

/-- Reading eligibility back onto the tree. Every clause is a fragment
case: the `\R` leaf pinned a `bsr` cell, which the code sweep forbids, and
the general repetition pinned the row whose bounds the table sweep read —
with the compiler's `none32` spelling of an unbounded high turned back
into `none` by the parser's cap on quantifier bounds. -/
theorem FragAt.pikeShape {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (hok : pikeOk code reps = true)
    (h : FragAt code classes reps r0 a lo hi) : PikeShape a := by
  induction h with
  | nul | chr _ | chrCI _ | cls _ _ _ | any _ | anyNoNL _ =>
      rw [PikeShape] <;> simp
  | @bsr _ pc hcell =>
      exact absurd (congrArg Inst.op hcell)
        (pikeOk_no_bsr hok (lt_size_of_cell hcell (by decide)))
  | @assn a' op _ _ ha _ =>
      cases a' <;> simp only [assnOp] at ha <;> try cases ha
      all_goals (rw [PikeShape] <;> simp)
  | catNil => exact pikeShape_cat_nil
  | catCons _ _ ihk ihkids => exact pikeShape_cat_cons.mpr ⟨ihk, ihkids⟩
  | altOne _ iha => exact pikeShape_alt_cons.mpr ⟨iha, pikeShape_alt_nil⟩
  | altCons _ _ _ _ iha ihrest => exact pikeShape_alt_cons.mpr ⟨iha, ihrest⟩
  | grpZero _ ihbody => rw [PikeShape]; exact ihbody
  | grpCap _ _ _ _ ihbody => rw [PikeShape]; exact ihbody
  | repNone => rw [PikeShape]; trivial
  | repOne _ ihbody => rw [PikeShape]; exact ihbody
  | repOpt _ _ _ ihbody => rw [PikeShape]; exact ihbody
  | @repGen lo' hi' greedy body r0 pc j _ _ _ _ hrow hinfo
      hbound _ _ _ ihbody =>
      obtain ⟨hlo, hhi, _⟩ := pikeOk_rep hok hrow
      rw [hinfo] at hlo hhi
      have hlo' : lo' = 0 := hlo
      have hhi' : hiCode hi' = none32 := hhi
      have hnone : hi' = none := by
        cases hi' with
        | none => rfl
        | some v =>
            rw [hiCode] at hhi'
            exact absurd (hbound v rfl) (by omega)
      subst hnone
      rw [PikeShape]
      all_goals first | exact ⟨hlo', rfl, ihbody⟩ | simp

/-- The whole compiled pattern: a well-shaped tree whose program the
lockstep matcher accepted is a tree of pure stars without `\R`. -/
theorem compile_pikeShape {p : Pat} (hc : Covered p.root)
    (hok : (compile p).pike = true) : PikeShape p.root :=
  (compile_shape hc).1.pikeShape hok

/-! ## What `pike_hollow` decides

The engine's second eligibility test walks the non-consuming transitions
out of a star's body and asks whether the star's own `repNext` is
reachable. A `yes` costs the pattern nothing but its Pike routing, so the
walk answers `yes` on anything it does not understand; what the proof
needs is the other direction, and that is what this section extracts.

Rather than reason about the worklist's schedule, the lemma hands back a
*certificate*: a set of program counters closed under the non-consuming
step, containing the body's entry and containing no goal. The final
visited set is that certificate — the loop only ever stops with an empty
worklist, and the invariant below says a marked pc has all its successors
marked or still pending. -/

/-- The non-consuming step the walk follows. `RepLoop` and `RepNext` are
read as the forks their control flow amounts to; a consuming instruction
and `Accept` are dead ends; everything else falls through to the next
cell. -/
def hollowTargets (code : Array Inst) (reps : Array RepInfo) (pc : Nat) :
    List Nat :=
  match (code[pc]!).op with
  | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .accept => []
  | .split => [(code[pc]!).alt, (code[pc]!).arg]
  | .jump => [(code[pc]!).arg]
  | .repLoop =>
      [(reps[(code[pc]!).arg]!).after, (reps[(code[pc]!).arg]!).body]
  | .repNext =>
      [(reps[(code[pc]!).arg]!).after, (reps[(code[pc]!).arg]!).head]
  | _ => [pc + 1]

/-- Where a non-consuming walk from `pc` can end up. -/
inductive HollowReach (code : Array Inst) (reps : Array RepInfo) :
    Nat → Nat → Prop where
  | refl {pc : Nat} : HollowReach code reps pc pc
  | step {pc mid q : Nat} (hmid : mid ∈ hollowTargets code reps pc)
      (hrest : HollowReach code reps mid q) : HollowReach code reps pc q

/-- The certificate: a set of real instructions, none of them the goal,
that the non-consuming step cannot leave. -/
structure HollowSafe (code : Array Inst) (reps : Array RepInfo) (goal : Nat)
    (S : Nat → Prop) : Prop where
  bounded : ∀ pc, S pc → pc < code.size
  avoids : ∀ pc, S pc → pc ≠ goal
  closed : ∀ pc, S pc → ∀ t ∈ hollowTargets code reps pc, S t

theorem HollowSafe.reach {code : Array Inst} {reps : Array RepInfo}
    {goal : Nat} {S : Nat → Prop} (h : HollowSafe code reps goal S) :
    ∀ {pc q : Nat}, HollowReach code reps pc q → S pc → S q := by
  intro pc q hr
  induction hr with
  | refl => exact id
  | step hmid _ ih => exact fun hpc => ih (h.closed _ hpc _ hmid)

private theorem getBang_set_self {α : Type _} [Inhabited α] (u : Array α)
    {i : Nat} (h : i < u.size) {x : α} : (u.set! i x)[i]! = x := by
  rw [Array.set!_eq_setIfInBounds,
    getElem!_pos (u.setIfInBounds i x) i (by simpa using h)]
  exact Array.getElem_setIfInBounds_self (by simpa using h)

private theorem getBang_set_other {α : Type _} [Inhabited α] (u : Array α)
    (i : Nat) {x : α} {j : Nat} (h : j ≠ i) : (u.set! i x)[j]! = u[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < u.size
  · rw [getElem!_pos (u.setIfInBounds i x) j (by simpa using hj),
      getElem!_pos u j hj]
    exact Array.getElem_setIfInBounds_ne hj (Ne.symm h)
  · rw [getElem!_neg (u.setIfInBounds i x) j (by simpa using hj),
      getElem!_neg u j hj]

/-- One iteration that finds a fresh, in-range, non-goal pc: it marks the
pc and hands the worklist that pc's non-consuming successors. -/
theorem pikeHollow_go_step (code : Array Inst) (reps : Array RepInfo)
    (which fuel pc : Nat) (seen : Array Bool) (rest : List Nat)
    (hlt : pc < code.size) (hgoal : ¬ pc = (reps[which]!).after - 1)
    (hseen : seen[pc]! = false) :
    pikeHollow.go code reps which (fuel + 1) seen (pc :: rest) =
      pikeHollow.go code reps which fuel (seen.set! pc true)
        (hollowTargets code reps pc ++ rest) := by
  rw [pikeHollow.go]
  rw [if_neg (by omega), if_neg (by simpa using hgoal), if_neg (by simp [hseen])]
  simp only [hollowTargets]
  split <;> rename_i heq <;> simp only [heq] <;> rfl

/-- And one that finds a pc already marked: it drops the entry and walks
on. -/
theorem pikeHollow_go_skip (code : Array Inst) (reps : Array RepInfo)
    (which fuel pc : Nat) (seen : Array Bool) (rest : List Nat)
    (hlt : pc < code.size) (hgoal : ¬ pc = (reps[which]!).after - 1)
    (hseen : seen[pc]! = true) :
    pikeHollow.go code reps which (fuel + 1) seen (pc :: rest) =
      pikeHollow.go code reps which fuel seen rest := by
  rw [pikeHollow.go]
  rw [if_neg (by omega), if_neg (by simpa using hgoal), if_pos hseen]

/-- The worklist's soundness, as an invariant. A run that ends `false`
exhibits a closed set: everything already marked has its successors
marked or still pending, so an empty worklist leaves the marked set
closed. -/
theorem pikeHollow_go_safe (code : Array Inst) (reps : Array RepInfo)
    (which : Nat) :
    ∀ (fuel : Nat) (seen : Array Bool) (pending : List Nat),
      seen.size = code.size →
      pikeHollow.go code reps which fuel seen pending = false →
      (∀ pc, seen[pc]! = true →
        pc < code.size ∧ pc ≠ (reps[which]!).after - 1 ∧
          ∀ t ∈ hollowTargets code reps pc,
            seen[t]! = true ∨ t ∈ pending) →
      ∃ S, HollowSafe code reps ((reps[which]!).after - 1) S ∧
        (∀ pc, seen[pc]! = true → S pc) ∧ (∀ pc ∈ pending, S pc) := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen pending hsz hrun hinv
      cases pending with
      | cons pc rest => rw [pikeHollow.go] at hrun; simp at hrun
      | nil =>
          refine ⟨fun q => seen[q]! = true, ⟨?_, ?_, ?_⟩, fun _ h => h,
            by simp⟩
          · exact fun q hq => (hinv q hq).1
          · exact fun q hq => (hinv q hq).2.1
          · exact fun q hq t ht =>
              ((hinv q hq).2.2 t ht).resolve_right (by simp)
  | succ fuel ih =>
      intro seen pending hsz hrun hinv
      cases pending with
      | nil =>
          refine ⟨fun q => seen[q]! = true, ⟨?_, ?_, ?_⟩, fun _ h => h,
            by simp⟩
          · exact fun q hq => (hinv q hq).1
          · exact fun q hq => (hinv q hq).2.1
          · exact fun q hq t ht =>
              ((hinv q hq).2.2 t ht).resolve_right (by simp)
      | cons pc rest =>
          have hlt : pc < code.size := by
            rcases Nat.lt_or_ge pc code.size with h | h
            · exact h
            · rw [pikeHollow.go, if_pos h] at hrun
              exact absurd hrun (by simp)
          have hgoal : ¬ pc = (reps[which]!).after - 1 := by
            intro h
            rw [pikeHollow.go, if_neg (by omega),
              if_pos (by simpa using h)] at hrun
            exact absurd hrun (by simp)
          by_cases hs : seen[pc]! = true
          · rw [pikeHollow_go_skip code reps which fuel pc seen rest hlt hgoal
              hs] at hrun
            have hinv' : ∀ q, seen[q]! = true →
                q < code.size ∧ q ≠ (reps[which]!).after - 1 ∧
                  ∀ t ∈ hollowTargets code reps q,
                    seen[t]! = true ∨ t ∈ rest := by
              intro q hq
              refine ⟨(hinv q hq).1, (hinv q hq).2.1, fun t ht => ?_⟩
              rcases (hinv q hq).2.2 t ht with h | h
              · exact Or.inl h
              · rcases List.mem_cons.mp h with rfl | h'
                · exact Or.inl hs
                · exact Or.inr h'
            obtain ⟨S, hsafe, hseenS, hpendS⟩ := ih seen rest hsz hrun hinv'
            exact ⟨S, hsafe, hseenS, fun q hq => by
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact hseenS q hs
              · exact hpendS q hq'⟩
          · rw [pikeHollow_go_step code reps which fuel pc seen rest hlt hgoal
              (by simpa using hs)] at hrun
            have hsz' : (seen.set! pc true).size = code.size := by
              rw [Array.size_set!]; exact hsz
            have hset : (seen.set! pc true)[pc]! = true :=
              getBang_set_self seen (by omega)
            have hinv' : ∀ q, (seen.set! pc true)[q]! = true →
                q < code.size ∧ q ≠ (reps[which]!).after - 1 ∧
                  ∀ t ∈ hollowTargets code reps q,
                    (seen.set! pc true)[t]! = true ∨
                      t ∈ hollowTargets code reps pc ++ rest := by
              intro q hq
              by_cases hqpc : q = pc
              · subst hqpc
                exact ⟨hlt, hgoal, fun t ht =>
                  Or.inr (List.mem_append_left _ ht)⟩
              · rw [getBang_set_other seen pc hqpc] at hq
                refine ⟨(hinv q hq).1, (hinv q hq).2.1, fun t ht => ?_⟩
                rcases (hinv q hq).2.2 t ht with h | h
                · left
                  by_cases htpc : t = pc
                  · subst htpc; exact hset
                  · rw [getBang_set_other seen pc htpc]; exact h
                · rcases List.mem_cons.mp h with rfl | h'
                  · exact Or.inl hset
                  · exact Or.inr (List.mem_append_right _ h')
            obtain ⟨S, hsafe, hseenS, hpendS⟩ :=
              ih (seen.set! pc true) (hollowTargets code reps pc ++ rest)
                hsz' hrun hinv'
            refine ⟨S, hsafe, fun q hq => hseenS q ?_, fun q hq => ?_⟩
            · by_cases hqpc : q = pc
              · subst hqpc; exact hset
              · rw [getBang_set_other seen pc hqpc]; exact hq
            · rcases List.mem_cons.mp hq with rfl | hq'
              · exact hseenS q hset
              · exact hpendS q (List.mem_append_right _ hq')

/-- What a `false` verdict is worth: a certificate covering the body's
entry, so no non-consuming walk out of the body reaches the repetition's
own `repNext`. -/
theorem pikeHollow_certificate {code : Array Inst} {reps : Array RepInfo}
    {which : Nat} (h : pikeHollow code reps which = false) :
    ∃ S, HollowSafe code reps ((reps[which]!).after - 1) S ∧
      S (reps[which]!).body := by
  rw [pikeHollow] at h
  have hblank : ∀ pc : Nat, (Array.replicate code.size false)[pc]! = false := by
    intro pc
    by_cases hpc : pc < code.size
    · rw [getElem!_pos _ pc (by simpa using hpc)]; simp
    · rw [getElem!_neg _ pc (by simpa using hpc)]; rfl
  obtain ⟨S, hsafe, _, hpend⟩ :=
    pikeHollow_go_safe code reps which (2 * code.size + 2)
      (Array.replicate code.size false) [(reps[which]!).body] (by simp) h
      (fun pc hpc => absurd (hblank pc ▸ hpc) (by simp))
  exact ⟨S, hsafe, hpend _ (by simp)⟩

/-- The absence itself: on a repetition `pike_hollow` cleared, an
iteration of the body can never come back round to its own `repNext`
without consuming a byte. -/
theorem pikeHollow_no_path {code : Array Inst} {reps : Array RepInfo}
    {which q : Nat} (h : pikeHollow code reps which = false)
    (hr : HollowReach code reps (reps[which]!).body q) :
    q < code.size ∧ q ≠ (reps[which]!).after - 1 := by
  obtain ⟨S, hsafe, hbody⟩ := pikeHollow_certificate h
  have hq := hsafe.reach hr hbody
  exact ⟨hsafe.bounded q hq, hsafe.avoids q hq⟩

/-- Eligibility, spelled at one repetition row: a pure star whose body
cannot finish an iteration emptily. -/
theorem pikeOk_star {code : Array Inst} {reps : Array RepInfo}
    (hok : pikeOk code reps = true) {i : Nat} (hi : i < reps.size) :
    (reps[i]!).lo = 0 ∧ (reps[i]!).hi = none32 ∧
      ∀ q, HollowReach code reps (reps[i]!).body q →
        q < code.size ∧ q ≠ (reps[i]!).after - 1 := by
  obtain ⟨hlo, hhi, hhollow⟩ := pikeOk_rep hok hi
  exact ⟨hlo, hhi, fun q hq => pikeHollow_no_path hhollow hq⟩

/-! ## The closure's own step, and the loop that cannot close

`pike_hollow` walks a relation of its own; the closure walks another. They
differ in one place — at a `repNext` the walk goes through the
repetition's deciding head while the closure jumps straight at the body —
and the two are the same relation once the repetition table is known to
describe the block it was emitted for. `FragAt.rows` reads that off the
fragment relation, and `pikeOk_no_eps_loop` states the result: on an
eligible program a star's loop-back edge can never be re-armed without
consuming a byte, which is the acyclicity the visited set rests on. -/

/-- Where the closure defers to from `pc` without consuming a byte:
`pike_add`'s own epsilon successors, preferred one first — which is the
order it pops them in, since it pushes the second arm before the first.
An assertion only defers when its test holds, so this over-approximates
the closure at any one position, which is the safe direction both for an
acyclicity argument and for a preference-order one. -/
def epsTargets (code : Array Inst) (reps : Array RepInfo) (pc : Nat) :
    List Nat :=
  match (code[pc]!).op with
  | .split => [(code[pc]!).arg, (code[pc]!).alt]
  | .jump => [(code[pc]!).arg]
  | .repLoop | .repNext =>
      let rep := reps[(code[pc]!).arg]!
      if rep.greedy then [rep.body, rep.after] else [rep.after, rep.body]
  | .chr | .chrCI | .cls | .any | .anyNoNL | .bsr | .accept => []
  | _ => [pc + 1]

/-- Where a closure can travel from `pc` without consuming a byte. -/
inductive EpsReach (code : Array Inst) (reps : Array RepInfo) :
    Nat → Nat → Prop where
  | refl {pc : Nat} : EpsReach code reps pc pc
  | step {pc mid q : Nat} (hmid : mid ∈ epsTargets code reps pc)
      (hrest : EpsReach code reps mid q) : EpsReach code reps pc q

theorem EpsReach.trans {code : Array Inst} {reps : Array RepInfo} :
    ∀ {a b c : Nat}, EpsReach code reps a b → EpsReach code reps b c →
      EpsReach code reps a c := by
  intro a b c h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hmid _ ih => exact .step hmid (ih h₂)

/-- One more epsilon step onto the end of a walk. -/
theorem EpsReach.snoc {code : Array Inst} {reps : Array RepInfo}
    {a b t : Nat} (h : EpsReach code reps a b)
    (ht : t ∈ epsTargets code reps b) : EpsReach code reps a t :=
  h.trans (.step ht .refl)

theorem HollowReach.trans {code : Array Inst} {reps : Array RepInfo} :
    ∀ {a b c : Nat}, HollowReach code reps a b → HollowReach code reps b c →
      HollowReach code reps a c := by
  intro a b c h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hmid _ ih => exact .step hmid (ih h₂)

/-- What a compiled repetition row says about the block it was emitted
for: the deciding head is that block's own `repLoop`, the body entry is
the cell right after it, the exit sits one past the block's own `repNext`,
and there is room between the two for the `repEnter` the head forks into.
-/
structure RowOk (code : Array Inst) (reps : Array RepInfo) (r : Nat) :
    Prop where
  head : code[(reps[r]!).head]! = ⟨.repLoop, r, 0⟩
  body : (reps[r]!).body = (reps[r]!).head + 1
  next : code[(reps[r]!).after - 1]! = ⟨.repNext, r, 0⟩
  room : (reps[r]!).head + 2 < (reps[r]!).after

/-- Every row a fragment claims describes its own block. The rows below
`r0` belong to earlier siblings and the rows from `r0 + repCount a` up to
later ones, which is the same accounting the compiler does. -/
theorem FragAt.rows {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    ∀ r, r0 ≤ r → r < r0 + repCount a → RowOk code reps r := by
  induction h with
  | nul | chr _ | chrCI _ | cls _ _ _ | any _ | anyNoNL _ | bsr _ =>
      intro r _ hlt
      rw [repCount] at hlt <;> first | omega | simp
  | assn ha _ =>
      intro r _ hlt
      rw [repCount_assn ha] at hlt
      omega
  | catNil =>
      intro r _ hlt
      rw [repCount_cat_nil] at hlt
      omega
  | @catCons k kids r0 lo mid hi _ _ ihk ihkids =>
      intro r hge hlt
      rw [repCount_cat_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount k) with h1 | h1
      · exact ihk r hge h1
      · exact ihkids r h1 (by omega)
  | @altOne a r0 lo hi _ iha =>
      intro r hge hlt
      rw [repCount_alt_cons, repCount_alt_nil] at hlt
      exact iha r hge (by omega)
  | @altCons a b rest r0 lo j hi _ _ _ _ iha ihrest =>
      intro r hge hlt
      rw [repCount_alt_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount a) with h1 | h1
      · exact iha r hge h1
      · exact ihrest r h1 (by omega)
  | grpZero _ ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | grpCap _ _ _ _ ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | repNone =>
      intro r _ hlt
      rw [repCount] at hlt
      omega
  | repOne _ ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | repOpt _ _ _ ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | @repGen lo' hi' greedy body r0 pc j _ hloop _ hnext _ hinfo
      _ hnot0 hnot1 hbody ihbody =>
      intro r hge hlt
      have hcount : repCount (.rep lo' hi' greedy body) = 1 + repCount body := by
        cases hi' with
        | none => rw [repCount] <;> simp
        | some v =>
            match v, hnot0, hnot1 with
            | 0, h, _ => exact absurd rfl h
            | 1, _, h => exact absurd rfl h
            | (_ + 2), _, _ => rw [repCount] <;> simp
      rw [hcount] at hlt
      rcases Nat.eq_or_lt_of_le hge with rfl | h1
      · have hb := hbody.le
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hinfo]; exact hloop
        · rw [hinfo]
        · rw [hinfo]
          show code[j + 1 - 1]! = _
          rw [show j + 1 - 1 = j from by omega]
          exact hnext
        · rw [hinfo]
          show pc + 1 + 2 < j + 1
          omega
      · exact ihbody r h1 (by omega)

/-- Every row of a compiled pattern describes its own block. -/
theorem compile_rows {p : Pat} (hc : Covered p.root) {r : Nat}
    (hr : r < (compile p).reps.size) :
    RowOk (compile p).code (compile p).reps r := by
  obtain ⟨hfrag, hrsz, _, _⟩ := compile_shape hc
  rw [hrsz] at hr
  exact hfrag.rows r (Nat.zero_le _) (by omega)

/-- Greediness orders a repetition's two arms; it does not change which
two they are. -/
private theorem mem_ite_pair {α : Type _} {c : Bool} {x y t : α} :
    (t ∈ if c then [x, y] else [y, x]) ↔ (t = x ∨ t = y) := by
  by_cases h : c = true
  · rw [if_pos h]; simp
  · rw [if_neg h]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or_comm

/-- One closure step is a `pike_hollow` walk: the two relations agree
everywhere but at a `repNext`, where the walk takes the deciding head
first and arrives at the same body one step later. -/
theorem hollowReach_of_epsStep {code : Array Inst} {reps : Array RepInfo}
    (hrows : ∀ r, r < reps.size → RowOk code reps r) {pc t : Nat}
    (ht : t ∈ epsTargets code reps pc) : HollowReach code reps pc t := by
  have hstep : ∀ u, u ∈ hollowTargets code reps pc →
      HollowReach code reps pc u := fun u hu => .step hu .refl
  cases hop : (code[pc]!).op
  case repNext =>
      -- The exit directly, the body through the deciding head.
      simp only [epsTargets, hop, mem_ite_pair] at ht
      rcases ht with rfl | rfl
      · by_cases hr : (code[pc]!).arg < reps.size
        · have hrow := hrows _ hr
          refine .step (mid := (reps[(code[pc]!).arg]!).head) ?_ ?_
          · simp only [hollowTargets, hop]; simp
          · refine .step (mid := (reps[(code[pc]!).arg]!).body) ?_ .refl
            simp only [hollowTargets, hrow.head]; simp
        · have hdef : (reps[(code[pc]!).arg]!).body =
              (reps[(code[pc]!).arg]!).head := by
            rw [getElem!_neg reps _ (by omega)]
            rfl
          rw [hdef]
          exact hstep _ (by simp only [hollowTargets, hop]; simp)
      · exact hstep _ (by simp only [hollowTargets, hop]; simp)
  all_goals
    simp only [epsTargets, hop, mem_ite_pair, List.mem_cons,
      List.not_mem_nil, or_false] at ht
  all_goals
    (refine hstep t ?_
     simp only [hollowTargets, hop, List.mem_cons, List.not_mem_nil, or_false]
     first | exact ht | exact ht.symm)

/-- And so is a whole closure walk. -/
theorem hollowReach_of_epsReach {code : Array Inst} {reps : Array RepInfo}
    (hrows : ∀ r, r < reps.size → RowOk code reps r) :
    ∀ {a b : Nat}, EpsReach code reps a b → HollowReach code reps a b := by
  intro a b h
  induction h with
  | refl => exact .refl
  | step hmid _ ih => exact (hollowReach_of_epsStep hrows hmid).trans ih

/-- The acyclicity eligibility bought. A star's loop-back edge leaves the
closure at the body's entry, and from there no chain of non-consuming
moves ever reaches that star's own `repNext` again — so no closure can go
round the loop twice, and depth-first in split order really is the
backtracking preference order. -/
theorem pikeOk_no_eps_loop {code : Array Inst} {reps : Array RepInfo}
    (hok : pikeOk code reps = true)
    (hrows : ∀ r, r < reps.size → RowOk code reps r) {r : Nat}
    (hr : r < reps.size) {q : Nat}
    (h : EpsReach code reps (reps[r]!).body q) :
    q < code.size ∧ q ≠ (reps[r]!).after - 1 :=
  (pikeOk_star hok hr).2.2 q (hollowReach_of_epsReach hrows h)

/-! ## An empty match is a non-consuming path

The last thing eligibility has to rule out is the empty iteration. The
backtracking matcher ends a star on an iteration that consumed nothing and
keeps that iteration's saves; the lockstep matcher has no such rule, so
the two can only agree where no iteration can finish empty. `pike_hollow`
decides that on the bytecode; what follows carries the verdict onto the
enumeration.

`frag_empty_reach` is the bridge, and it is an induction over the fragment
relation with nothing in it but control flow: a construct that matched
without moving spells out a non-consuming path from its entry to its exit,
one epsilon step per instruction the machine would have walked through.
`pikeOk_body_consumes` reads the consequence off it — on an eligible
program a star's body cannot match empty, because the path that would
witness it is the one `pike_ok` refused. -/

theorem EpsReach.one {code : Array Inst} {reps : Array RepInfo} {x y : Nat}
    (h : y ∈ epsTargets code reps x) : EpsReach code reps x y := .step h .refl

private theorem search_cat_eq {c : Spec.SCtx} (fuel : Nat) (kids : List Ast)
    (pos : Nat) (regs : Spec.Regs) :
    Spec.search fuel c (.cat kids) pos regs =
      Spec.searchCat fuel c kids pos regs := by
  rw [Spec.search.eq_def]

private theorem search_alt_eq {c : Spec.SCtx} (fuel : Nat) (arms : List Ast)
    (pos : Nat) (regs : Spec.Regs) :
    Spec.search fuel c (.alt arms) pos regs =
      Spec.searchAlt fuel c arms pos regs := by
  rw [Spec.search.eq_def]

private theorem search_grp_eq {c : Spec.SCtx} (fuel cap : Nat) (body : Ast)
    (pos : Nat) (regs : Spec.Regs) :
    Spec.search fuel c (.grp cap body) pos regs =
      (Spec.search fuel c body pos
        (if cap != 0 then regs.set! (2 * cap) pos.toUInt32 else regs)).map
        (List.map fun t =>
          if cap != 0 then ⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩
          else t) := by
  rw [Spec.search.eq_def]

private theorem search_rep_one_eq {c : Spec.SCtx} (fuel : Nat) (greedy : Bool)
    (body : Ast) (pos : Nat) (regs : Spec.Regs) :
    Spec.search fuel c (.rep 1 (some 1) greedy body) pos regs =
      Spec.search fuel c body pos regs := by
  rw [Spec.search.eq_def]
  simp only []
  rw [if_pos (by simp)]

private theorem search_rep_opt_eq {c : Spec.SCtx} (fuel lo' : Nat)
    (greedy : Bool) (body : Ast) (pos : Nat) (regs : Spec.Regs)
    (h : lo' ≠ 1) :
    Spec.search fuel c (.rep lo' (some 1) greedy body) pos regs =
      (Spec.search fuel c body pos regs).map fun taken =>
        if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken := by
  rw [Spec.search.eq_def]
  simp only []
  rw [if_neg (by simpa using h)]

private theorem search_rep_gen_eq {c : Spec.SCtx} (fuel lo' : Nat)
    (hi : Option Nat) (greedy : Bool) (body : Ast) (pos : Nat)
    (regs : Spec.Regs) (h0 : hi ≠ some 0) (h1 : hi ≠ some 1) :
    Spec.search fuel c (.rep lo' hi greedy body) pos regs =
      Spec.searchRep fuel c body lo' hi greedy 0 pos regs := by
  match hi, h0, h1 with
  | none, _, _ => rw [Spec.search.eq_def]
  | some 0, h, _ => exact absurd rfl h
  | some 1, _, h => exact absurd rfl h
  | some (_ + 2), _, _ =>
      rw [Spec.search.eq_def]
      simp only []

/-- A construct that matched without consuming a byte spells a
non-consuming path from its fragment's entry to its exit. Every clause is
the control flow the machine would have taken: a leaf that consumes cannot
be in the picture at all, an assertion and a save step to the next cell,
an alternation goes in by its split and out by its jump, and a repetition
either skips through its head or completes an empty iteration and leaves
by its `repNext`. -/
theorem frag_empty_reach {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {c : Spec.SCtx} {a : Ast} {r0 lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    ∀ (fuel pos : Nat) (regs : Spec.Regs) (ts : List Spec.Thread),
      Spec.search fuel c a pos regs = some ts → pos ≤ c.s.size →
      ∀ t ∈ ts, t.pos = pos → EpsReach code reps lo hi := by
  induction h with
  | nul => exact fun _ _ _ _ _ _ _ _ _ => .refl
  | chr _ | chrCI _ | cls _ _ _ | any _ | anyNoNL _ =>
      intro fuel pos regs ts hs _ t ht hpos
      rw [Spec.search.eq_def] at hs
      cases hs
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [] at hpos
        omega
      · simp at ht
  | @bsr r0 pc hcell =>
      intro fuel pos regs ts hs _ t ht hpos
      rw [Spec.search.eq_def] at hs
      cases hs
      split at ht <;> rename_i heaten
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [] at hpos
        simp only [bne_iff_ne, ne_eq] at heaten
        omega
      · simp at ht
  | @assn a' op r0 pc ha hcell =>
      intro fuel pos regs ts hs _ t ht hpos
      have hop : (code[pc]!).op = op := by rw [hcell]
      have hstep : EpsReach code reps pc (pc + 1) := by
        refine .one ?_
        cases a' <;> simp only [assnOp] at ha <;> try cases ha
        all_goals simp [epsTargets, hop]
      exact hstep
  | catNil => exact fun _ _ _ _ _ _ _ _ _ => .refl
  | @catCons k kids r0 pc mid hi hk hkids ihk ihkids =>
      intro fuel pos regs ts hs hpos t ht hzero
      rw [search_cat_eq, Spec.searchCat.eq_def] at hs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hs
      obtain ⟨heads, hheads, tails, htails, rfl⟩ := hs
      simp only [List.mem_flatten] at ht
      obtain ⟨l, hl, htl⟩ := ht
      obtain ⟨u, hu, hul⟩ := Spec.mapM_mem htails hl
      have hb1 := Spec.search_pos_le hheads hpos u hu
      have hb2 := Spec.searchCat_pos_le hul hb1.2 t htl
      have hue : u.pos = pos := by omega
      refine (ihk fuel pos regs heads hheads hpos u hu hue).trans ?_
      refine ihkids fuel pos u.regs l ?_ hpos t htl hzero
      rw [search_cat_eq, ← hue]
      exact hul
  | @altOne a' r0 pc hi ha iha =>
      intro fuel pos regs ts hs hpos t ht hzero
      rw [search_alt_eq, Spec.searchAlt.eq_def] at hs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hs
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := hs
      rw [Spec.searchAlt.eq_def] at htheirs
      cases htheirs
      rw [List.append_nil] at ht
      exact iha fuel pos regs mine hmine hpos t ht hzero
  | @altCons a' b rest r0 pc j hi hsplit ha hjump hrest iha ihrest =>
      intro fuel pos regs ts hs hpos t ht hzero
      have hop : (code[pc]!).op = .split := by rw [hsplit]
      rw [search_alt_eq, Spec.searchAlt.eq_def] at hs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hs
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := hs
      rcases List.mem_append.mp ht with hm | hm
      · refine (EpsReach.one (y := pc + 1) ?_).trans ?_
        · simp [epsTargets, hsplit]
        · exact (iha fuel pos regs mine hmine hpos t hm hzero).trans
            (.one (by simp [epsTargets, hjump]))
      · refine (EpsReach.one (y := j + 1) ?_).trans ?_
        · simp [epsTargets, hsplit]
        · refine ihrest fuel pos regs theirs ?_ hpos t hm hzero
          rw [search_alt_eq]
          exact htheirs
  | @grpZero body r0 pc hi hbody ihbody =>
      intro fuel pos regs ts hs hpos t ht hzero
      rw [search_grp_eq] at hs
      simp only [Option.map_eq_some_iff] at hs
      obtain ⟨taken, htaken, rfl⟩ := hs
      simp only [List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hue : u.pos = pos := by split at hzero <;> exact hzero
      exact ihbody fuel pos _ taken htaken hpos u hu hue
  | @grpCap cap body r0 pc j hcap hopen hbody hclose ihbody =>
      intro fuel pos regs ts hs hpos t ht hzero
      have hopenop : (code[pc]!).op = .save := by rw [hopen]
      have hcloseop : (code[j]!).op = .save := by rw [hclose]
      rw [search_grp_eq] at hs
      simp only [Option.map_eq_some_iff] at hs
      obtain ⟨taken, htaken, rfl⟩ := hs
      simp only [List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hue : u.pos = pos := by split at hzero <;> exact hzero
      refine (EpsReach.one (y := pc + 1) (by simp [epsTargets, hopenop])).trans ?_
      exact (ihbody fuel pos _ taken htaken hpos u hu hue).trans
        (.one (by simp [epsTargets, hcloseop]))
  | repNone => exact fun _ _ _ _ _ _ _ _ _ => .refl
  | @repOne greedy body r0 pc hi hbody ihbody =>
      intro fuel pos regs ts hs hpos t ht hzero
      rw [search_rep_one_eq] at hs
      exact ihbody fuel pos regs ts hs hpos t ht hzero
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro fuel pos regs ts hs hpos t ht hzero
      have hmemsucc : sp + 1 ∈ epsTargets code reps sp := by
        cases hg : greedy <;> simp [epsTargets, hsplit, hg]
      have hmemexit : j ∈ epsTargets code reps sp := by
        cases hg : greedy <;> simp [epsTargets, hsplit, hg]
      rw [search_rep_opt_eq _ _ _ _ _ _ hlo] at hs
      simp only [Option.map_eq_some_iff] at hs
      obtain ⟨taken, htaken, rfl⟩ := hs
      have hcase : t ∈ taken ∨ t = ⟨pos, regs⟩ := by
        split at ht
        · simpa only [List.mem_append, List.mem_singleton] using ht
        · rcases List.mem_cons.mp ht with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
      rcases hcase with hm | rfl
      · exact EpsReach.trans (.one hmemsucc)
          (ihbody fuel pos regs taken htaken hpos t hm hzero)
      · exact .one hmemexit
  | @repGen lo' hi' greedy body r0 pc j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro fuel pos regs ts hs hpos t ht hz
      have hzeroop : (code[pc]!).op = .repZero := by rw [hzero]
      have hloopop : (code[pc + 1]!).op = .repLoop := by rw [hloop]
      have hloopar : (code[pc + 1]!).arg = r0 := by rw [hloop]
      have henterop : (code[pc + 2]!).op = .repEnter := by rw [henter]
      have hnextop : (code[j]!).op = .repNext := by rw [hnext]
      have hnextar : (code[j]!).arg = r0 := by rw [hnext]
      -- The head forks between the body's first cell and the exit.
      have hhead : ∀ x, x = pc + 2 ∨ x = j + 1 →
          x ∈ epsTargets code reps (pc + 1) := by
        intro x hx
        simp only [epsTargets, hloopop, hloopar, hinfo, mem_ite_pair]
        exact hx
      have hexit : EpsReach code reps pc (j + 1) :=
        (EpsReach.one (by simp [epsTargets, hzeroop])).trans
          (.one (hhead _ (Or.inr rfl)))
      have hin : EpsReach code reps pc (pc + 3) :=
        ((EpsReach.one (by simp [epsTargets, hzeroop])).trans
            (.one (hhead _ (Or.inl rfl)))).trans
          (.one (by simp [epsTargets, henterop]))
      have hback : ∀ x, x = (reps[r0]!).body ∨ x = (reps[r0]!).after →
          x ∈ epsTargets code reps j := by
        intro x hx
        simp only [epsTargets, hnextop, hnextar, mem_ite_pair]
        exact hx
      -- One round of the counted repetition, read for an empty answer.
      have hrep : ∀ (f cnt p : Nat) (rg : Spec.Regs) (us : List Spec.Thread),
          Spec.searchRep f c body lo' hi' greedy cnt p rg = some us →
          p ≤ c.s.size → ∀ u ∈ us, u.pos = p →
          EpsReach code reps pc (j + 1) := by
        intro f cnt p rg us hus hp u hu hue
        match f with
        | 0 => rw [Spec.searchRep.eq_def] at hus; exact absurd hus (by simp)
        | f + 1 =>
            rw [Spec.searchRep.eq_def] at hus
            simp only [] at hus
            have henterCase : ∀ v,
                (do
                  let taken ← Spec.search f c body p rg
                  let onward ← taken.mapM fun w =>
                    if hi'.isNone && w.pos == p && cnt + 1 ≥ lo' then
                      pure [w]
                    else
                      Spec.searchRep f c body lo' hi' greedy (cnt + 1)
                        w.pos w.regs
                  pure onward.flatten : Option (List Spec.Thread)) = some v →
                ∀ w ∈ v, w.pos = p → EpsReach code reps pc (j + 1) := by
              intro v hv w hw hwe
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
                Option.pure_def, Option.some.injEq] at hv
              obtain ⟨taken, htaken, onward, honward, rfl⟩ := hv
              simp only [List.mem_flatten] at hw
              obtain ⟨l, hl, hwl⟩ := hw
              obtain ⟨x, hx, hxl⟩ := Spec.mapM_mem honward hl
              have hb1 := Spec.search_pos_le htaken hp x hx
              have hxe : x.pos = p := by
                split at hxl
                · simp only [Option.some.injEq] at hxl
                  subst hxl
                  simp only [List.mem_singleton] at hwl
                  subst hwl
                  omega
                · have := Spec.searchRep_pos_le hxl hb1.2 w hwl
                  omega
              exact hin.trans ((ihbody f p rg taken htaken hp x hx hxe).trans
                (.one (hback (j + 1) (Or.inr (by rw [hinfo])))))
            split at hus
            · exact henterCase _ hus u hu hue
            · split at hus
              · cases hus
                simp only [List.mem_singleton] at hu
                subst hu
                exact hexit
              · obtain ⟨taken, htaken, hres⟩ := Option.bind_eq_some_iff.mp hus
                simp only [Option.pure_def, Option.some.injEq] at hres
                subst hres
                have hcase : u ∈ taken ∨ u = ⟨p, rg⟩ := by
                  split at hu
                  · simpa only [List.mem_append, List.mem_singleton] using hu
                  · rcases List.mem_cons.mp hu with h' | h'
                    · exact Or.inr h'
                    · exact Or.inl h'
                rcases hcase with hm | rfl
                · exact henterCase _ htaken u hm hue
                · exact hexit
      rw [search_rep_gen_eq _ _ _ _ _ _ _ hnot0 hnot1] at hs
      exact hrep fuel 0 pos regs ts hs hpos t ht hz

/-- On an eligible program a star's body cannot match without consuming a
byte. The thread that would witness it spells a non-consuming path from
the body's first cell to the block's own `repNext`, and one step through
the `repEnter` in front of it turns that into the path `pike_ok` refused.

So the empty-match rule the backtracking matcher runs at `repNext` never
fires here, and the lockstep matcher's want of one costs it nothing. -/
theorem frag_rep_body_consumes {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {c : Spec.SCtx} {lo' : Nat} {hi : Option Nat}
    {greedy : Bool} {body : Ast} {r0 pc j : Nat}
    (hok : pikeOk code reps = true)
    (hrows : ∀ i, i < reps.size → RowOk code reps i)
    (hnot0 : hi ≠ some 0) (hnot1 : hi ≠ some 1)
    (h : FragAt code classes reps r0 (.rep lo' hi greedy body) pc j) :
    ∀ (fuel pos : Nat) (regs : Spec.Regs) (ts : List Spec.Thread),
      Spec.search fuel c body pos regs = some ts → pos ≤ c.s.size →
      ∀ t ∈ ts, t.pos ≠ pos := by
  cases h with
  | assn ha _ => simp [assnOp] at ha
  | repNone => exact absurd rfl hnot0
  | repOne _ => exact absurd rfl hnot1
  | repOpt _ _ _ => exact absurd rfl hnot1
  | repGen hzero hloop henter hnext hrow hinfo hbound hn0 hn1 hbody =>
      rename_i jj
      intro fuel pos regs ts hs hpos t ht he
      have hbodypc : (reps[r0]!).body = pc + 2 := by rw [hinfo]
      have hafter : (reps[r0]!).after = jj + 1 := by rw [hinfo]
      have hpath : EpsReach code reps (reps[r0]!).body jj := by
        rw [hbodypc]
        exact (EpsReach.one (by simp [epsTargets, henter])).trans
          (frag_empty_reach hbody fuel pos regs ts hs hpos t ht he)
      exact (pikeOk_no_eps_loop hok hrows hrow hpath).2 (by omega)

/-! ## What one closure build can mark

The closure is `pike_add`: a stack of deferred threads, popped one at a
time, each fresh pc marked and replaced by the continuations its
instruction offers. Reading that against `epsTargets` gives the invariant
the dedup argument wants — every pc a build marks is epsilon-reachable
from the pc it was seeded with — and with the acyclicity above, a build
seeded inside a star's body can never mark that star's own `repNext`. -/

/-- The pc a closure pops is one of the pcs on its stack. -/
private theorem back_mem_toList {A : Array Th} (hne : A.size ≠ 0) :
    A.back! ∈ A.toList := by
  have hlt : A.size - 1 < A.toList.length := by
    simp only [Array.length_toList]; omega
  rw [Array.back!, getElem!_pos A (A.size - 1) (by simpa using hlt),
    ← Array.getElem_toList]
  exact List.getElem_mem hlt

/-- A refusal is not a completion: the two `Except` constructors cannot be
the same value. Spelled as a lemma rather than a tactic so a branch that
does not fit it fails to elaborate instead of failing to close. -/
private theorem absurd_error {α β : Type} {a : α} {b : β} {P : Prop}
    (h : (Except.error a : Except α β) = Except.ok b) : P := by cases h

set_option maxHeartbeats 1000000 in
/-- The closure loop only marks what it can reach. Each iteration pops one
thread: a pc already marked lets its handle go and changes nothing, and a
fresh pc is marked and replaced on the stack by continuations its
instruction defers to — which is to say by its `epsTargets`. So the
reachability of the pcs on the stack is an invariant, and the marks it
leaves behind are covered by it. -/
theorem pikeAdd_go_marks (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (intoNext : Bool) (pos pc0 : Nat) :
    ∀ (fuel : Nat) (st st' : PikeSt),
      pikeAdd.go re s mo lim intoNext pos fuel st = .ok st' →
      (∀ th ∈ st.stk.toList, EpsReach re.code re.reps pc0 th.pc) →
      ∀ q, st'.seen[q]! = true →
        st.seen[q]! = true ∨ EpsReach re.code re.reps pc0 q := by
  intro fuel
  induction fuel with
  | zero =>
      intro st st' hok _
      rw [pikeAdd.go] at hok
      exact absurd hok (by simp)
  | succ fuel ih =>
      intro st st' hok hinv
      simp only [pikeAdd.go] at hok
      split at hok
      · cases hok
        exact fun q hq => Or.inl hq
      · have hr0 : EpsReach re.code re.reps pc0 st.stk.back!.pc := by
          refine hinv _ (back_mem_toList ?_)
          rename_i hne
          simpa using hne
        have hpop : ∀ th ∈ st.stk.pop.toList,
            EpsReach re.code re.reps pc0 th.pc := by
          intro th hth
          rw [Array.toList_pop] at hth
          exact hinv th (List.dropLast_subset _ hth)
        have hpush : ∀ (A : Array Th),
            (∀ th ∈ A.toList, EpsReach re.code re.reps pc0 th.pc) →
            ∀ t hh : Nat, t ∈ epsTargets re.code re.reps st.stk.back!.pc →
            ∀ th ∈ (A.push ⟨t, hh⟩).toList,
              EpsReach re.code re.reps pc0 th.pc := by
          intro A hA t hh ht th hth
          rw [Array.toList_push] at hth
          rcases List.mem_append.mp hth with h | h
          · exact hA th h
          · simp only [List.mem_singleton] at h
            subst h
            exact hr0.snoc ht
        have hfinish : ∀ stX : PikeSt,
            stX.seen = st.seen.set! st.stk.back!.pc true →
            (∀ th ∈ stX.stk.toList, EpsReach re.code re.reps pc0 th.pc) →
            pikeAdd.go re s mo lim intoNext pos fuel stX = .ok st' →
            ∀ q, st'.seen[q]! = true →
              st.seen[q]! = true ∨ EpsReach re.code re.reps pc0 q := by
          intro stX hseen hstk hgo q hq
          rcases ih _ _ hgo hstk q hq with h | h
          · rw [hseen] at h
            by_cases hqpc : q = st.stk.back!.pc
            · exact Or.inr (hqpc ▸ hr0)
            · exact Or.inl (by rwa [getBang_set_other st.seen _ hqpc] at h)
          · exact Or.inr h
        split at hok
        · -- Already marked: the handle goes and the walk carries on.
          split at hok
          · exact absurd hok (by simp)
          · rename_i stD hD
            obtain ⟨hk, he⟩ := pikeDrop_ok hD
            intro q hq
            rcases ih _ _ hok (by rw [hk]; exact hpop) q hq with h | h
            · exact Or.inl (by rw [he] at h; exact h)
            · exact Or.inr h
        · split at hok
          · exact absurd hok (by simp)
          · repeat' split at hok
            all_goals first
              | exact absurd_error hok
              | -- A fork: two continuations, the preferred one on top.
                (rename_i _ stA hA _ stB hB
                 obtain ⟨hkA, heA⟩ := pikeDefer_ok hA
                 obtain ⟨hkB, heB⟩ := pikeDefer_ok hB
                 exact hfinish _ (by rw [heB, heA])
                   (by rw [hkB, hkA]
                       exact hpush _ (hpush _ hpop _ _ (by simp [epsTargets, *]))
                         _ _ (by simp [epsTargets, *])) hok)
              | -- A save: the copy-on-write, then one continuation.
                (rename_i _ stW _ hW _ stD hD
                 obtain ⟨hkW, heW⟩ := pikeWrite_ok hW
                 obtain ⟨hkD, heD⟩ := pikeDefer_ok hD
                 exact hfinish _ (by rw [heD, heW])
                   (by rw [hkD, hkW]
                       exact hpush _ hpop _ _ (by simp [epsTargets, *])) hok)
              | -- One continuation.
                (rename_i _ stD hD
                 obtain ⟨hk, he⟩ := pikeDefer_ok hD
                 exact hfinish _ (by rw [he])
                   (by rw [hk]
                       exact hpush _ hpop _ _ (by simp [epsTargets, *])) hok)
              | -- A dead thread.
                (rename_i _ stD hD
                 obtain ⟨hk, he⟩ := pikeDrop_ok hD
                 exact hfinish _ (by rw [he]) (by rw [hk]; exact hpop) hok)
              | -- A thread parked for the position it waits on.
                (rename_i _ stP hP
                 obtain ⟨hk, he⟩ := pikePark_ok hP
                 exact hfinish _ (by rw [he]) (by rw [hk]; exact hpop) hok)

/-- One whole closure build, seeded on an empty stack: every mark it adds
sits on an epsilon walk out of the seed. -/
theorem pikeAdd_marks {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {intoNext : Bool} {pos pc0 h0 : Nat} {st st' : PikeSt}
    (hstk : st.stk.size = 0)
    (hok : pikeAdd re s mo lim intoNext pos pc0 h0 st = .ok st') :
    ∀ q, st'.seen[q]! = true →
      st.seen[q]! = true ∨ EpsReach re.code re.reps pc0 q := by
  rw [pikeAdd] at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i stO hdef
    obtain ⟨hk, he⟩ := pikeDefer_ok hdef
    have hnil : st.stk.toList = [] := by
      rw [← List.length_eq_zero_iff, Array.length_toList, hstk]
    have hseed : ∀ th ∈ stO.stk.toList, EpsReach re.code re.reps pc0 th.pc := by
      intro th hth
      rw [hk, Array.toList_push] at hth
      rcases List.mem_append.mp hth with h | h
      · exact absurd h (by rw [hnil]; simp)
      · simp only [List.mem_singleton] at h
        subst h
        exact .refl
    intro q hq
    rcases pikeAdd_go_marks re s mo lim intoNext pos pc0 _ stO st' hok hseed q hq
      with h | h
    · exact Or.inl (by rw [he] at h; exact h)
    · exact Or.inr h

/-- The lockstep matcher's own no-reentry fact, and the point of the
eligibility test: a closure seeded at a star's body entry never marks that
star's `repNext`, so within one position the loop-back edge is taken at
most once. -/
theorem pikeAdd_no_reentry {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {intoNext : Bool} {pos h0 r : Nat} {st st' : PikeSt}
    (hok : pikeOk re.code re.reps = true)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hr : r < re.reps.size) (hstk : st.stk.size = 0)
    (hbuild : pikeAdd re s mo lim intoNext pos (re.reps[r]!).body h0 st = .ok st')
    (hfresh : st.seen[(re.reps[r]!).after - 1]! = false) :
    st'.seen[(re.reps[r]!).after - 1]! = false := by
  cases h : st'.seen[(re.reps[r]!).after - 1]!
  · rfl
  · exfalso
    rcases pikeAdd_marks hstk hbuild _ h with h1 | h1
    · rw [hfresh] at h1
      exact absurd h1 (by simp)
    · exact (pikeOk_no_eps_loop hok hrows hr h1).2 rfl

/-! ## The two guards

`pikeRun` refuses two kinds of call before it allocates anything: a
program the lockstep matcher may not run, and a start offset past the
subject's end. The second is the specification's own BadInput; the first
is a refusal the specification knows nothing about, which is why the
eligibility premise appears in the statement rather than in the
conclusion. -/

/-- The two refusals, located. Nothing below them answers BadInput: the
position loop reports a match, no match, or a budget refusal. -/
theorem pikeRun_badInput (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) (init : PikeSt) :
    (pikeRun re s start mo lim init).outcome = .badInput ↔
      (re.pike = false ∨ start > s.size) := by
  unfold pikeRun
  split
  · rename_i hpk
    exact ⟨fun _ => Or.inl (by simpa using hpk), fun _ => rfl⟩
  · rename_i hpk
    have hpk' : re.pike = true := by simpa using hpk
    split
    · rename_i hst
      exact ⟨fun _ => Or.inr hst, fun _ => rfl⟩
    · rename_i hst
      refine ⟨fun hbad => absurd hbad ?_, ?_⟩
      · simp only []
        repeat' split
        all_goals simp
      · rintro (h | h)
        · exact absurd hpk' (by simp [h])
        · exact absurd h hst

/-- Once the subject fits the documented cap, the specification calls an
input bad on exactly one condition: a start offset past the subject's
end. -/
theorem matches_badInput_iff {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} (hs : s.size ≤ ceiling) :
    Spec.Matches p s start mo = .badInput ↔ start > s.size := by
  have hst := Spec.matches_stable p s start mo _ (Nat.le_refl _)
  constructor
  · intro hbad
    rcases Nat.lt_or_ge s.size start with hlt | hle
    · exact hlt
    · exfalso
      have hcond : ¬ (decide (start > s.size) || decide (s.size > ceiling)) =
          true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
        omega
      rw [Spec.matchesF, if_neg hcond, hbad] at hst
      exact scan_ne_badInput _ _ _ hst rfl
  · intro hlt
    have hcond : (decide (start > s.size) || decide (s.size > ceiling)) =
        true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl hlt
    rw [Spec.matchesF, if_pos hcond] at hst
    exact (Option.some.inj hst).symm

/-- S-8's third clause for the lockstep matcher: on an eligible program
and a subject inside the documented cap, the two layers refuse exactly the
same calls. -/
theorem pikeRun_badInput_agrees {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} {init : PikeSt} (hs : s.size ≤ ceiling)
    (hok : (compile p).pike = true) :
    (pikeRun (compile p) s start mo lim init).outcome = .badInput ↔
      Spec.Matches p s start mo = .badInput := by
  rw [pikeRun_badInput, matches_badInput_iff hs]
  exact ⟨fun h => h.resolve_left (by simp [hok]), Or.inr⟩

/-! ## The target

The statement the rest of S-8 has to reach, spelled the way
`BtRunRefinesMatches` is spelled and read against the same three
hypotheses — the parser facts, the documented subject cap, the
counter-wrap bound — plus the one the lockstep matcher adds: the program
is eligible, since an ineligible one is refused at the door for a reason
the specification has no opinion about.

The third clause, BadInput, is `pikeRun_badInput_agrees` above. The two
that remain are the substance, and what is left of them is the lockstep
bookkeeping itself:

* the closure at one position builds the deduplicated, preference-ordered
  list of the surviving threads the backtracking enumeration would have
  there. The dedup is sound because on a `PikeShape` tree no compiled
  repetition has a counter worth reading, so `repZero` and `repEnter` are
  plain epsilon steps and `repLoop` and `repNext` plain epsilon forks and
  a thread's future is its pc alone; because `frag_rep_body_consumes`
  rules the empty iteration out, so the two matchers read a star the same
  way; and because `pikeAdd_no_reentry` closes off the one backward edge,
  so first arrival wins exactly. What is missing is the correspondence
  itself — the invariant relating the built list to the pending
  continuations of `frag_runs`, order-preserving and dropping only
  duplicates;
* one position step, then the loop, seeding at lowest priority for the
  leftmost rule and letting an accepting thread kill everything below it
  while higher-priority threads may still overwrite it;
* delivery, against `Spec.scan`'s first survivor.

When those land, `matchers_agree` in `Pcrevera/Proofs/ExecRefine.lean`
becomes unconditional: it already takes the two `RefinesMatches` facts,
and `Pcrevera/Proofs/ExecBacktrack.lean` shows how the backtracking half
composes into it. -/

/-- Whenever the lockstep run reports matched or no-match on an eligible
program, its answer is the specification's — found with the very ovector,
or not found — and the two layers agree on bad input. A budget refusal is
the one answer that claims nothing, so completion is not asserted here any
more than it is in `BtRunRefinesMatches`. -/
def PikeRunRefinesMatches : Prop :=
  ∀ (p : Pat) (s : ByteArray) (start : Nat) (mo : MOpts) (lim : Limits)
    (init : PikeSt),
    Wf p → s.size ≤ ceiling → (compile p).pike = true →
    Spec.suffFuel s.size p.root < none32 →
    RefinesMatches (pikeRun (compile p) s start mo lim init) p s start mo

end Pcrevera.Refine
