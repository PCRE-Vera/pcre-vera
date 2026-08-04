import Pcrevera.Proofs.Refine
import Pcrevera.Proofs.Agreement
import Pcrevera.Proofs.PikeBounds

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
  first half of the acyclicity the visited set rests on: on an eligible
  program a star's loop-back edge can never be re-armed without consuming
  a byte. `FragAt.epsForward` is the other half — every closure edge in
  the program runs forward, except a `repNext`'s offer of its own block's
  body — and `epsReach_no_cycle` puts the two together: no closure walk
  ever takes a step and comes back where it started. That is what makes
  depth-first in split order the backtracking preference order, and a
  marked pc one the closure is done with.

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

* **The mirror's non-consuming moves.** `eff_hollow_goto` and
  `eff_hollow_fork` say every move the backtracking mirror makes without
  advancing the position is a step of `pike_hollow`'s walk, `repNext`'s
  return to its deciding head included — which is why the walk was
  written to go through the head. On that bridge rests the invariant
  `EntryPast`/`EntryFresh`: a recorded entry position is one already
  reached, and where a repetition's own `repNext` is still in reach
  without consuming, the iteration under way did not start here.
  `eff_entry_goto` and `eff_entry_fork` preserve it, and
  `eff_repNext_loops` is the payoff — the machine-level twin of
  `frag_rep_body_consumes`, saying the mirror at a `repNext` always
  returns to its head, so the empty-match rule is dead code there too.

* **The capture pool.** A lockstep thread carries a handle into a flat
  pool where the specification's threads carry the block itself, so the
  correspondence needs a decoding. `blockAt` is it — `deliver_eq_blockAt`
  says it is the very slice `pike_run` hands back on a match — and what
  the rest asks of it is three facts: `blockAt_seed` (a seed starts blank
  but for the attempt in slot 0), `pikeTake_pool` (taking a block only
  appends, so a block the pool already had reads the same afterwards) and
  `pikeWrite_block` (a write is a register write, in place through an
  unshared handle and on a fresh copy through a shared one).
  `pikeWrite_block_owned` discharges its room hypotheses from `Owned`, the
  ownership reading of `PikeBounds`, whose `blocks` clause says the pool
  is the refcount table's blocks laid end to end.

* **No way into the middle of a block.** The count a `repLoop` reads is
  the one `repZero` left, and the reason is an address one.
  `FragAt.targets` says a construct's compiled form never spells an
  address outside its own range, `FragAt.blockIn` nests every repetition
  row's block inside the fragment that claimed it, and
  `FragAt.noMidEntry` reads the two together — an edge that lands in a
  block starts in that block or at the `repZero` in front of it.
  `FragAt.cells` is the same induction read down the other side, over
  what each construct pins rather than what it targets: every repetition
  opcode stands at the address its own row names and every save lands
  inside the ovector. `compile_noMidEntry` and `compile_cellsOk` state
  the two for a whole compiled pattern, the ENDANCHORED assertion and the
  accept behind the root included.

* **The count at the deciding head.** `CountPast` is what a
  configuration inside a block carries: while the round's `repEnter` is
  still ahead, a count no larger than the position it stands at, and once
  that cell is behind, a count no larger than the position the round
  began at — which `EntryPast` turns back into the first, since a
  recorded entry position is one already reached. `eff_count_goto` and
  `eff_count_fork` preserve it — away from a block's three writing cells
  a move can only be carrying a count that was already live — and the
  entry-position invariant turns the second half into a strict
  inequality, so the bump at `repNext` never reaches the sentinel.
  `eff_repLoop_forks` is the payoff and the twin of `eff_repNext_loops`:
  wherever those invariants hold, the deciding head of an eligible
  program always forks.

* **The dedup lemma.** `Steady` bundles the three invariants,
  `eff_steady_goto`/`eff_steady_fork` carry it across a move, and
  `eff_ctrl_congr` says what they were for — at a steady configuration
  the mirror's next move is a function of the pc and the position alone,
  so two threads meeting at the same pc with different register files
  cannot be told apart by the control flow. `run_dedup` runs that out
  over a whole search, pending stacks travelling entry for entry, and
  `resumes_drop` is the form the thread list wants: an entry whose search
  has already come back empty is one the list can do without.
  `compile_runs_dedup` states it with every side condition about the
  program discharged, and `resumes_drop_dup` is the visited set's own
  step — a pending list already carrying this pc at this position higher
  up answers the same without the second copy.

* **The bumpalong, on this side.** `pikeSeed_skip_spec`: the position loop
  declines a starting position exactly where `Spec.scan` skips an attempt.

* **The guards.** `pikeRun_badInput` locates the two refusals in the call
  itself, and `pikeRun_badInput_agrees` matches them against the
  specification's own BadInput under the documented subject cap. That is
  S-8's third clause for this matcher, proved.
-/

open private rootSt from Pcrevera.Proofs.Refine

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

/-- A single epsilon step is a walk. -/
theorem EpsReach.one {code : Array Inst} {reps : Array RepInfo} {x y : Nat}
    (h : y ∈ epsTargets code reps x) : EpsReach code reps x y := .step h .refl

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
for: the deciding head is that block's own `repLoop`, the cell in front of
it zeroes the count, the body entry is the cell right after it and records
the round's starting position, the exit sits one past the block's own
`repNext`, and there is room between the head and the exit for the
`repEnter` the head forks into. -/
structure RowOk (code : Array Inst) (reps : Array RepInfo) (r : Nat) :
    Prop where
  low : 0 < (reps[r]!).head
  zero : code[(reps[r]!).head - 1]! = ⟨.repZero, r, 0⟩
  head : code[(reps[r]!).head]! = ⟨.repLoop, r, 0⟩
  enter : code[(reps[r]!).body]! = ⟨.repEnter, r, 0⟩
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
  | @repGen lo' hi' greedy body r0 pc j hzero hloop henter hnext _ hinfo
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
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hinfo]
          show 0 < pc + 1
          omega
        · rw [hinfo]
          show code[pc + 1 - 1]! = _
          rw [show pc + 1 - 1 = pc from by omega]
          exact hzero
        · rw [hinfo]; exact hloop
        · rw [hinfo]; exact henter
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

/-! ## No way into the middle of a block

The count a `repLoop` reads is the one `repZero` left, and the reason is
an address one: nothing outside a repetition's block defers into it
except the `repZero` standing in front of it. Three inductions say so,
and all three are the accounting of `FragAt.rows` again.

`FragAt.targets` is the containment — a construct's compiled form never
spells an address outside its own range, one past the end included.
`FragAt.blockIn` nests every row's block inside the fragment that claimed
it, with room in front of the head for the `repZero`. `FragAt.noMidEntry`
reads the two together: inside a fragment, an edge that lands in a row's
block starts in that block, or at the `repZero` in front of it. -/

/-- A fragment defers only inside itself, or to the cell just past its
end. -/
theorem FragAt.targets {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    ∀ pc, lo ≤ pc → pc < hi → ∀ t ∈ hollowTargets code reps pc,
      lo ≤ t ∧ t ≤ hi := by
  induction h with
  | nul | catNil | repNone => intro pc h1 h2 _ _; omega
  | @chr b r0 lo hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [hollowTargets, hcell] at ht
  | @chrCI folded r0 lo hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [hollowTargets, hcell] at ht
  | @cls bits r0 idx lo hcell hblob hsem =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [hollowTargets, hcell] at ht
  | @any r0 lo hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [hollowTargets, hcell] at ht
  | @anyNoNL r0 lo hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [hollowTargets, hcell] at ht
  | @bsr r0 lo hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [hollowTargets, hcell] at ht
  | @assn a' op r0 lo ha hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      have hop : (code[lo]!).op = op := by rw [hcell]
      cases a' <;> simp only [assnOp] at ha <;> try cases ha
      all_goals
        (simp only [hollowTargets, hop, List.mem_singleton] at ht
         omega)
  | @catCons k kids r0 lo mid hi hk hkids ihk ihkids =>
      intro pc h1 h2 t ht
      have hle1 := hk.le
      have hle2 := hkids.le
      rcases Nat.lt_or_ge pc mid with hm | hm
      · have := ihk pc h1 hm t ht
        omega
      · have := ihkids pc hm h2 t ht
        omega
  | @altOne a' r0 lo hi ha iha => exact iha
  | @altCons a' b rest r0 lo j hi hsplit ha hjump hrest iha ihrest =>
      intro pc h1 h2 t ht
      have hle1 := ha.le
      have hle2 := hrest.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega] at ht
        simp only [hollowTargets, hsplit, List.mem_cons, List.not_mem_nil,
          or_false] at ht
        omega
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · have := iha pc hp hp2 t ht
          omega
        · rcases Nat.eq_or_lt_of_le hp2 with hj | hj
          · rw [show pc = j from by omega] at ht
            simp only [hollowTargets, hjump, List.mem_singleton] at ht
            omega
          · have := ihrest pc (by omega) h2 t ht
            omega
  | @grpZero body r0 lo hi hbody ihbody => exact ihbody
  | @grpCap cap body r0 lo j hcap hopen hbody hclose ihbody =>
      intro pc h1 h2 t ht
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega] at ht
        simp only [hollowTargets, hopen, List.mem_singleton] at ht
        omega
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · have := ihbody pc hp hp2 t ht
          omega
        · rw [show pc = j from by omega] at ht
          simp only [hollowTargets, hclose, List.mem_singleton] at ht
          omega
  | @repOne greedy body r0 lo hi hbody ihbody => exact ihbody
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro pc h1 h2 t ht
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (sp + 1) with hp | hp
      · rw [show pc = sp from by omega] at ht
        cases greedy <;>
          (simp only [hollowTargets, hsplit, if_true, Bool.false_eq_true,
             if_false, List.mem_cons, List.not_mem_nil, or_false] at ht
           omega)
      · have := ihbody pc hp h2 t ht
        omega
  | @repGen lo' hi' greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro pc h1 h2 t ht
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega] at ht
        simp only [hollowTargets, hzero, List.mem_singleton] at ht
        omega
      · rcases Nat.lt_or_ge pc (lo + 2) with hp2 | hp2
        · rw [show pc = lo + 1 from by omega] at ht
          simp only [hollowTargets, hloop, hinfo, List.mem_cons,
            List.not_mem_nil, or_false] at ht
          omega
        · rcases Nat.lt_or_ge pc (lo + 3) with hp3 | hp3
          · rw [show pc = lo + 2 from by omega] at ht
            simp only [hollowTargets, henter, List.mem_singleton] at ht
            omega
          · rcases Nat.lt_or_ge pc j with hp4 | hp4
            · have := ihbody pc hp3 hp4 t ht
              omega
            · rw [show pc = j from by omega] at ht
              simp only [hollowTargets, hnext, hinfo, List.mem_cons,
                List.not_mem_nil, or_false] at ht
              omega

/-- Every row a fragment claims sits inside it, `repZero` included. -/
theorem FragAt.blockIn {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    ∀ r, r0 ≤ r → r < r0 + repCount a →
      lo + 1 ≤ (reps[r]!).head ∧ (reps[r]!).after ≤ hi := by
  induction h with
  | nul | chr _ | chrCI _ | cls _ _ _ | any _ | anyNoNL _ | bsr _ =>
      intro r _ hlt
      exfalso
      rw [repCount] at hlt <;> first | omega | simp
  | assn ha _ =>
      intro r _ hlt
      exact absurd (repCount_assn ha ▸ hlt) (by omega)
  | catNil =>
      intro r _ hlt
      exact absurd (repCount_cat_nil ▸ hlt) (by omega)
  | @catCons k kids r0 lo mid hi hk hkids ihk ihkids =>
      intro r hge hlt
      have hle1 := hk.le
      have hle2 := hkids.le
      rw [repCount_cat_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount k) with h1 | h1
      · have := ihk r hge h1
        omega
      · have := ihkids r h1 (by omega)
        omega
  | @altOne a' r0 lo hi ha iha =>
      intro r hge hlt
      rw [repCount_alt_cons, repCount_alt_nil] at hlt
      exact iha r hge (by omega)
  | @altCons a' b rest r0 lo j hi hsplit ha hjump hrest iha ihrest =>
      intro r hge hlt
      have hle1 := ha.le
      have hle2 := hrest.le
      rw [repCount_alt_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount a') with h1 | h1
      · have := iha r hge h1
        omega
      · have := ihrest r h1 (by omega)
        omega
  | @grpZero body r0 lo hi hbody ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | @grpCap cap body r0 lo j hcap hopen hbody hclose ihbody =>
      intro r hge hlt
      have hle := hbody.le
      rw [repCount] at hlt
      have := ihbody r hge hlt
      omega
  | repNone =>
      intro r _ hlt
      exfalso
      rw [repCount] at hlt
      omega
  | @repOne greedy body r0 lo hi hbody ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro r hge hlt
      have hle := hbody.le
      rw [repCount] at hlt
      have := ihbody r hge hlt
      omega
  | @repGen lo' hi' greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro r hge hlt
      have hle := hbody.le
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
      · rw [hinfo]
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · have := ihbody r h1 (by omega)
        omega

/-- No edge into the middle of a block. Inside a fragment, a cell that
defers into one of the fragment's blocks is a cell of that block, or the
`repZero` that opens it. -/
theorem FragAt.noMidEntry {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    ∀ r, r0 ≤ r → r < r0 + repCount a → ∀ pc, lo ≤ pc → pc < hi →
      ∀ t ∈ hollowTargets code reps pc,
        (reps[r]!).head ≤ t → t < (reps[r]!).after →
        (reps[r]!).head - 1 ≤ pc ∧ pc < (reps[r]!).after := by
  induction h with
  | nul | chr _ | chrCI _ | cls _ _ _ | any _ | anyNoNL _ | bsr _ =>
      intro r _ hlt
      exfalso
      rw [repCount] at hlt <;> first | omega | simp
  | assn ha _ =>
      intro r _ hlt
      exact absurd (repCount_assn ha ▸ hlt) (by omega)
  | catNil =>
      intro r _ hlt
      exact absurd (repCount_cat_nil ▸ hlt) (by omega)
  | @catCons k kids r0 lo mid hi hk hkids ihk ihkids =>
      intro r hge hlt pc h1 h2 t ht hh1 hh2
      rw [repCount_cat_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount k) with hr | hr
      · rcases Nat.lt_or_ge pc mid with hp | hp
        · exact ihk r hge hr pc h1 hp t ht hh1 hh2
        · exfalso
          have hb := hk.blockIn r hge hr
          have hc := hkids.targets pc hp h2 t ht
          omega
      · rcases Nat.lt_or_ge pc mid with hp | hp
        · exfalso
          have hb := hkids.blockIn r hr (by omega)
          have hc := hk.targets pc h1 hp t ht
          omega
        · exact ihkids r hr (by omega) pc hp h2 t ht hh1 hh2
  | @altOne a' r0 lo hi ha iha =>
      intro r hge hlt
      rw [repCount_alt_cons, repCount_alt_nil] at hlt
      exact iha r hge (by omega)
  | @altCons a' b rest r0 lo j hi hsplit ha hjump hrest iha ihrest =>
      intro r hge hlt pc h1 h2 t ht hh1 hh2
      have hle1 := ha.le
      have hle2 := hrest.le
      rw [repCount_alt_cons] at hlt
      have hsp : lo ≤ pc → pc < lo + 1 → t = j + 1 ∨ t = lo + 1 := by
        intro _ hb
        rw [show pc = lo from by omega] at ht
        simpa only [hollowTargets, hsplit, List.mem_cons, List.not_mem_nil,
          or_false] using ht
      have hjp : j ≤ pc → pc < j + 1 → t = hi := by
        intro ha' hb
        rw [show pc = j from by omega] at ht
        simpa only [hollowTargets, hjump, List.mem_singleton] using ht
      rcases Nat.lt_or_ge r (r0 + repCount a') with hr | hr
      · have hb := ha.blockIn r hge hr
        rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
        · exact absurd (hsp h1 hp) (by omega)
        · rcases Nat.lt_or_ge pc j with hp2 | hp2
          · exact iha r hge hr pc hp hp2 t ht hh1 hh2
          · rcases Nat.lt_or_ge pc (j + 1) with hp3 | hp3
            · exact absurd (hjp hp2 hp3) (by omega)
            · exfalso
              have hc := hrest.targets pc hp3 h2 t ht
              omega
      · have hb := hrest.blockIn r hr (by omega)
        rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
        · exact absurd (hsp h1 hp) (by omega)
        · rcases Nat.lt_or_ge pc j with hp2 | hp2
          · exfalso
            have hc := ha.targets pc hp hp2 t ht
            omega
          · rcases Nat.lt_or_ge pc (j + 1) with hp3 | hp3
            · exact absurd (hjp hp2 hp3) (by omega)
            · exact ihrest r hr (by omega) pc hp3 h2 t ht hh1 hh2
  | @grpZero body r0 lo hi hbody ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | @grpCap cap body r0 lo j hcap hopen hbody hclose ihbody =>
      intro r hge hlt pc h1 h2 t ht hh1 hh2
      have hle := hbody.le
      rw [repCount] at hlt
      have hb := hbody.blockIn r hge hlt
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · exfalso
        rw [show pc = lo from by omega] at ht
        simp only [hollowTargets, hopen, List.mem_singleton] at ht
        omega
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · exact ihbody r hge hlt pc hp hp2 t ht hh1 hh2
        · exfalso
          rw [show pc = j from by omega] at ht
          simp only [hollowTargets, hclose, List.mem_singleton] at ht
          omega
  | repNone =>
      intro r _ hlt
      exfalso
      rw [repCount] at hlt
      omega
  | @repOne greedy body r0 lo hi hbody ihbody =>
      intro r hge hlt
      rw [repCount] at hlt
      exact ihbody r hge hlt
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro r hge hlt pc h1 h2 t ht hh1 hh2
      have hle := hbody.le
      rw [repCount] at hlt
      have hb := hbody.blockIn r hge hlt
      rcases Nat.lt_or_ge pc (sp + 1) with hp | hp
      · exfalso
        rw [show pc = sp from by omega] at ht
        cases greedy <;>
          (simp only [hollowTargets, hsplit, if_true, Bool.false_eq_true,
             if_false, List.mem_cons, List.not_mem_nil, or_false] at ht
           omega)
      · exact ihbody r hge hlt pc hp h2 t ht hh1 hh2
  | @repGen lo' hi' greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro r hge hlt pc h1 h2 t ht hh1 hh2
      have hle := hbody.le
      have hcount : repCount (.rep lo' hi' greedy body) = 1 + repCount body := by
        cases hi' with
        | none => rw [repCount] <;> simp
        | some v =>
            match v, hnot0, hnot1 with
            | 0, h, _ => exact absurd rfl h
            | 1, _, h => exact absurd rfl h
            | (_ + 2), _, _ => rw [repCount] <;> simp
      rw [hcount] at hlt
      rcases Nat.eq_or_lt_of_le hge with rfl | h3
      · rw [hinfo]
        exact ⟨by show lo + 1 - 1 ≤ pc; omega, by show pc < j + 1; omega⟩
      · have hb := hbody.blockIn r h3 (by omega)
        rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
        · exfalso
          rw [show pc = lo from by omega] at ht
          simp only [hollowTargets, hzero, List.mem_singleton] at ht
          omega
        · rcases Nat.lt_or_ge pc (lo + 2) with hp2 | hp2
          · exfalso
            rw [show pc = lo + 1 from by omega] at ht
            simp only [hollowTargets, hloop, hinfo, List.mem_cons,
              List.not_mem_nil, or_false] at ht
            omega
          · rcases Nat.lt_or_ge pc (lo + 3) with hp3 | hp3
            · exfalso
              rw [show pc = lo + 2 from by omega] at ht
              simp only [hollowTargets, henter, List.mem_singleton] at ht
              omega
            · rcases Nat.lt_or_ge pc j with hp4 | hp4
              · exact ihbody r h3 (by omega) pc hp3 hp4 t ht hh1 hh2
              · exfalso
                rw [show pc = j from by omega] at ht
                simp only [hollowTargets, hnext, hinfo, List.mem_cons,
                  List.not_mem_nil, or_false] at ht
                omega

/-- The address fact read at a whole program: nothing defers into a
repetition's block but the block itself and the `repZero` that opens
it. -/
def NoMidEntry (re : Re) : Prop :=
  ∀ pc t, t ∈ hollowTargets re.code re.reps pc → ∀ r, r < re.reps.size →
    (re.reps[r]!).head ≤ t → t < (re.reps[r]!).after →
      (re.reps[r]!).head - 1 ≤ pc ∧ pc < (re.reps[r]!).after

/-- Reading the fragment induction at the program the root compiled to.
Past the root's own code sit the ENDANCHORED assertion and the accept,
which defer forward or nowhere; every block is behind them, so they
cannot be the way in. -/
theorem noMidEntry_of_root {re : Re} {root : Ast} {M : Nat}
    (hroot : FragAt re.code re.classes re.reps 0 root 0 M)
    (hsize : re.reps.size ≤ repCount root)
    (htail : ∀ pc, M ≤ pc → ∀ t ∈ hollowTargets re.code re.reps pc, M ≤ t) :
    NoMidEntry re := by
  intro pc t ht r hr hh1 hh2
  have hb := hroot.blockIn r (Nat.zero_le _) (by omega)
  rcases Nat.lt_or_ge pc M with hp | hp
  · exact hroot.noMidEntry r (Nat.zero_le _) (by omega) pc (Nat.zero_le _) hp
      t ht hh1 hh2
  · exact absurd (htail pc hp t ht) (by omega)

/-- Past the end of the program every cell reads as the default, which
defers nowhere. -/
private theorem hollowTargets_past {code : Array Inst} {reps : Array RepInfo}
    {pc : Nat} (h : code.size ≤ pc) : hollowTargets code reps pc = [] := by
  rw [hollowTargets, getElem!_neg code pc (by omega)]
  rfl

/-- What `compile` leaves behind the root's own code: the ENDANCHORED
assertion when the option is on, then the accept. -/
private theorem compile_code_eq (p : Pat) :
    (compile p).code =
      if p.opts.endanchored then
        ((compileNode p.root 0 rootSt).code.push ⟨.eod, 0, 0⟩).push
          ⟨.accept, 0, 0⟩
      else (compileNode p.root 0 rootSt).code.push ⟨.accept, 0, 0⟩ := by
  by_cases hend : p.opts.endanchored = true
  · rw [if_pos hend]
    simp only [compile, hend]
    rfl
  · rw [if_neg (by simpa using hend)]
    simp only [compile, eq_false_of_ne_true hend]
    rfl

private theorem compile_code_size (p : Pat) :
    (compile p).code.size =
      if p.opts.endanchored then (compileNode p.root 0 rootSt).code.size + 2
      else (compileNode p.root 0 rootSt).code.size + 1 := by
  rw [compile_code_eq]
  split <;> simp

/-- And so the address fact holds of a whole compiled pattern. -/
theorem compile_noMidEntry {p : Pat} (hc : Covered p.root) :
    NoMidEntry (compile p) := by
  obtain ⟨hfrag, hrsz, hopen, hanch⟩ := compile_shape hc
  refine noMidEntry_of_root hfrag (by omega) ?_
  intro pc hp t ht
  have hsize := compile_code_size p
  rcases Nat.lt_or_ge pc (compile p).code.size with hlt | hge
  · by_cases hend : p.opts.endanchored = true
    · rw [if_pos hend] at hsize
      rcases Nat.lt_or_ge pc ((compileNode p.root 0 rootSt).code.size + 1)
        with h1 | h1
      · rw [show pc = (compileNode p.root 0 rootSt).code.size from by omega,
          hollowTargets, (hanch hend).1] at ht
        simp only [List.mem_singleton] at ht
        omega
      · rw [show pc = (compileNode p.root 0 rootSt).code.size + 1 from by omega,
          hollowTargets, (hanch hend).2] at ht
        simp at ht
    · rw [if_neg (by simpa using hend)] at hsize
      rw [show pc = (compileNode p.root 0 rootSt).code.size from by omega,
        hollowTargets, hopen (eq_false_of_ne_true hend)] at ht
      simp at ht
  · rw [hollowTargets_past hge] at ht
    simp at ht

/-- Every cell of a fragment stands where the compiler put it: each of
the four repetition opcodes at the address its own row names, and every
save inside the ovector. The induction is the edge one again, read down
the other side — this time what each construct pins is its own cells
rather than its own targets. -/
theorem FragAt.cells {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi novec : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    CapsBelow novec a → ∀ pc, lo ≤ pc → pc < hi →
      ((code[pc]!).op = Op.repZero → (code[pc]!).arg < reps.size ∧
        pc + 1 = (reps[(code[pc]!).arg]!).head) ∧
      ((code[pc]!).op = Op.repLoop → (code[pc]!).arg < reps.size ∧
        pc = (reps[(code[pc]!).arg]!).head) ∧
      ((code[pc]!).op = Op.repEnter → (code[pc]!).arg < reps.size ∧
        pc = (reps[(code[pc]!).arg]!).body) ∧
      ((code[pc]!).op = Op.repNext → (code[pc]!).arg < reps.size ∧
        pc = (reps[(code[pc]!).arg]!).after - 1) ∧
      ((code[pc]!).op = Op.save → (code[pc]!).arg < novec) := by
  induction h with
  | nul | catNil | repNone => intro _ pc h1 h2; exact absurd h2 (by omega)
  | @chr b r0 lo hcell | @chrCI b r0 lo hcell | @any r0 lo hcell
  | @anyNoNL r0 lo hcell | @bsr r0 lo hcell =>
      intro _ pc h1 h2
      rw [show pc = lo from by omega, hcell]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun hq => by simp at hq
  | @cls bits r0 idx lo hcell hblob hsem =>
      intro _ pc h1 h2
      rw [show pc = lo from by omega, hcell]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun hq => by simp at hq
  | @assn a' op r0 lo ha hcell =>
      intro _ pc h1 h2
      rw [show pc = lo from by omega, hcell]
      cases a' <;> simp only [assnOp] at ha <;> try cases ha
      all_goals
        (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun hq => by simp at hq)
  | @catCons k kids r0 lo mid hi hk hkids ihk ihkids =>
      intro hcaps pc h1 h2
      obtain ⟨hck, hcr⟩ := capsBelow_cat_cons.mp hcaps
      rcases Nat.lt_or_ge pc mid with hm | hm
      · exact ihk hck pc h1 hm
      · exact ihkids hcr pc hm h2
  | @altOne a' r0 lo hi ha iha =>
      intro hcaps
      exact iha (capsBelow_alt_cons.mp hcaps).1
  | @altCons a' b rest r0 lo j hi hsplit ha hjump hrest iha ihrest =>
      intro hcaps pc h1 h2
      obtain ⟨hca, hcr⟩ := capsBelow_alt_cons.mp hcaps
      have hle1 := ha.le
      have hle2 := hrest.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega, hsplit]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun hq => by simp at hq
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · exact iha hca pc hp hp2
        · rcases Nat.lt_or_ge pc (j + 1) with hp3 | hp3
          · rw [show pc = j from by omega, hjump]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun hq => by simp at hq
          · exact ihrest hcr pc hp3 h2
  | @grpZero body r0 lo hi hbody ihbody =>
      intro hcaps
      rw [CapsBelow] at hcaps
      exact ihbody hcaps.2
  | @grpCap cap body r0 lo j hcap hopen hbody hclose ihbody =>
      intro hcaps pc h1 h2
      rw [CapsBelow] at hcaps
      have hnov := hcaps.1 hcap
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega, hopen]
        exact ⟨fun hq => by simp at hq, fun hq => by simp at hq,
          fun hq => by simp at hq, fun hq => by simp at hq,
          fun _ => by show 2 * cap < novec; omega⟩
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · exact ihbody hcaps.2 pc hp hp2
        · rw [show pc = j from by omega, hclose]
          exact ⟨fun hq => by simp at hq, fun hq => by simp at hq,
            fun hq => by simp at hq, fun hq => by simp at hq,
            fun _ => by show 2 * cap + 1 < novec; omega⟩
  | @repOne greedy body r0 lo hi hbody ihbody =>
      intro hcaps
      rw [CapsBelow] at hcaps
      exact ihbody hcaps
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro hcaps pc h1 h2
      rw [CapsBelow] at hcaps
      rcases Nat.lt_or_ge pc (sp + 1) with hp | hp
      · rw [show pc = sp from by omega]
        cases greedy <;>
          (rw [hsplit]
           simp only [if_true, Bool.false_eq_true, if_false]
           refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun hq => by simp at hq)
      · exact ihbody hcaps pc hp h2
  | @repGen lo' hi' greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro hcaps pc h1 h2
      rw [CapsBelow] at hcaps
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega, hzero]
        exact ⟨fun _ => ⟨hrow, by simp [hinfo]⟩, fun hq => by simp at hq,
          fun hq => by simp at hq, fun hq => by simp at hq,
          fun hq => by simp at hq⟩
      · rcases Nat.lt_or_ge pc (lo + 2) with hp2 | hp2
        · rw [show pc = lo + 1 from by omega, hloop]
          exact ⟨fun hq => by simp at hq, fun _ => ⟨hrow, by simp [hinfo]⟩,
            fun hq => by simp at hq, fun hq => by simp at hq,
            fun hq => by simp at hq⟩
        · rcases Nat.lt_or_ge pc (lo + 3) with hp3 | hp3
          · rw [show pc = lo + 2 from by omega, henter]
            exact ⟨fun hq => by simp at hq,
              fun hq => by simp at hq, fun _ => ⟨hrow, by simp [hinfo]⟩,
              fun hq => by simp at hq, fun hq => by simp at hq⟩
          · rcases Nat.lt_or_ge pc j with hp4 | hp4
            · exact ihbody hcaps pc hp3 hp4
            · rw [show pc = j from by omega, hnext]
              exact ⟨fun hq => by simp at hq,
                fun hq => by simp at hq, fun hq => by simp at hq,
                fun _ => ⟨hrow, by simp [hinfo]⟩, fun hq => by simp at hq⟩

/-- Where the four repetition opcodes may stand, and how far a save may
reach: each repetition cell sits at the address its own row names, and no
capture slot climbs into the counters above the ovector. The compiler
lays the program out that way; the invariants below only read it back. -/
structure CellsOk (re : Re) : Prop where
  zero : ∀ q : Nat, (re.code[q]! : Inst).op = Op.repZero →
    (re.code[q]! : Inst).arg < re.reps.size ∧
      q + 1 = (re.reps[(re.code[q]! : Inst).arg]! : RepInfo).head
  head : ∀ q : Nat, (re.code[q]! : Inst).op = Op.repLoop →
    (re.code[q]! : Inst).arg < re.reps.size ∧
      q = (re.reps[(re.code[q]! : Inst).arg]! : RepInfo).head
  enter : ∀ q : Nat, (re.code[q]! : Inst).op = Op.repEnter →
    (re.code[q]! : Inst).arg < re.reps.size ∧
      q = (re.reps[(re.code[q]! : Inst).arg]! : RepInfo).body
  next : ∀ q : Nat, (re.code[q]! : Inst).op = Op.repNext →
    (re.code[q]! : Inst).arg < re.reps.size ∧
      q = (re.reps[(re.code[q]! : Inst).arg]! : RepInfo).after - 1
  save : ∀ q : Nat, (re.code[q]! : Inst).op = Op.save →
    (re.code[q]! : Inst).arg < re.novec

/-- And the cell fact for a whole compiled pattern. Past the root's own
code sit the ENDANCHORED assertion and the accept, and past the end of
the program every read hands back the default `chr`; none of the three is
a repetition cell or a save. -/
theorem compile_cellsOk {p : Pat} (hc : Covered p.root)
    (hcaps : CapsBelow (2 * (p.ncap + 1)) p.root) : CellsOk (compile p) := by
  obtain ⟨hfrag, hrsz, hopen, hanch⟩ := compile_shape hc
  have hnovec : (compile p).novec = 2 * (p.ncap + 1) := rfl
  have hall : ∀ q : Nat,
      (((compile p).code[q]!).op = Op.repZero →
        ((compile p).code[q]!).arg < (compile p).reps.size ∧
          q + 1 = ((compile p).reps[((compile p).code[q]!).arg]!).head) ∧
      (((compile p).code[q]!).op = Op.repLoop →
        ((compile p).code[q]!).arg < (compile p).reps.size ∧
          q = ((compile p).reps[((compile p).code[q]!).arg]!).head) ∧
      (((compile p).code[q]!).op = Op.repEnter →
        ((compile p).code[q]!).arg < (compile p).reps.size ∧
          q = ((compile p).reps[((compile p).code[q]!).arg]!).body) ∧
      (((compile p).code[q]!).op = Op.repNext →
        ((compile p).code[q]!).arg < (compile p).reps.size ∧
          q = ((compile p).reps[((compile p).code[q]!).arg]!).after - 1) ∧
      (((compile p).code[q]!).op = Op.save →
        ((compile p).code[q]!).arg < (compile p).novec) := by
    intro q
    rcases Nat.lt_or_ge q (compileNode p.root 0 rootSt).code.size with hq | hq
    · exact hfrag.cells (by rw [hnovec]; exact hcaps) q (Nat.zero_le _) hq
    · have hsize := compile_code_size p
      have hcellop : ((compile p).code[q]!).op = Op.accept ∨
          ((compile p).code[q]!).op = Op.eod ∨
          ((compile p).code[q]!).op = Op.chr := by
        rcases Nat.lt_or_ge q (compile p).code.size with hlt | hge
        · by_cases hend : p.opts.endanchored = true
          · rw [if_pos hend] at hsize
            rcases Nat.lt_or_ge q ((compileNode p.root 0 rootSt).code.size + 1)
              with h1 | h1
            · rw [show q = (compileNode p.root 0 rootSt).code.size from by omega,
                (hanch hend).1]
              exact Or.inr (Or.inl rfl)
            · rw [show q = (compileNode p.root 0 rootSt).code.size + 1 from by
                  omega, (hanch hend).2]
              exact Or.inl rfl
          · rw [if_neg (by simpa using hend)] at hsize
            rw [show q = (compileNode p.root 0 rootSt).code.size from by omega,
              hopen (eq_false_of_ne_true hend)]
            exact Or.inl rfl
        · rw [getElem!_neg (compile p).code q (by omega)]
          exact Or.inr (Or.inr rfl)
      refine ⟨fun hq' => ?_, fun hq' => ?_, fun hq' => ?_, fun hq' => ?_,
        fun hq' => ?_⟩ <;>
        (rcases hcellop with h' | h' | h' <;> rw [hq'] at h' <;>
          exact absurd h' (by decide))
  exact ⟨fun q hq => (hall q).1 hq, fun q hq => (hall q).2.1 hq,
    fun q hq => (hall q).2.2.1 hq, fun q hq => (hall q).2.2.2.1 hq,
    fun q hq => (hall q).2.2.2.2 hq⟩

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

/-- Where the closure defers, read at a whole program: forward, to a cell
after itself, with one exception — a `repNext` offers its own block's
body, which is behind it. -/
def EpsForward (re : Re) : Prop :=
  ∀ pc, ∀ t ∈ epsTargets re.code re.reps pc,
    pc < t ∨ ((re.code[pc]! : Inst).op = Op.repNext ∧
      t = (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).body)

/-- Which way a fragment's edges run. Every cell defers forward, with the
`repNext` exception, so a closure that comes back where it started went
round some star's loop-back edge — and `pikeOk_no_eps_loop` is what says
it cannot have. -/
theorem FragAt.epsForward {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    ∀ pc, lo ≤ pc → pc < hi → ∀ t ∈ epsTargets code reps pc,
      pc < t ∨ ((code[pc]!).op = Op.repNext ∧
        t = (reps[(code[pc]!).arg]!).body) := by
  induction h with
  | nul | catNil | repNone => intro pc h1 h2 _ _; omega
  | @chr b r0 lo hcell | @chrCI b r0 lo hcell | @any r0 lo hcell
  | @anyNoNL r0 lo hcell | @bsr r0 lo hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [epsTargets, hcell] at ht
  | @cls bits r0 idx lo hcell hblob hsem =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      simp [epsTargets, hcell] at ht
  | @assn a' op r0 lo ha hcell =>
      intro pc h1 h2 t ht
      rw [show pc = lo from by omega] at ht
      have hop : (code[lo]!).op = op := by rw [hcell]
      cases a' <;> simp only [assnOp] at ha <;> try cases ha
      all_goals
        (simp only [epsTargets, hop, List.mem_singleton] at ht
         omega)
  | @catCons k kids r0 lo mid hi hk hkids ihk ihkids =>
      intro pc h1 h2 t ht
      have hle2 := hkids.le
      rcases Nat.lt_or_ge pc mid with hm | hm
      · exact ihk pc h1 hm t ht
      · exact ihkids pc hm h2 t ht
  | @altOne a' r0 lo hi ha iha => exact iha
  | @altCons a' b rest r0 lo j hi hsplit ha hjump hrest iha ihrest =>
      intro pc h1 h2 t ht
      have hle1 := ha.le
      have hle2 := hrest.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega] at ht
        simp only [epsTargets, hsplit, List.mem_cons, List.not_mem_nil,
          or_false] at ht
        left
        omega
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · exact iha pc hp hp2 t ht
        · rcases Nat.eq_or_lt_of_le hp2 with hj | hj
          · rw [show pc = j from by omega] at ht
            simp only [epsTargets, hjump, List.mem_singleton] at ht
            left
            omega
          · exact ihrest pc (by omega) h2 t ht
  | @grpZero body r0 lo hi hbody ihbody => exact ihbody
  | @grpCap cap body r0 lo j hcap hopen hbody hclose ihbody =>
      intro pc h1 h2 t ht
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega] at ht
        simp only [epsTargets, hopen, List.mem_singleton] at ht
        left
        omega
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · exact ihbody pc hp hp2 t ht
        · rw [show pc = j from by omega] at ht
          simp only [epsTargets, hclose, List.mem_singleton] at ht
          left
          omega
  | @repOne greedy body r0 lo hi hbody ihbody => exact ihbody
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro pc h1 h2 t ht
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (sp + 1) with hp | hp
      · rw [show pc = sp from by omega] at ht
        left
        cases greedy <;>
          (simp only [epsTargets, hsplit, if_true, Bool.false_eq_true, if_false,
             List.mem_cons, List.not_mem_nil, or_false] at ht
           omega)
      · exact ihbody pc hp h2 t ht
  | @repGen lo' hi' greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro pc h1 h2 t ht
      have hle := hbody.le
      rcases Nat.lt_or_ge pc (lo + 1) with hp | hp
      · rw [show pc = lo from by omega] at ht
        simp only [epsTargets, hzero, List.mem_singleton] at ht
        left
        omega
      · rcases Nat.lt_or_ge pc (lo + 2) with hp2 | hp2
        · rw [show pc = lo + 1 from by omega] at ht
          simp only [epsTargets, hloop, hinfo, mem_ite_pair] at ht
          left
          omega
        · rcases Nat.lt_or_ge pc (lo + 3) with hp3 | hp3
          · rw [show pc = lo + 2 from by omega] at ht
            simp only [epsTargets, henter, List.mem_singleton] at ht
            left
            omega
          · rcases Nat.lt_or_ge pc j with hp4 | hp4
            · exact ihbody pc hp3 hp4 t ht
            · rw [show pc = j from by omega] at ht ⊢
              simp only [epsTargets, hnext, hinfo, mem_ite_pair] at ht
              rcases ht with rfl | rfl
              · exact Or.inr ⟨by rw [hnext], by rw [hnext, hinfo]⟩
              · left
                omega

/-- Past the end of the program the closure defers nowhere. -/
private theorem epsTargets_past {code : Array Inst} {reps : Array RepInfo}
    {pc : Nat} (h : code.size ≤ pc) : epsTargets code reps pc = [] := by
  rw [epsTargets, getElem!_neg code pc (by omega)]
  rfl

/-- The same at a whole compiled pattern. What sits past the root's own
code is the ENDANCHORED assertion, which defers to the accept in front of
it, and the accept, which defers nowhere. -/
theorem compile_epsForward {p : Pat} (hc : Covered p.root) :
    EpsForward (compile p) := by
  obtain ⟨hfrag, hrsz, hopen, hanch⟩ := compile_shape hc
  intro pc t ht
  rcases Nat.lt_or_ge pc (compileNode p.root 0 rootSt).code.size with hp | hp
  · exact hfrag.epsForward pc (Nat.zero_le _) hp t ht
  · have hsize := compile_code_size p
    rcases Nat.lt_or_ge pc (compile p).code.size with hlt | hge
    · by_cases hend : p.opts.endanchored = true
      · rw [if_pos hend] at hsize
        rcases Nat.lt_or_ge pc ((compileNode p.root 0 rootSt).code.size + 1)
          with h1 | h1
        · rw [show pc = (compileNode p.root 0 rootSt).code.size from by omega]
            at ht ⊢
          simp only [epsTargets, (hanch hend).1, List.mem_singleton] at ht
          left
          omega
        · rw [show pc = (compileNode p.root 0 rootSt).code.size + 1 from by
              omega] at ht
          simp [epsTargets, (hanch hend).2] at ht
      · rw [if_neg (by simpa using hend)] at hsize
        rw [show pc = (compileNode p.root 0 rootSt).code.size from by omega]
          at ht
        simp [epsTargets, hopen (eq_false_of_ne_true hend)] at ht
    · rw [epsTargets_past hge] at ht
      simp at ht

/-- One walk, read for the loop-back edge it must have taken to go
backward: either it only ever went forward, or some star's `repNext` sent
it to that star's body, with the walk reaching the `repNext` on the way in
and carrying on out of the body. -/
theorem epsReach_back {re : Re} (hcells : CellsOk re) (hfwd : EpsForward re) :
    ∀ {a b : Nat}, EpsReach re.code re.reps a b →
      a ≤ b ∨ ∃ r, r < re.reps.size ∧
        EpsReach re.code re.reps (re.reps[r]!).body b ∧
        EpsReach re.code re.reps a ((re.reps[r]!).after - 1) := by
  intro a b h
  induction h with
  | refl => exact Or.inl (Nat.le_refl _)
  | @step pc mid q hmid hrest ih =>
      rcases hfwd pc mid hmid with hlt | ⟨hop, hbody⟩
      · rcases ih with hle | ⟨r, hr, h1, h2⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨r, hr, h1, .step hmid h2⟩
      · obtain ⟨harg, hafter⟩ := hcells.next pc hop
        exact Or.inr ⟨(re.code[pc]!).arg, harg, hbody ▸ hrest, hafter ▸ .refl⟩

/-- And so no closure walk comes back where it started. One that took a
step and returned would have gone round some star's loop-back edge — the
one edge in the program that runs backward — and from that star's body
its own `repNext` is exactly what `pike_ok` refused. That is the
acyclicity the priority ordering rests on: depth-first in split order
really is the backtracking preference order, and a pc the visited set has
marked is one the closure is done with. -/
theorem epsReach_no_cycle {re : Re} (hok : pikeOk re.code re.reps = true)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hcells : CellsOk re) (hfwd : EpsForward re) {pc mid : Nat}
    (hmid : mid ∈ epsTargets re.code re.reps pc)
    (hback : EpsReach re.code re.reps mid pc) : False := by
  rcases epsReach_back hcells hfwd hback with hle | ⟨r, hr, hb1, hb2⟩
  · rcases hfwd pc mid hmid with hlt | ⟨hop, hbody⟩
    · omega
    · obtain ⟨harg, hafter⟩ := hcells.next pc hop
      exact (pikeOk_no_eps_loop hok hrows harg (hbody ▸ hback)).2 hafter
  · exact (pikeOk_no_eps_loop hok hrows hr (hb1.trans (.step hmid hb2))).2 rfl

/-- The reachability is a partial order, which is the same fact read
between two pcs rather than round one. -/
theorem epsReach_antisymm {re : Re} (hok : pikeOk re.code re.reps = true)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hcells : CellsOk re) (hfwd : EpsForward re) {a b : Nat}
    (h1 : EpsReach re.code re.reps a b)
    (h2 : EpsReach re.code re.reps b a) : a = b := by
  rcases epsReach_back hcells hfwd h1 with hab | ⟨r, hr, hb1, hb2⟩
  · rcases epsReach_back hcells hfwd h2 with hba | ⟨r, hr, hb1, hb2⟩
    · omega
    · exact absurd rfl (pikeOk_no_eps_loop hok hrows hr
        ((hb1.trans h1).trans hb2)).2
  · exact absurd rfl (pikeOk_no_eps_loop hok hrows hr
      ((hb1.trans h2).trans hb2)).2

/-- The same at a compiled pattern, every side condition discharged. -/
theorem compile_epsReach_no_cycle {p : Pat} (hw : Wf p)
    (hpike : (compile p).pike = true) {pc mid : Nat}
    (hmid : mid ∈ epsTargets (compile p).code (compile p).reps pc)
    (hback : EpsReach (compile p).code (compile p).reps mid pc) : False :=
  epsReach_no_cycle (re := compile p) hpike
    (fun _ hi => compile_rows hw.1.covered hi)
    (compile_cellsOk hw.1.covered hw.2) (compile_epsForward hw.1.covered)
    hmid hback

theorem compile_epsReach_antisymm {p : Pat} (hw : Wf p)
    (hpike : (compile p).pike = true) {a b : Nat}
    (h1 : EpsReach (compile p).code (compile p).reps a b)
    (h2 : EpsReach (compile p).code (compile p).reps b a) : a = b :=
  epsReach_antisymm (re := compile p) hpike
    (fun _ hi => compile_rows hw.1.covered hi)
    (compile_cellsOk hw.1.covered hw.2) (compile_epsForward hw.1.covered) h1 h2

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

/-! ## The mirror's non-consuming moves

`pike_hollow` walks a relation the backtracking mirror walks too: every
move `eff` makes without advancing the position is a step of
`hollowTargets`, `repNext`'s return to its deciding head included — which
is why the walk was written to go through the head rather than straight
at the body, and why the two agree here where `epsTargets` and the walk
had to be reconciled. That correspondence is the bridge the machine-level
reading of eligibility needs.

What it buys is the invariant below. `EntryPast` says a recorded entry
position is one already reached, or still the sentinel nothing has
written; `EntryFresh` says that where a repetition's own `repNext` is
still in reach without consuming, the iteration under way did not start
here. Together they are preserved by every move the mirror makes: a
consuming step re-establishes the second from the first outright, a
non-consuming one carries the guard back one step, and `repEnter` — the
one move that writes an entry position — establishes it from eligibility,
since from a star's body its own `repNext` is not reachable at all.

The consequence is the machine-level twin of `frag_rep_body_consumes`:
on an eligible program the mirror's `repNext` always returns to its head,
so the empty-match rule the backtracking matcher runs there is dead code
and a matcher without one loses nothing. -/

/-- Below the wrap a count survives the round trip through the register
file. -/
private theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) :
    (n.toUInt32).toNat = n := by
  simp [Nat.toUInt32, Nat.mod_eq_of_lt h]

set_option maxHeartbeats 1000000 in
/-- Every move the mirror makes without advancing the position is a step
of `pike_hollow`'s walk. -/
theorem eff_hollow_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' : Nat} {regs regs' : Spec.Regs}
    (h : eff re s mo start attempt pc pos regs = .goto pc' pos regs') :
    pc' ∈ hollowTargets re.code re.reps pc := by
  cases hop : (re.code[pc]!).op <;>
    simp only [eff, hop] at h <;>
    simp only [hollowTargets, hop] <;>
    (repeat' split at h) <;> simp_all

set_option maxHeartbeats 1000000 in
/-- And so is either arm of a fork, which never advances one. -/
theorem eff_hollow_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' alt : Nat} {regs : Spec.Regs}
    (h : eff re s mo start attempt pc pos regs = .fork pc' alt) :
    pc' ∈ hollowTargets re.code re.reps pc ∧
      alt ∈ hollowTargets re.code re.reps pc := by
  cases hop : (re.code[pc]!).op <;>
    simp only [eff, hop] at h <;>
    simp only [hollowTargets, hop] <;>
    (repeat' split at h) <;> simp_all

/-- A recorded entry position is one the run has already reached, or the
sentinel nothing has written yet. -/
def EntryPast (re : Re) (pos : Nat) (regs : Spec.Regs) : Prop :=
  ∀ r, r < re.reps.size →
    (regs[re.novec + r * 2 + 1]!).toNat ≤ pos ∨
      regs[re.novec + r * 2 + 1]! = unset32

/-- And where a repetition's own `repNext` is still in reach without
consuming, the iteration under way did not start here. -/
def EntryFresh (re : Re) (pc pos : Nat) (regs : Spec.Regs) : Prop :=
  ∀ r, r < re.reps.size →
    HollowReach re.code re.reps pc ((re.reps[r]!).after - 1) →
      regs[re.novec + r * 2 + 1]! ≠ pos.toUInt32

theorem unset32_toNat : (unset32).toNat = 2 ^ 32 - 1 := by decide

private theorem absurd_fail {P : Prop} {pc' pos' : Nat} {regs' : Spec.Regs}
    (h : (Eff.fail) = .goto pc' pos' regs') : P := by cases h

private theorem absurd_fork {P : Prop} {a b pc' pos' : Nat}
    {regs' : Spec.Regs} (h : (Eff.fork a b) = .goto pc' pos' regs') : P := by
  cases h

private theorem absurd_give {P : Prop} {t : Spec.Thread} {pc' pos' : Nat}
    {regs' : Spec.Regs} (h : (Eff.give t) = .goto pc' pos' regs') : P := by
  cases h

private theorem absurd_goto' {P : Prop} {a b x y : Nat} {rg : Spec.Regs}
    (h : (Eff.goto a b rg) = .fork x y) : P := by cases h

private theorem absurd_fail' {P : Prop} {x y : Nat}
    (h : (Eff.fail) = .fork x y) : P := by cases h

private theorem absurd_give' {P : Prop} {t : Spec.Thread} {x y : Nat}
    (h : (Eff.give t) = .fork x y) : P := by cases h

set_option maxHeartbeats 1000000 in
/-- The mirror never resizes a register file. -/
theorem eff_size {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (h : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    regs'.size = regs.size := by
  cases hop : (re.code[pc]!).op <;> simp only [eff, hop] at h <;>
    (repeat' split at h) <;>
    first
      | exact absurd_fail h
      | exact absurd_fork h
      | exact absurd_give h
      | (injection h with _ _ h5
         subst h5
         simp)

/-- Nothing an eligible program can stand at is a `\R`, past the end of
the code included: the cell a read off the end hands back is a `chr`. -/
private theorem op_ne_bsr {re : Re} (hok : pikeOk re.code re.reps = true)
    (pc : Nat) : (re.code[pc]! : Inst).op ≠ Op.bsr := by
  rcases Nat.lt_or_ge pc re.code.size with h | h
  · exact pikeOk_no_bsr hok h
  · rw [getElem!_neg re.code pc (by omega)]
    decide

set_option maxHeartbeats 2000000 in
/-- The invariant, preserved by one move. A consuming step re-establishes
`EntryFresh` from `EntryPast` outright, since the position it arrives at
is one no entry has recorded; a non-consuming one carries the guard back
a step; and `repEnter`, the one move that records an entry position,
kills the guard outright, because from a star's body its own `repNext` is
not reachable without consuming. -/
theorem eff_entry_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hpos : pos < 2 ^ 31)
    (hsz : re.novec + 2 * re.reps.size ≤ regs.size)
    (h1 : EntryPast re pos regs) (h2 : EntryFresh re pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    EntryPast re pos' regs' ∧ EntryFresh re pc' pos' regs' := by
  have hreach : pos' = pos → pc' ∈ hollowTargets re.code re.reps pc := by
    intro hp
    subst hp
    exact eff_hollow_goto heff
  have hstill : pos' = pos →
      (∀ r, r < re.reps.size →
        regs'[re.novec + r * 2 + 1]! = regs[re.novec + r * 2 + 1]!) →
      EntryPast re pos' regs' ∧ EntryFresh re pc' pos' regs' := by
    intro hp hu
    subst hp
    exact ⟨fun r hr => by rw [hu r hr]; exact h1 r hr,
      fun r hr hR => by rw [hu r hr]; exact h2 r hr (.step (hreach rfl) hR)⟩
  have hate : pos' = pos + 1 → regs' = regs →
      EntryPast re pos' regs' ∧ EntryFresh re pc' pos' regs' := by
    intro hp hr
    subst hp
    subst hr
    refine ⟨fun r hr => ?_, fun r hr _ => ?_⟩
    · rcases h1 r hr with hle | hun
      · exact Or.inl (by omega)
      · exact Or.inr hun
    · intro heq
      have hv := congrArg UInt32.toNat heq
      rw [toNat_ofNat32 (by omega)] at hv
      rcases h1 r hr with hle | hun
      · omega
      · rw [hun, unset32_toNat] at hv
        omega
  cases hop : (re.code[pc]!).op <;> simp only [eff, hop] at heff
  case bsr => exact absurd hop (op_ne_bsr hok pc)
  case chr | chrCI | cls | any | anyNoNL =>
      split at heff
      · injection heff with _ h4 h5
        exact hate h4.symm h5.symm
      · exact absurd_fail heff
  case split => exact absurd_fork heff
  case accept =>
      split at heff
      · exact absurd_fail heff
      · exact absurd_give heff
  case save =>
      injection heff with _ h4 h5
      refine hstill h4.symm (fun r hr => ?_)
      rw [← h5]
      exact getBang_set_other regs _ (by have := hcells.save pc hop; omega)
  case repZero =>
      injection heff with _ h4 h5
      refine hstill h4.symm (fun r hr => ?_)
      rw [← h5]
      exact getBang_set_other regs _ (by omega)
  case repNext =>
      split at heff <;>
        (injection heff with _ h4 h5
         refine hstill h4.symm (fun r hr => ?_)
         rw [← h5]
         exact getBang_set_other regs _ (by omega))
  case repEnter =>
      obtain ⟨harg, hbody⟩ := hcells.enter pc hop
      injection heff with h3 h4 h5
      subst h4
      refine ⟨fun r hr => ?_, fun r hr hR => ?_⟩
      · by_cases hra : r = (re.code[pc]!).arg
        · subst hra
          rw [← h5, getBang_set_self _ (by omega)]
          exact Or.inl (by rw [toNat_ofNat32 (by omega)]; omega)
        · rw [← h5, getBang_set_other regs _ (by omega)]
          exact h1 r hr
      · by_cases hra : r = (re.code[pc]!).arg
        · exfalso
          subst hra
          exact (pikeOk_star hok harg).2.2 _
            (hbody ▸ HollowReach.step (hreach rfl) hR) |>.2 rfl
        · rw [← h5, getBang_set_other regs _ (by omega)]
          exact h2 r hr (.step (hreach rfl) hR)
  case jump | repLoop | circ | circM | doll | dollE | dollM | sod | eod
     | eodn | wordB | notWordB =>
      repeat' split at heff
      all_goals first
        | exact absurd_fail heff
        | exact absurd_fork heff
        | (injection heff with _ h4 h5
           exact hstill h4.symm (fun r _ => by rw [← h5]))

/-- The same for a fork, which never advances the position and never
writes. -/
theorem eff_entry_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' alt : Nat} {regs : Spec.Regs}
    (h2 : EntryFresh re pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .fork pc' alt) :
    EntryFresh re pc' pos regs ∧ EntryFresh re alt pos regs := by
  obtain ⟨hp, ha⟩ := eff_hollow_fork heff
  exact ⟨fun r hr hR => h2 r hr (.step hp hR),
    fun r hr hR => h2 r hr (.step ha hR)⟩

/-- The payoff, and the machine-level twin of `frag_rep_body_consumes`:
on an eligible program the mirror at a repetition's own `repNext` always
returns to the deciding head. The empty-match rule the backtracking
matcher runs there is dead code, which is exactly what lets a matcher
without one agree with it. -/
theorem eff_repNext_loops {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {regs : Spec.Regs}
    (hop : (re.code[pc]! : Inst).op = Op.repNext)
    (harg : (re.code[pc]! : Inst).arg < re.reps.size)
    (hgoal : pc = (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).after - 1)
    (h2 : EntryFresh re pc pos regs) :
    eff re s mo start attempt pc pos regs =
      .goto (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).head pos
        (regs.set! (re.novec + (re.code[pc]! : Inst).arg * 2)
          (regs[re.novec + (re.code[pc]! : Inst).arg * 2]! + 1)) := by
  have hne : ¬ (pos.toUInt32 =
      regs[re.novec + (re.code[pc]! : Inst).arg * 2 + 1]!) := by
    intro he
    exact h2 _ harg (hgoal ▸ HollowReach.refl) he.symm
  simp only [eff, hop]
  rw [if_neg (by simp [hne])]

/-! ## The count at the deciding head

The last register the mirror reads to decide anything is a repetition's
counter, and `repLoop` asks it two questions: whether the count is still
below the minimum — vacuous on a pure star — and whether it has reached
the high bound, which on a pure star is the `none32` sentinel, so what is
really being asked is whether the count was ever written. It was.
`repZero` writes it in the cell in front of the block, and `NoMidEntry`
says nothing else defers into a block, so a configuration standing inside
one stands downstream of that write.

`CountPast` carries the fact, and claims a little more than the test
needs, because the bump at `repNext` has to stay clear of the sentinel
too. Before the round's `repEnter` it holds a count no larger than the
position stood at; after it, a count no larger than the position the
round began at, which `EntryPast` reads back as the same bound.
`EntryFresh` then makes that second one strict — the round did not start
here — so the bump lands below the position and the sentinel stays out of
reach. -/

/-- Below the wrap a bump on the register file is a bump on the count. -/
private theorem toNat_succ32 {x : UInt32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

/-- What one row asks of a configuration: before the round's `repEnter`,
a count no larger than the position stood at; after it, a count no larger
than the position the round began at, with that position on record. -/
def CountAt (re : Re) (r pc pos : Nat) (regs : Spec.Regs) : Prop :=
  (pc ≤ (re.reps[r]!).body → (regs[re.novec + r * 2]!).toNat ≤ pos) ∧
  ((re.reps[r]!).body < pc →
    regs[re.novec + r * 2 + 1]! ≠ unset32 ∧
      (regs[re.novec + r * 2]!).toNat ≤ (regs[re.novec + r * 2 + 1]!).toNat)

/-- The count every live row carries. -/
def CountPast (re : Re) (pc pos : Nat) (regs : Spec.Regs) : Prop :=
  ∀ r, r < re.reps.size → (re.reps[r]!).head ≤ pc → pc < (re.reps[r]!).after →
    CountAt re r pc pos regs

/-- Either way round, a live count is one the run has already reached: the
entry position a round recorded is itself behind the position. -/
theorem CountPast.le {re : Re} {pc pos : Nat} {regs : Spec.Regs}
    (h : CountPast re pc pos regs) (h1 : EntryPast re pos regs) {r : Nat}
    (hr : r < re.reps.size) (hge : (re.reps[r]!).head ≤ pc)
    (hlt : pc < (re.reps[r]!).after) :
    (regs[re.novec + r * 2]!).toNat ≤ pos := by
  rcases Nat.lt_or_ge (re.reps[r]!).body pc with hb | hb
  · obtain ⟨hne, hle⟩ := (h r hr hge hlt).2 hb
    rcases h1 r hr with h' | h'
    · omega
    · exact absurd h' hne
  · exact (h r hr hge hlt).1 hb

/-- A cell that is none of a row's three writing cells stands inside that
row's block already, and past the round's own `repEnter`. -/
private theorem count_stay {re : Re} {pc r : Nat}
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hr : r < re.reps.size) (hz : re.code[pc]! ≠ ⟨.repZero, r, 0⟩)
    (hl : re.code[pc]! ≠ ⟨.repLoop, r, 0⟩)
    (he : re.code[pc]! ≠ ⟨.repEnter, r, 0⟩)
    (hge : (re.reps[r]!).head - 1 ≤ pc) :
    (re.reps[r]!).head ≤ pc ∧ (re.reps[r]!).body < pc := by
  have hrow := hrows r hr
  have hq1 : pc ≠ (re.reps[r]!).head - 1 :=
    fun hq => hz (by rw [hq]; exact hrow.zero)
  have hq2 : pc ≠ (re.reps[r]!).head :=
    fun hq => hl (by rw [hq]; exact hrow.head)
  have hq3 : pc ≠ (re.reps[r]!).body :=
    fun hq => he (by rw [hq]; exact hrow.enter)
  have := hrow.low
  have := hrow.body
  omega

/-- Where a move can have come from: an edge of the walk, or the cell in
front of the one it lands on. -/
private theorem count_back {re : Re} {pc q r : Nat} (hmid : NoMidEntry re)
    (hq : q ∈ hollowTargets re.code re.reps pc ∨ q = pc + 1)
    (hr : r < re.reps.size) (ha : (re.reps[r]!).head ≤ q)
    (hb : q < (re.reps[r]!).after) :
    (re.reps[r]!).head - 1 ≤ pc ∧ pc < (re.reps[r]!).after := by
  rcases hq with hq | rfl
  · exact hmid pc q hq r hr ha hb
  · exact ⟨by omega, by omega⟩

/-- One row carried across a move that neither enters its block nor writes
either of its slots. -/
private theorem count_carry {re : Re} {pc pos pcT posT r : Nat}
    {regs regsT : Spec.Regs}
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (h1 : EntryPast re pos regs)
    (h3 : CountPast re pc pos regs)
    (hedge : pcT ∈ hollowTargets re.code re.reps pc ∨ pcT = pc + 1)
    (hr : r < re.reps.size) (hge : (re.reps[r]!).head ≤ pcT)
    (hlt : pcT < (re.reps[r]!).after)
    (hz : re.code[pc]! ≠ ⟨.repZero, r, 0⟩)
    (hl : re.code[pc]! ≠ ⟨.repLoop, r, 0⟩)
    (he : re.code[pc]! ≠ ⟨.repEnter, r, 0⟩)
    (hk1 : regsT[re.novec + r * 2]! = regs[re.novec + r * 2]!)
    (hk2 : regsT[re.novec + r * 2 + 1]! = regs[re.novec + r * 2 + 1]!)
    (hle : pos ≤ posT) : CountAt re r pcT posT regsT := by
  obtain ⟨hb1, hb2⟩ := count_back hmid hedge hr hge hlt
  obtain ⟨hin, hbody⟩ := count_stay hrows hr hz hl he hb1
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [hk1]
    exact Nat.le_trans (h3.le h1 hr hin hb2) hle
  · rw [hk1, hk2]
    exact (h3 r hr hin hb2).2 hbody

/-- And a whole configuration carried across such a move. -/
private theorem count_frame {re : Re} {pc pos pcT posT : Nat}
    {regs regsT : Spec.Regs}
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (h1 : EntryPast re pos regs)
    (h3 : CountPast re pc pos regs)
    (hedge : pcT ∈ hollowTargets re.code re.reps pc ∨ pcT = pc + 1)
    (hne : ∀ r, r < re.reps.size → re.code[pc]! ≠ ⟨.repZero, r, 0⟩ ∧
      re.code[pc]! ≠ ⟨.repLoop, r, 0⟩ ∧ re.code[pc]! ≠ ⟨.repEnter, r, 0⟩)
    (hkeep : ∀ r, r < re.reps.size →
      regsT[re.novec + r * 2]! = regs[re.novec + r * 2]! ∧
        regsT[re.novec + r * 2 + 1]! = regs[re.novec + r * 2 + 1]!)
    (hle : pos ≤ posT) : CountPast re pcT posT regsT := by
  intro r hr hge hlt
  obtain ⟨hz, hl, he⟩ := hne r hr
  obtain ⟨hk1, hk2⟩ := hkeep r hr
  exact count_carry hrows hmid h1 h3 hedge hr hge hlt hz hl he hk1 hk2 hle

/-- An opcode that is none of the three settles all three refusals at
once. -/
private theorem count_notRep {re : Re} {pc : Nat} {o : Op}
    (ho : (re.code[pc]!).op = o) (hz : o ≠ .repZero) (hl : o ≠ .repLoop)
    (he : o ≠ .repEnter) : ∀ r, r < re.reps.size →
    re.code[pc]! ≠ ⟨.repZero, r, 0⟩ ∧ re.code[pc]! ≠ ⟨.repLoop, r, 0⟩ ∧
      re.code[pc]! ≠ ⟨.repEnter, r, 0⟩ := by
  intro r _
  exact ⟨fun hq => hz (by rw [hq] at ho; exact ho.symm),
    fun hq => hl (by rw [hq] at ho; exact ho.symm),
    fun hq => he (by rw [hq] at ho; exact ho.symm)⟩

/-- The deciding head's own two arms. The exit leaves the block, and the
body entry is reached with the count still the one the head just read. -/
private theorem count_head {re : Re} {pc pos q : Nat} {regs : Spec.Regs}
    (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (h1 : EntryPast re pos regs)
    (h3 : CountPast re pc pos regs)
    (hop : (re.code[pc]! : Inst).op = Op.repLoop)
    (hq : q = (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).after ∨
      q = (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).body) :
    CountPast re q pos regs := by
  obtain ⟨harg, hheadq⟩ := hcells.head pc hop
  have hrow := hrows _ harg
  have hroom := hrow.room
  have hbd := hrow.body
  intro r hr hge hlt
  by_cases hra : r = (re.code[pc]!).arg
  · subst hra
    rcases hq with rfl | rfl
    · exact absurd hlt (by omega)
    · exact ⟨fun _ => h3.le h1 hr (by omega) (by omega),
        fun hq' => absurd hq' (by omega)⟩
  · refine count_carry hrows hmid h1 h3 (Or.inl ?_) hr hge hlt
      (fun hz => hra (by rw [hz])) (fun hz => hra (by rw [hz]))
      (fun hz => hra (by rw [hz])) rfl rfl (Nat.le_refl _)
    simp only [hollowTargets, hop, List.mem_cons, List.not_mem_nil, or_false]
    exact hq

set_option maxHeartbeats 4000000 in
/-- The count invariant, preserved by one move. Away from the three cells
a block writes through, the move can only be carrying a count that was
already live, because it cannot have entered a block anywhere but at its
`repZero` nor crossed a round's `repEnter`. At those three cells the row
is the one the instruction names: `repZero` plants a zero, `repEnter`
records the position the round begins at, and `repNext` bumps the count
past a position the round has already left behind. -/
theorem eff_count_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hpos : pos < 2 ^ 31)
    (hsz : re.novec + 2 * re.reps.size ≤ regs.size)
    (h1 : EntryPast re pos regs) (h2 : EntryFresh re pc pos regs)
    (h3 : CountPast re pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    CountPast re pc' pos' regs' := by
  cases hop : (re.code[pc]!).op <;> simp only [eff, hop] at heff
  case bsr => exact absurd hop (op_ne_bsr hok pc)
  case split => exact absurd_fork heff
  case accept =>
      split at heff
      · exact absurd_fail heff
      · exact absurd_give heff
  case chr | chrCI | cls | any | anyNoNL =>
      split at heff
      · injection heff with h4 h5 h6
        subst h4
        subst h5
        subst h6
        exact count_frame hrows hmid h1 h3 (Or.inr rfl)
          (count_notRep hop (by decide) (by decide) (by decide))
          (fun _ _ => ⟨rfl, rfl⟩) (by omega)
      · exact absurd_fail heff
  case jump =>
      injection heff with h4 h5 h6
      subst h4
      subst h5
      subst h6
      refine count_frame hrows hmid h1 h3 (Or.inl ?_)
        (count_notRep hop (by decide) (by decide) (by decide))
        (fun _ _ => ⟨rfl, rfl⟩) (Nat.le_refl _)
      simp [hollowTargets, hop]
  case save =>
      injection heff with h4 h5 h6
      subst h4
      subst h5
      subst h6
      have hlow := hcells.save pc hop
      exact count_frame hrows hmid h1 h3 (Or.inr rfl)
        (count_notRep hop (by decide) (by decide) (by decide))
        (fun r _ => ⟨getBang_set_other regs _ (by omega),
          getBang_set_other regs _ (by omega)⟩) (Nat.le_refl _)
  case circ | circM | doll | dollE | dollM | sod | eod | eodn | wordB
     | notWordB =>
      repeat' split at heff
      all_goals first
        | exact absurd_fail heff
        | (injection heff with h4 h5 h6
           subst h4
           subst h5
           subst h6
           exact count_frame hrows hmid h1 h3 (Or.inr rfl)
             (count_notRep hop (by decide) (by decide) (by decide))
             (fun _ _ => ⟨rfl, rfl⟩) (Nat.le_refl _))
  case repZero =>
      obtain ⟨harg, hhead⟩ := hcells.zero pc hop
      have hbd := (hrows _ harg).body
      injection heff with h4 h5 h6
      subst h4
      subst h5
      subst h6
      intro r hr hge hlt
      by_cases hra : r = (re.code[pc]!).arg
      · subst hra
        refine ⟨fun _ => ?_, fun hq => absurd hq (by omega)⟩
        rw [getBang_set_self regs (by omega)]
        simp
      · exact count_carry hrows hmid h1 h3 (Or.inr rfl) hr hge hlt
          (fun hq => hra (by rw [hq])) (fun hq => hra (by rw [hq]))
          (fun hq => hra (by rw [hq]))
          (getBang_set_other regs _ (by omega))
          (getBang_set_other regs _ (by omega)) (Nat.le_refl _)
  case repEnter =>
      obtain ⟨harg, hbodyq⟩ := hcells.enter pc hop
      have hrow := hrows _ harg
      have hbd := hrow.body
      have hroom := hrow.room
      injection heff with h4 h5 h6
      subst h4
      subst h5
      subst h6
      intro r hr hge hlt
      by_cases hra : r = (re.code[pc]!).arg
      · subst hra
        have hcnt := h3.le h1 hr (by omega) (by omega)
        refine ⟨fun hq => absurd hq (by omega), fun _ => ⟨?_, ?_⟩⟩
        · rw [getBang_set_self regs (by omega)]
          intro hq
          have hv := congrArg UInt32.toNat hq
          rw [toNat_ofNat32 (by omega), unset32_toNat] at hv
          omega
        · rw [getBang_set_self regs (by omega),
            getBang_set_other regs _ (by omega), toNat_ofNat32 (by omega)]
          exact hcnt
      · exact count_carry hrows hmid h1 h3 (Or.inr rfl) hr hge hlt
          (fun hq => hra (by rw [hq])) (fun hq => hra (by rw [hq]))
          (fun hq => hra (by rw [hq]))
          (getBang_set_other regs _ (by omega))
          (getBang_set_other regs _ (by omega)) (Nat.le_refl _)
  case repLoop =>
      repeat' split at heff
      all_goals first
        | exact absurd_fork heff
        | (injection heff with h4 h5 h6
           subst h4
           subst h5
           subst h6
           exact count_head hcells hrows hmid h1 h3 hop
             (by first | exact Or.inl rfl | exact Or.inr rfl))
  case repNext =>
      obtain ⟨harg, hnextq⟩ := hcells.next pc hop
      have hrow := hrows _ harg
      have hbd := hrow.body
      have hroom := hrow.room
      obtain ⟨hentne, hentle⟩ := (h3 _ harg (by omega) (by omega)).2 (by omega)
      have hentpos : (regs[re.novec + (re.code[pc]!).arg * 2 + 1]!).toNat
          ≤ pos := by
        rcases h1 _ harg with h' | h'
        · exact h'
        · exact absurd h' hentne
      have hstrict : (regs[re.novec + (re.code[pc]!).arg * 2 + 1]!).toNat
          < pos := by
        rcases Nat.lt_or_ge (regs[re.novec + (re.code[pc]!).arg * 2 + 1]!).toNat
          pos with h' | h'
        · exact h'
        · exact absurd (UInt32.toNat_inj.mp
            (by rw [toNat_ofNat32 (show pos < 2 ^ 32 by omega)]; omega))
            (h2 _ harg (hnextq ▸ HollowReach.refl))
      have hbump : ((regs.set! (re.novec + (re.code[pc]!).arg * 2)
            (regs[re.novec + (re.code[pc]!).arg * 2]! + 1))[
              re.novec + (re.code[pc]!).arg * 2]!).toNat
          = (regs[re.novec + (re.code[pc]!).arg * 2]!).toNat + 1 := by
        rw [getBang_set_self regs (by omega)]
        exact toNat_succ32 (by omega)
      have hedge : ∀ q, q = (re.reps[(re.code[pc]!).arg]!).after ∨
          q = (re.reps[(re.code[pc]!).arg]!).head →
          q ∈ hollowTargets re.code re.reps pc := by
        intro q hq
        simp only [hollowTargets, hop, List.mem_cons, List.not_mem_nil,
          or_false]
        exact hq
      have hcase : ∀ q, q = (re.reps[(re.code[pc]!).arg]!).after ∨
          q = (re.reps[(re.code[pc]!).arg]!).head →
          CountPast re q pos (regs.set! (re.novec + (re.code[pc]!).arg * 2)
            (regs[re.novec + (re.code[pc]!).arg * 2]! + 1)) := by
        intro q hq r hr hge hlt
        by_cases hra : r = (re.code[pc]!).arg
        · subst hra
          rcases hq with rfl | rfl
          · exact absurd hlt (by omega)
          · exact ⟨fun _ => by rw [hbump]; omega,
              fun hq' => absurd hq' (by omega)⟩
        · exact count_carry hrows hmid h1 h3 (Or.inl (hedge q hq)) hr hge hlt
            (fun hz => hra (by rw [hz])) (fun hz => hra (by rw [hz]))
            (fun hz => hra (by rw [hz]))
            (getBang_set_other regs _ (by omega))
            (getBang_set_other regs _ (by omega)) (Nat.le_refl _)
      split at heff <;>
        (injection heff with h4 h5 h6
         subst h4
         subst h5
         subst h6
         first
           | exact hcase _ (Or.inl rfl)
           | exact hcase _ (Or.inr rfl))

/-- The same across a fork, which neither advances the position nor
writes. Both arms are edges of the walk, and the only fork that names a
row is the deciding head's own. -/
theorem eff_count_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' alt : Nat} {regs : Spec.Regs}
    (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (h1 : EntryPast re pos regs)
    (h3 : CountPast re pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .fork pc' alt) :
    CountPast re pc' pos regs ∧ CountPast re alt pos regs := by
  cases hop : (re.code[pc]!).op <;> simp only [eff, hop] at heff
  case split =>
      injection heff with h4 h5
      subst h4
      subst h5
      constructor <;>
        (refine count_frame hrows hmid h1 h3 (Or.inl ?_)
           (count_notRep hop (by decide) (by decide) (by decide))
           (fun _ _ => ⟨rfl, rfl⟩) (Nat.le_refl _)
         simp [hollowTargets, hop])
  case repLoop =>
      repeat' split at heff
      all_goals first
        | exact absurd_goto' heff
        | (injection heff with h4 h5
           subst h4
           subst h5
           exact ⟨count_head hcells hrows hmid h1 h3 hop
               (by first | exact Or.inl rfl | exact Or.inr rfl),
             count_head hcells hrows hmid h1 h3 hop
               (by first | exact Or.inl rfl | exact Or.inr rfl)⟩)
  all_goals (repeat' split at heff)
  all_goals first
    | exact absurd_goto' heff
    | exact absurd_fail' heff
    | exact absurd_give' heff

/-- The counter clause, and the twin of `eff_repNext_loops`: where the
invariants hold, the mirror at an eligible program's deciding head always
forks. `cnt < lo`
is `cnt < 0` on a pure star, and `cnt ≥ hi` asks whether the count has
reached the `none32` sentinel, which `CountPast` puts a whole subject's
length out of reach of. So neither test the head runs can tell two
threads standing there apart. -/
theorem eff_repLoop_forks {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {regs : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hop : (re.code[pc]! : Inst).op = Op.repLoop) (hpos : pos < 2 ^ 31)
    (h1 : EntryPast re pos regs) (h3 : CountPast re pc pos regs) :
    eff re s mo start attempt pc pos regs =
      (if (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).greedy then
        .fork (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).body
          (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).after
      else
        .fork (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).after
          (re.reps[(re.code[pc]! : Inst).arg]! : RepInfo).body) := by
  obtain ⟨harg, hhead⟩ := hcells.head pc hop
  obtain ⟨hlo, hhi, _⟩ := pikeOk_star hok harg
  have hroom := (hrows _ harg).room
  have hcnt := h3.le h1 harg (by omega) (by omega)
  simp only [eff, hop]
  rw [if_neg (by omega), if_neg (by rw [hhi]; simp only [none32]; omega)]

/-! ## The dedup lemma, one move at a time

Two threads that meet at the same pc and the same position differ only in
the register file they carry, and the point of everything above is that
the mirror's control flow cannot tell them apart. `Steady` bundles the
three invariants that make it so — a recorded entry position already
reached, no round started here where its own `repNext` is still in reach,
and a count that never reaches the sentinel — and `eff_ctrl_congr` reads
off the consequence: at a steady configuration the move the mirror makes
is a function of the pc and the position alone. Every other test in `eff`
reads the subject, the options or the position, never a register. -/

/-- Everything the mirror's control flow reads out of a register file,
held in check. -/
def Steady (re : Re) (pc pos : Nat) (regs : Spec.Regs) : Prop :=
  EntryPast re pos regs ∧ EntryFresh re pc pos regs ∧ CountPast re pc pos regs

/-- Steadiness survives a move. -/
theorem eff_steady_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hpos : pos < 2 ^ 31)
    (hsz : re.novec + 2 * re.reps.size ≤ regs.size)
    (hs : Steady re pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    Steady re pc' pos' regs' :=
  ⟨(eff_entry_goto hok hcells hpos hsz hs.1 hs.2.1 heff).1,
    (eff_entry_goto hok hcells hpos hsz hs.1 hs.2.1 heff).2,
    eff_count_goto hok hcells hrows hmid hpos hsz hs.1 hs.2.1 hs.2.2 heff⟩

/-- And a fork, which hands it to both arms. -/
theorem eff_steady_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' alt : Nat} {regs : Spec.Regs}
    (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hs : Steady re pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .fork pc' alt) :
    Steady re pc' pos regs ∧ Steady re alt pos regs :=
  ⟨⟨hs.1, (eff_entry_fork hs.2.1 heff).1,
      (eff_count_fork hcells hrows hmid hs.1 hs.2.2 heff).1⟩,
    ⟨hs.1, (eff_entry_fork hs.2.1 heff).2,
      (eff_count_fork hcells hrows hmid hs.1 hs.2.2 heff).2⟩⟩

/-- What one move does to the control state alone: where it goes, and how
far along the subject, with the register file it carries left out. -/
inductive Ctrl where
  | goto (pc pos : Nat)
  | fork (pc alt : Nat)
  | fail
  | give (pos : Nat)
  | stuck
deriving DecidableEq

def Eff.ctrl : Eff → Ctrl
  | .goto pc pos _ => .goto pc pos
  | .fork pc alt => .fork pc alt
  | .fail => .fail
  | .give t => .give t.pos
  | .stuck => .stuck

/-- The dedup lemma, one move at a time: at a steady configuration the
control half of the mirror's next move — where it goes and how far along
the subject — is the same whatever register file it carries, though the
file it hands on of course is not. The two repetition cells are the only
ones that read a register to decide anything, and eligibility has
answered both: the deciding head always forks, and a `repNext` always
returns to it. -/
theorem eff_ctrl_congr {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {regs u : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hpos : pos < 2 ^ 31) (hs : Steady re pc pos regs)
    (hu : Steady re pc pos u) :
    (eff re s mo start attempt pc pos regs).ctrl =
      (eff re s mo start attempt pc pos u).ctrl := by
  cases hop : (re.code[pc]!).op
  case repLoop =>
      rw [eff_repLoop_forks hok hcells hrows hop hpos hs.1 hs.2.2,
        eff_repLoop_forks hok hcells hrows hop hpos hu.1 hu.2.2]
  case repNext =>
      obtain ⟨harg, hnextq⟩ := hcells.next pc hop
      rw [eff_repNext_loops hop harg hnextq hs.2.1,
        eff_repNext_loops hop harg hnextq hu.2.1]
      rfl
  all_goals
    (simp only [eff, hop]
     repeat' split
     all_goals rfl)

/-- A move never leaves the subject: the leaves that advance the position
are guarded by the very test that keeps them inside it, and `\R`, the one
leaf that advances by more than a byte, an eligible program does not
spell. -/
theorem eff_pos_le {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hp : pos ≤ s.size)
    (heff : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    pos' ≤ s.size := by
  cases hop : (re.code[pc]!).op <;> simp only [eff, hop] at heff
  case bsr => exact absurd hop (op_ne_bsr hok pc)
  case chr | chrCI | cls | any | anyNoNL =>
      split at heff
      · rename_i hcond
        injection heff with _ h5 _
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        omega
      · exact absurd_fail heff
  all_goals (repeat' split at heff)
  all_goals first
    | exact absurd_fail heff
    | exact absurd_fork heff
    | exact absurd_give heff
    | (injection heff with _ h5 _
       omega)

/-- What a configuration has to satisfy for the dedup argument to reach
it: a position inside the subject, a register file long enough to hold
the counters, and the three invariants. -/
def Fit (re : Re) (s : ByteArray) (pc pos : Nat) (regs : Spec.Regs) : Prop :=
  pos ≤ s.size ∧ re.novec + 2 * re.reps.size ≤ regs.size ∧
    Steady re pc pos regs

/-- Two pending threads the closure would deduplicate: same pc, same
position, both fit. -/
def Twin (re : Re) (s : ByteArray) (e f : Entry) : Prop :=
  e.1 = f.1 ∧ e.2.pos = f.2.pos ∧ Fit re s e.1 e.2.pos e.2.regs ∧
    Fit re s f.1 f.2.pos f.2.regs

theorem Fit.lt {re : Re} {s : ByteArray} {pc pos : Nat} {regs : Spec.Regs}
    (h : Fit re s pc pos regs) (hs : s.size ≤ ceiling) : pos < 2 ^ 31 := by
  have := h.1
  simp only [ceiling] at hs
  omega

/-- Fitness survives a move. -/
theorem eff_fit_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hs : s.size ≤ ceiling)
    (hfit : Fit re s pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    Fit re s pc' pos' regs' :=
  ⟨eff_pos_le hok hfit.1 heff, by rw [eff_size heff]; exact hfit.2.1,
    eff_steady_goto hok hcells hrows hmid (hfit.lt hs) hfit.2.1 hfit.2.2 heff⟩

/-- And a fork hands it to both arms. -/
theorem eff_fit_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' alt : Nat} {regs : Spec.Regs}
    (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hfit : Fit re s pc pos regs)
    (heff : eff re s mo start attempt pc pos regs = .fork pc' alt) :
    Fit re s pc' pos regs ∧ Fit re s alt pos regs :=
  ⟨⟨hfit.1, hfit.2.1, (eff_steady_fork hcells hrows hmid hfit.2.2 heff).1⟩,
    ⟨hfit.1, hfit.2.1, (eff_steady_fork hcells hrows hmid hfit.2.2 heff).2⟩⟩

private theorem ctrl_goto {e : Eff} {a b : Nat} (h : e.ctrl = .goto a b) :
    ∃ rg, e = .goto a b rg := by
  cases e <;> simp only [Eff.ctrl] at h
  case goto p q rg =>
      injection h with h1 h2
      exact ⟨rg, by rw [h1, h2]⟩
  all_goals exact absurd h (by simp)

private theorem ctrl_fork {e : Eff} {a b : Nat} (h : e.ctrl = .fork a b) :
    e = .fork a b := by
  cases e <;> simp only [Eff.ctrl] at h
  case fork p q =>
      injection h with h1 h2
      rw [h1, h2]
  all_goals exact absurd h (by simp)

private theorem ctrl_fail {e : Eff} (h : e.ctrl = .fail) : e = .fail := by
  cases e <;> simp only [Eff.ctrl] at h
  all_goals first | rfl | exact absurd h (by simp)

set_option maxHeartbeats 1000000 in
/-- The dedup lemma. Two threads that meet at the same pc and the same
position search the same tree: every move they make is the same move, so
where one comes back empty the other does too, whatever register file it
was carrying. The pending stacks travel with them, entry for entry.
That is what makes the closure's visited set sound — the later thread's
search was already run by the earlier one. -/
theorem run_dedup {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} (hok : pikeOk re.code re.reps = true)
    (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hs : s.size ≤ ceiling) :
    ∀ (fuel pc pos : Nat) (regs u : Spec.Regs) (stk stk' : List Entry),
      Fit re s pc pos regs → Fit re s pc pos u →
      List.Forall₂ (Twin re s) stk stk' →
      run re s mo start attempt fuel pc pos regs stk = some .nomatch →
      run re s mo start attempt fuel pc pos u stk' = some .nomatch := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; simp [run] at h
  | succ fuel ih =>
      intro pc pos regs u stk stk' hfit hufit hstk h
      have hctrl := eff_ctrl_congr (s := s) (mo := mo) (start := start)
        (attempt := attempt) hok hcells hrows (hfit.lt hs) hfit.2.2 hufit.2.2
      rw [run] at h ⊢
      cases heff : eff re s mo start attempt pc pos regs
      case goto a b rg =>
          simp only [heff] at h
          obtain ⟨u', heffu⟩ : ∃ w, eff re s mo start attempt pc pos u
              = .goto a b w := ctrl_goto (by rw [← hctrl, heff]; rfl)
          simp only [heffu]
          exact ih a b rg u' stk stk'
            (eff_fit_goto hok hcells hrows hmid hs hfit heff)
            (eff_fit_goto hok hcells hrows hmid hs hufit heffu) hstk h
      case fork a alt =>
          simp only [heff] at h
          have heffu : eff re s mo start attempt pc pos u = .fork a alt :=
            ctrl_fork (by rw [← hctrl, heff]; rfl)
          simp only [heffu]
          obtain ⟨hf1, hf2⟩ := eff_fit_fork hcells hrows hmid hfit heff
          obtain ⟨hg1, hg2⟩ := eff_fit_fork hcells hrows hmid hufit heffu
          exact ih a pos regs u ((alt, ⟨pos, regs⟩) :: stk)
            ((alt, ⟨pos, u⟩) :: stk') hf1 hg1
            (.cons ⟨rfl, rfl, hf2, hg2⟩ hstk) h
      case fail =>
          simp only [heff] at h
          have heffu : eff re s mo start attempt pc pos u = .fail :=
            ctrl_fail (by rw [← hctrl, heff]; rfl)
          simp only [heffu]
          cases hstk with
          | nil => rw [dispatch]
          | cons hpair hrest =>
              rename_i e f estk fstk
              obtain ⟨q, t⟩ := e
              obtain ⟨q', t'⟩ := f
              obtain ⟨hq, hpp, hfe, hff⟩ := hpair
              simp only [dispatch] at h ⊢
              simp only [] at hq hpp
              subst hq
              rw [← hpp]
              exact ih q t.pos t.regs t'.regs estk fstk hfe
                (by rw [hpp]; exact hff) hrest h
      case give t => simp only [heff] at h; exact absurd h (by simp)
      case stuck => simp only [heff] at h; exact absurd h (by simp)

/-- The dedup lemma at the judgment level. -/
theorem runs_dedup {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {regs u : Spec.Regs}
    {stk stk' : List Entry} (hok : pikeOk re.code re.reps = true)
    (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hs : s.size ≤ ceiling)
    (hfit : Fit re s pc pos regs) (hufit : Fit re s pc pos u)
    (hstk : List.Forall₂ (Twin re s) stk stk')
    (h : Runs re s mo start attempt pc pos regs stk .nomatch) :
    Runs re s mo start attempt pc pos u stk' .nomatch := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, run_dedup hok hcells hrows hmid hs fuel pc pos regs u stk stk'
    hfit hufit hstk hf⟩

/-- What the dedup lemma is for: an entry whose search has already been
run, and came back empty, is one the pending list can do without. It
neither finds anything of its own nor keeps the list from going on. -/
theorem resumes_drop {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc : Nat} {t : Spec.Thread} {L : List Entry} {r : Out}
    (hdead : Runs re s mo start attempt pc t.pos t.regs [] .nomatch) :
    Resumes re s mo start attempt ((pc, t) :: L) r ↔
      Resumes re s mo start attempt L r := by
  rw [resumes_cons]
  constructor
  · intro hrun
    rcases (runs_append (stk := []) (stk₂ := L)).mp (by simpa using hrun)
      with ⟨t', hr, hr2⟩ | ⟨_, hres⟩
    · exact absurd (runs_det hr2 hdead) (by rw [hr]; simp)
    · exact hres
  · intro hres
    simpa using (runs_append (stk := []) (stk₂ := L) (r := r)).mpr
      (Or.inr ⟨hdead, hres⟩)

/-- The eligibility flag is the verdict on the program it was computed
from. -/
theorem compile_pikeOk {p : Pat} (h : (compile p).pike = true) :
    pikeOk (compile p).code (compile p).reps = true := h

/-- The dedup lemma at a compiled pattern, with every side condition
about the program discharged: the rows describe their blocks, nothing
defers into the middle of one, and the repetition cells stand where their
rows name. What is left to the caller is about the two configurations
alone. -/
theorem compile_runs_dedup {p : Pat} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {regs u : Spec.Regs} {stk stk' : List Entry}
    (hw : Wf p) (hpike : (compile p).pike = true) (hs : s.size ≤ ceiling)
    (hfit : Fit (compile p) s pc pos regs)
    (hufit : Fit (compile p) s pc pos u)
    (hstk : List.Forall₂ (Twin (compile p) s) stk stk')
    (h : Runs (compile p) s mo start attempt pc pos regs stk .nomatch) :
    Runs (compile p) s mo start attempt pc pos u stk' .nomatch :=
  runs_dedup (compile_pikeOk hpike) (compile_cellsOk hw.1.covered hw.2)
    (fun _ hi => compile_rows hw.1.covered hi)
    (compile_noMidEntry hw.1.covered) hs hfit hufit hstk h

/-- The step the closure's visited set takes, spelled on a pending list.
An entry the list already carries higher up — same pc, same position —
makes a second copy of itself dead weight: whatever the copy would find,
the first one finds first, and where the first comes back empty the
dedup lemma says the copy does too. This is the soundness of dropping a
marked pc, and the only thing the correspondence needs from the visited
set. -/
theorem resumes_drop_dup {p : Pat} {s : ByteArray} {mo : MOpts}
    {start attempt pc : Nat} {t t₀ : Spec.Thread} {A B : List Entry}
    {r : Out} (hw : Wf p) (hpike : (compile p).pike = true)
    (hs : s.size ≤ ceiling) (hmem : (pc, t₀) ∈ A) (hpos : t₀.pos = t.pos)
    (hfit₀ : Fit (compile p) s pc t₀.pos t₀.regs)
    (hfit : Fit (compile p) s pc t.pos t.regs) :
    Resumes (compile p) s mo start attempt (A ++ (pc, t) :: B) r ↔
      Resumes (compile p) s mo start attempt (A ++ B) r := by
  rw [resumes_append, resumes_append]
  refine or_congr Iff.rfl (and_congr_right fun hA => ?_)
  refine resumes_drop ?_
  obtain ⟨A₁, A₂, rfl⟩ := List.mem_iff_append.mp hmem
  have hmid : Runs (compile p) s mo start attempt pc t₀.pos t₀.regs [] .nomatch := by
    have h1 := (resumes_append.mp hA).resolve_left (by simp)
    have h2 := (resumes_cons.mp h1.2)
    exact ((runs_append (stk := []) (stk₂ := A₂)).mp
      (by simpa using h2)).resolve_left (by simp) |>.1
  exact compile_runs_dedup (pos := t.pos) (regs := t₀.regs) (u := t.regs)
    hw hpike hs (hpos ▸ hfit₀) hfit List.Forall₂.nil (hpos ▸ hmid)

/-! ## The capture pool, read as a register file

A lockstep thread carries an integer handle into a flat pool of
`novec`-slot blocks where the specification's threads carry the block
itself, so the correspondence needs a decoding. `blockAt` is it, and it is
literally the slice `pike_run` delivers for the handle a match recorded.

What the rest will ask of it is small: blocks at different handles do not
overlap, a write lands in one block and leaves the others alone, and the
copy-on-write of `pike_write` really copies. -/

/-- The register file a handle points at: its block of the flat pool. -/
def blockAt (pool : Array UInt32) (novec h : Nat) : Spec.Regs :=
  (Array.range novec).map (fun k => pool[h * novec + k]!)

theorem blockAt_size (pool : Array UInt32) (novec h : Nat) :
    (blockAt pool novec h).size = novec := by simp [blockAt]

theorem blockAt_get {pool : Array UInt32} {novec h k : Nat} (hk : k < novec) :
    (blockAt pool novec h)[k]! = pool[h * novec + k]! := by
  rw [blockAt, getElem!_pos _ k (by simpa using hk)]
  simp

/-- Two blocks that agree slot for slot are the same register file, even
at different handles in different pools. -/
theorem blockAt_congr {p q : Array UInt32} {novec a b : Nat}
    (hag : ∀ k, k < novec → p[a * novec + k]! = q[b * novec + k]!) :
    blockAt p novec a = blockAt q novec b := by
  apply Array.ext
  · simp [blockAt_size]
  intro i h1 _
  have hlt : i < novec := by rwa [blockAt_size] at h1
  rw [← getElem!_pos _ i (by rw [blockAt_size]; exact hlt),
    ← getElem!_pos _ i (by rw [blockAt_size]; exact hlt),
    blockAt_get hlt, blockAt_get hlt]
  exact hag i hlt

/-- And it is the delivery: what a match hands back is the block its
handle names. -/
theorem deliver_eq_blockAt (pool : Array UInt32) (novec mh : Nat) :
    (Array.range novec).map (fun k => pool[mh * novec + k]!) =
      blockAt pool novec mh := rfl

/-- Blocks at different handles never overlap. -/
theorem block_disjoint {a b m k n : Nat} (hab : a ≠ b) (hm : m < n)
    (hk : k < n) : a * n + m ≠ b * n + k := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · have h1 : (a + 1) * n ≤ b * n := Nat.mul_le_mul_right n hlt
    rw [Nat.succ_mul] at h1
    omega
  · have hba : b < a := by omega
    have h1 : (b + 1) * n ≤ a * n := Nat.mul_le_mul_right n hba
    rw [Nat.succ_mul] at h1
    omega

/-- A write inside a block is a register write on that block. -/
theorem blockAt_set_self {pool : Array UInt32} {novec h slot : Nat}
    {v : UInt32} (hslot : slot < novec)
    (hroom : h * novec + novec ≤ pool.size) :
    blockAt (pool.set! (h * novec + slot) v) novec h =
      (blockAt pool novec h).set! slot v := by
  apply Array.ext
  · simp [blockAt_size]
  intro i h1 _
  have hlt : i < novec := by rwa [blockAt_size] at h1
  rw [← getElem!_pos _ i (by rw [blockAt_size]; exact hlt),
    ← getElem!_pos _ i (by simpa [blockAt_size] using hlt),
    blockAt_get hlt]
  by_cases hi : i = slot
  · rw [hi, getBang_set_self _ (by omega),
      getBang_set_self _ (by rw [blockAt_size]; omega)]
  · rw [getBang_set_other _ _ (by omega : h * novec + i ≠ h * novec + slot),
      getBang_set_other _ _ hi, blockAt_get hlt]

/-- A write outside a block leaves it alone. -/
theorem blockAt_set_other {pool : Array UInt32} {novec h i : Nat} {v : UInt32}
    (hout : ∀ k, k < novec → i ≠ h * novec + k) :
    blockAt (pool.set! i v) novec h = blockAt pool novec h := by
  refine blockAt_congr (fun k hk => ?_)
  exact getBang_set_other pool i (Ne.symm (hout k hk))

/-- Growth appends, so a block the pool already had room for reads the
same afterwards. -/
theorem blockAt_push {pool : Array UInt32} {novec h : Nat} {x : UInt32}
    (hroom : h * novec + novec ≤ pool.size) :
    blockAt (pool.push x) novec h = blockAt pool novec h := by
  refine blockAt_congr (fun k hk => ?_)
  rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
  simp [Array.getElem_push, show h * novec + k < pool.size from by omega]

/-- The copy `pike_write` makes before writing through a shared handle:
`novec` slots from the held block into the taken one. It reads back
correctly whether or not the two handles happen to be the same — with the
same handle every write is the identity, and with different ones the two
blocks do not overlap. -/
private theorem copy_size (pool : Array UInt32) (novec src dst : Nat) :
    ∀ m, ((List.range m).foldl (fun (p : Array UInt32) i =>
        p.set! (dst * novec + i) p[src * novec + i]!) pool).size =
      pool.size := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Array.size_set!]
      exact ih

private theorem copy_block (pool : Array UInt32) (novec src dst : Nat)
    (hdst : dst * novec + novec ≤ pool.size) :
    ∀ m, m ≤ novec →
      (∀ k, k < m →
        ((List.range m).foldl (fun (p : Array UInt32) i =>
            p.set! (dst * novec + i) p[src * novec + i]!)
          pool)[dst * novec + k]! = pool[src * novec + k]!) ∧
      (∀ i, (∀ k, k < m → i ≠ dst * novec + k) →
        ((List.range m).foldl (fun (p : Array UInt32) i =>
            p.set! (dst * novec + i) p[src * novec + i]!) pool)[i]! =
          pool[i]!) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨by simp, fun _ _ => rfl⟩
  | succ m ih =>
      intro hle
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have ihs := copy_size pool novec src dst m
      have hne : ∀ k, k < m → src * novec + m ≠ dst * novec + k := by
        intro k hk
        by_cases hsd : src = dst
        · subst hsd
          intro heq
          exact absurd (Nat.add_left_cancel heq) (by omega)
        · exact block_disjoint hsd (by omega) (by omega)
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · intro k hk
        by_cases hkm : k = m
        · subst hkm
          rw [getBang_set_self _ (by rw [ihs]; omega)]
          exact ih2 _ hne
        · rw [getBang_set_other _ _ (by omega : dst * novec + k ≠ dst * novec + m)]
          exact ih1 k (by omega)
      · intro i hi
        rw [getBang_set_other _ _ (hi m (by omega))]
        exact ih2 i (fun k hk => hi k (by omega))

private theorem blank_size (pool : Array UInt32) (novec h : Nat) :
    ∀ m, ((List.range m).foldl (fun (p : Array UInt32) i =>
        p.set! (h * novec + i) unset32) pool).size = pool.size := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Array.size_set!]
      exact ih

/-- The block `pike_seed` blanks before it plants the attempt: `novec`
slots of `unset32`, which is the register file the specification starts an
attempt with. -/
private theorem blank_block (pool : Array UInt32) (novec h : Nat)
    (hroom : h * novec + novec ≤ pool.size) :
    ∀ m, m ≤ novec →
      ∀ k, k < m →
        ((List.range m).foldl (fun (p : Array UInt32) i =>
          p.set! (h * novec + i) unset32) pool)[h * novec + k]! = unset32 := by
  intro m
  induction m with
  | zero => intro _ k hk; exact absurd hk (by omega)
  | succ m ih =>
      intro hle k hk
      have ihs := blank_size pool novec h m
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hkm : k = m
      · subst hkm
        rw [getBang_set_self _ (by rw [ihs]; omega)]
      · rw [getBang_set_other _ _
          (by omega : h * novec + k ≠ h * novec + m)]
        exact ih (by omega) k (by omega)

/-- And so the seed thread starts on a blank register file. -/
theorem blockAt_blank (pool : Array UInt32) (novec h : Nat)
    (hroom : h * novec + novec ≤ pool.size) :
    blockAt ((List.range novec).foldl
        (fun (p : Array UInt32) k => p.set! (h * novec + k) unset32) pool)
      novec h = Array.replicate novec unset32 := by
  apply Array.ext
  · simp [blockAt_size]
  intro i h1 _
  have hlt : i < novec := by rwa [blockAt_size] at h1
  rw [← getElem!_pos _ i (by rw [blockAt_size]; exact hlt),
    ← getElem!_pos _ i (by simpa using hlt), blockAt_get hlt,
    blank_block pool novec h hroom novec (Nat.le_refl _) i hlt,
    getElem!_pos _ i (by simpa using hlt)]
  simp

/-- Zeroing a fresh block only appends to the pool. -/
private theorem fill_pool {lim : Limits} : ∀ (k : Nat) (st st' : PikeSt),
    pikeTake.fill lim k st = .ok st' →
    st.pool.size ≤ st'.pool.size ∧
      ∀ i, i < st.pool.size → st'.pool[i]! = st.pool[i]! := by
  intro k
  induction k with
  | zero =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      injection hok with hok
      subst hok
      exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | succ n ih =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      split at hok
      · exact absurd_error hok
      · obtain ⟨h1, h2⟩ := ih _ _ hok
        simp only [Array.size_push] at h1
        refine ⟨by omega, fun i hi => ?_⟩
        rw [h2 i (by simp; omega), getElem!_pos _ i (by simp; omega),
          getElem!_pos _ i hi]
        simp [Array.getElem_push, hi]

/-- And so does `pike_take`: a block the pool already had reads the same
after one. -/
theorem pikeTake_pool {st st' : PikeSt} {novec hOut : Nat} {lim : Limits}
    (hok : pikeTake st novec lim = .ok (st', hOut)) :
    st.pool.size ≤ st'.pool.size ∧
      ∀ i, i < st.pool.size → st'.pool[i]! = st.pool[i]! := by
  unfold pikeTake at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    injection hok with hok _
    subst hok
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  · split at hok
    · exact absurd_error hok
    · split at hok
      · exact absurd_error hok
      · split at hok
        · exact absurd_error hok
        · rename_i hfill
          injection hok with hok
          injection hok with hok _
          subst hok
          obtain ⟨h1, h2⟩ := fill_pool _ _ _ hfill
          exact ⟨h1, h2⟩

/-- `pike_write` is a register write on the block its handle names: in
place through an unshared handle, on a fresh copy through a shared one.
The room hypothesis is about the block the answer names, which is where
the write landed. -/
theorem pikeWrite_block {st st' : PikeSt} {novec h slot hOut : Nat}
    {v : UInt32} {lim : Limits} (hslot : slot < novec)
    (hroom : h * novec + novec ≤ st.pool.size)
    (hroom' : hOut * novec + novec ≤ st'.pool.size)
    (hok : pikeWrite st novec h slot v lim = .ok (st', hOut)) :
    blockAt st'.pool novec hOut = (blockAt st.pool novec h).set! slot v := by
  unfold pikeWrite at hok
  simp only [] at hok
  split at hok
  · split at hok
    · exact absurd_error hok
    · split at hok
      · exact absurd_error hok
      · rename_i stT fresh hTake
        injection hok with hok
        injection hok with hok hfresh
        subst hfresh
        subst hok
        obtain ⟨_, hkeep0⟩ := pikeTake_pool hTake
        -- The charge before the take moved the meter, not the pool.
        have hkeep : ∀ i, i < st.pool.size → stT.pool[i]! = st.pool[i]! :=
          hkeep0
        simp only [Array.size_set!, copy_size] at hroom'
        have hcopy := copy_block stT.pool novec h fresh hroom' novec
          (Nat.le_refl _)
        rw [blockAt_set_self hslot (by simp only [copy_size]; exact hroom'),
          blockAt_congr (novec := novec) (a := fresh) (b := h)
            (fun k hk => hcopy.1 k hk),
          blockAt_congr (fun k hk => hkeep (h * novec + k) (by omega))]
  · injection hok with hok
    injection hok with hok hfresh
    subst hfresh
    subst hok
    exact blockAt_set_self hslot hroom

/-- The same at slot zero, where the index is the block's own base. -/
theorem blockAt_set_zero {pool : Array UInt32} {novec h : Nat} {v : UInt32}
    (hnov : 0 < novec) (hroom : h * novec + novec ≤ pool.size) :
    blockAt (pool.set! (h * novec) v) novec h =
      (blockAt pool novec h).set! 0 v := by
  simpa using blockAt_set_self (pool := pool) (novec := novec) (h := h)
    (slot := 0) (v := v) hnov hroom

/-- The block a seed starts on: blank but for the attempt in slot 0, which
is the register file the specification hands an attempt with the machine's
one pre-write already in it. -/
theorem blockAt_seed (pool : Array UInt32) (novec sh pos : Nat)
    (hnov : 0 < novec) (hroom : sh * novec + novec ≤ pool.size) :
    blockAt (((List.range novec).foldl
        (fun (p : Array UInt32) k => p.set! (sh * novec + k) unset32)
        pool).set! (sh * novec) pos.toUInt32) novec sh =
      (Array.replicate novec unset32).set! 0 pos.toUInt32 := by
  rw [blockAt_set_zero hnov (by rw [blank_size]; omega),
    blockAt_blank _ _ _ hroom]

/-! ## The pool's room

`Owned`, the ownership reading of `PikeBounds`, says a handle someone
holds is a block the refcount table names and that the pool is exactly the
table's blocks laid end to end. Between them that is the one fact the
register-file reading was missing. -/

/-- A handle someone holds names a block the pool has room for, which is
what every lemma above asks of a handle. -/
theorem room_of_owned {novec : Nat} {rc free : Array Nat}
    {pool : Array UInt32} {live : List Nat} {h : Nat}
    (how : Owned novec rc free pool live) (hh : h ∈ live) :
    h * novec + novec ≤ pool.size := by
  have hlt : h < rc.size := how.reach h hh
  have hmul : (h + 1) * novec ≤ rc.size * novec :=
    Nat.mul_le_mul_right novec (by omega)
  rw [Nat.succ_mul] at hmul
  rw [how.blocks]
  omega

/-- `pike_write` as a register write, its room hypotheses discharged by
the pool's own bookkeeping: the handle written through and the handle
answered are both blocks someone holds. -/
theorem pikeWrite_block_owned {st st' : PikeSt} {novec h slot hOut : Nat}
    {v : UInt32} {rest : List Nat} {lim : Limits} (hslot : slot < novec)
    (how : Owned novec st.rc st.free st.pool (h :: rest))
    (hok : pikeWrite st novec h slot v lim = .ok (st', hOut)) :
    blockAt st'.pool novec hOut = (blockAt st.pool novec h).set! slot v :=
  pikeWrite_block hslot (room_of_owned how List.mem_cons_self)
    (room_of_owned (pikeWrite_owned hok how).1 List.mem_cons_self) hok

/-! ## The bumpalong rule, on the lockstep side

The position loop's one piece of arithmetic that does not wait on the
thread correspondence: which starting positions it offers at all.
`pike_seed` declines under exactly the test `scan_first` computes, and
`crFirst_agrees` says that bit is the specification's own, so the two
layers attempt the same positions. -/

/-- `pike_seed`'s refusal is the compiled pattern's own bumpalong test,
asked of every position after the first. -/
theorem pikeSeed_skip {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start pos : Nat} {st : PikeSt} (hgt : start < pos)
    (hskip : Re.skipsAttempt re s pos = true) :
    pikeSeed re s mo lim start pos st = .ok st := by
  rw [pikeSeed]
  split
  · rfl
  · rename_i hno
    exfalso
    apply hno
    rw [Re.skipsAttempt] at hskip
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hskip ⊢
    refine ⟨⟨⟨⟨⟨⟨hgt, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp_all

/-- The same refusal read against the specification: on a well-formed
pattern the lockstep loop declines exactly the attempts `Spec.scan`
skips. -/
theorem pikeSeed_skip_spec {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start pos : Nat} {st : PikeSt} (hw : WfAst p.root)
    (hgt : start < pos) (hskip : Spec.skipsAttempt p s pos = true) :
    pikeSeed (compile p) s mo lim start pos st = .ok st :=
  pikeSeed_skip hgt (by rw [skipsAttempt_agrees hw]; exact hskip)

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
  there. Its two ingredients are in hand: `resumes_drop_dup` is the
  visited set's step, sound by the dedup lemma, and
  `compile_epsReach_no_cycle` is the ordering it needs — a marked pc is
  one the closure has finished with, because no walk steps out and comes
  back. What is
  owed is the invariant that runs the induction over `pikeAdd.go`: the
  parked list and the worklist, decoded through `blockAt`, read as a
  pending list that answers what the mirror's continuation answers, with
  a marked pc standing for a segment of the parked prefix. The decoding is
  by `Agree re.novec`, not equality — a pool block is `novec` slots wide
  where the mirror's file carries the repetition counters above them —
  and the `Fit` the dedup wants is carried on the mirror's side, where the
  seed's blank file has it and `eff_fit_goto`/`eff_fit_fork` keep it;
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
