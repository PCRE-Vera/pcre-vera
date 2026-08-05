import Pcrevera.Proofs.Refine
import Pcrevera.Proofs.Agreement
import Pcrevera.Proofs.PikeBounds

/-!
# S-8, the lockstep half

`pikeRun_refines_matches` is the twin of `btRun_refines_matches`: on a
Pike-eligible program, whenever `pikeRun` reports matched or no-match its
answer is `Spec.Matches`, and the two layers call an input bad on the same
offsets — plus the refusal the lockstep matcher owns alone, an ineligible
program.

The argument is four layers deep. The epsilon closure reads one build
against the mirror; the list step reads one position against the merge of
the attempts still running; the seed puts one more attempt in at the
bottom of the list; and the position loop reads the whole walk against
`Spec.scan`, whose attempts are the positions the loop seeds. Everything
above the closure works in one currency, the merge, and the reason it has
to is that a lockstep list is not one attempt's search but several,
running side by side in leftmost order.

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

* **The capture pool, and threads decoded.** A lockstep thread carries a
  handle into a flat pool where the specification's threads carry the
  block itself, so the correspondence needs a decoding. `blockAt` is it — `deliver_eq_blockAt`
  says it is the very slice `pike_run` hands back on a match — and what
  the rest asks of it is three facts: `blockAt_seed` (a seed starts blank
  but for the attempt in slot 0), `pikeTake_pool` (taking a block only
  appends, so a block the pool already had reads the same afterwards) and
  `pikeWrite_block` (a write is a register write, in place through an
  unshared handle and on a fresh copy through a shared one).
  `pikeWrite_block_owned` discharges its room hypotheses from `Owned`, the
  ownership reading of `PikeBounds`, whose `blocks` clause says the pool
  is the refcount table's blocks laid end to end. `pikeWrite_block_keep`
  is the other half of the same fact — a write lands in one block only,
  the one the answer names — and with `pikeTake_block` and the three
  `_pool` lemmas it is the stability every reading rests on. `ThAt` is
  the reading itself, at `Agree re.novec` rather than equality, and
  `ThAt.goto`, `ThAt.bump`, `ThAt.write` and `ThAt.keepWrite` are what
  the closure's four kinds of arm do to it.

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

* **One move, read as a rewrite of the pending list.** `resumes_goto`,
  `resumes_fork`, `resumes_fail` and `resumes_give` are `runs_eff` read
  through `resumes_cons`: the shape `pike_add`'s worklist follows, since
  popping an entry and replacing it by what its instruction defers to is
  exactly what these four say the mirror does. `fit_seed` starts the
  chain — the blank register file an attempt begins on fits.

* **The dedup across attempts, and the merge.** A lockstep thread list at
  one position carries the live threads of every attempt still running,
  earliest first, with the position's own seed last — so the visited set
  deduplicates across attempts, and what the list answers is a merge
  rather than one attempt's `Resumes`. `run_dedup_att` is the first half:
  `eff` reads its attempt at one cell only, the empty-match refusal at
  `accept`, and the thread the visited set keeps is the earlier one, which
  standing no earlier than the later attempt began cannot be at its own
  starting offset and so never refuses. `MergeAfter` is the second — a
  merged pending list read with a verdict already on record below it,
  which is what a recorded match is — and `mergeAfter_append`,
  `mergeAfter_tagAtt` and `mergeAfter_drop_dup` are its frame law, its
  reading of a single attempt, and the visited set's step.

* **Pending lists that answer alike.** `SameAfter` is what the closure has
  to preserve: two stretches of a pending list answering alike under every
  continuation, read behind a common prefix. The prefix is not decoration.
  The closure's one lossy move, dropping a pc it has already expanded, is
  sound only in the shadow of the stretch that expanded it, and `Settled`
  is that shadow — a pc the closure is done with, because a run of the
  parked list already answers for it. `Settled.drop` is what it buys.

* **One iteration, read on both sides.** `ArmOk` and `PopOk` say what one
  turn of `pike_add`'s loop leaves behind: the worklist with an expansion
  on top, whatever the arm parked, the pc marked, the pool undisturbed
  away from the handle a save wrote through, and an
  expansion answering what the popped entry answered. `pikeAdd_go_step`
  proves it arm by arm, and the two repetition cells are where eligibility
  is spent — the deciding head always forks and a `repNext` always returns
  to it, so the machine's one step through both is the mirror's two.

* **The closure correspondence.** `pikeAdd_go_refine` drains one stretch
  of the worklist and says what the parked list gained in its place: a
  stretch answering what the drained one answered, and a settlement for
  every pc the drain marked. `pikeAdd_refine` is the whole call, and it
  hands the settlement back so that the next build in the same list can
  take over. The invariant speaks about the stack rather than about the
  parked prefix, because at the moment a pc is marked its expansion is on
  the worklist and only draining it moves the settlement into place; a pc
  pushed from inside its own expansion would be a walk that stepped out and
  came back, which is what `epsReach_no_cycle` refuses. Two clauses of
  `ArmOk` are there for the list step rather than for the closure: an arm
  parks only at an opcode the step dispatches, and it leaves slot zero
  alone, since a compiled save names slot two or above and the counters
  live above the ovector.

* **The one cell the mirror never reads.** A thread's block carries its
  attempt in slot zero, so the mirror's file carries it there too, where
  the specification's blank file carries nothing. `OffTag` is the
  difference and `run_offTag` says no search can see it: slot zero is read
  at no instruction and written only by the accept, which writes the
  attempt. `seed_attempt_refines` is what that buys — one attempt's whole
  search, read against `Spec.attemptThreads`.

* **One position, stepped.** `Live` and `MList` read a built list as a
  merge: every entry fits, carries its attempt in slot zero, stands at an
  opcode the step dispatches, and the attempts run earliest first.
  `stepThreads_refine` walks it — a consuming leaf whose byte matches opens
  a closure into the next list, one whose byte does not is dropped, and an
  accepting thread records its answer and takes everything below it with
  it, which is what `MergeAfter`'s record is for. The visited set travels
  with the list rather than with a build, since it is cleared once per
  position and spans every build that fills one list.

* **The bumpalong, on this side.** `pikeSeed_skip_spec`: the position loop
  declines a starting position exactly where `Spec.scan` skips an attempt.
  `pikeSeed_refine` reads the other side of that test — a call the loop
  makes whose own bumpalong does not skip takes a block that is the
  specification's blank file with the attempt already stamped into slot
  zero, and the build on top of it goes in at the bottom of the list, which
  is the leftmost rule read as priority order. Whether the loop calls at
  all, which anchoring and a recorded match also decide, is the loop's own
  business.

* **The position loop.** `pikeLoop_refine` walks the positions carrying
  `MList` on the current list, `OnRecord` on the match handle and the
  settlement premise on the visited set, and reads the whole walk against
  `Spec.scan`. `Decides` is the reading: a merge that finds something
  settles the call outright, and one that comes back empty hands the
  question on to the attempts not opened yet — which is the scan's own
  tail. `Link` is the only bookkeeping that costs anything, since where the
  machine declines a position the scan is already standing one further on.

* **The guards.** `pikeRun_badInput` locates the two refusals in the call
  itself, and `pikeRun_badInput_agrees` matches them against the
  specification's own BadInput under the documented subject cap. That is
  S-8's third clause for this matcher.

* **The whole call.** `pikeRun_refines_matches` puts the three together.
  At the last position the next list is empty, because `Live` asks for a
  position inside the subject, so the merge is its own record, and
  `deliver_eq_blockAt` says the ovector handed back is the block that
  record names.
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
      ((code[pc]!).op = Op.save →
        2 ≤ (code[pc]!).arg ∧ (code[pc]!).arg < novec) := by
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
          fun _ => ⟨by show 2 ≤ 2 * cap; omega,
            by show 2 * cap < novec; omega⟩⟩
      · rcases Nat.lt_or_ge pc j with hp2 | hp2
        · exact ihbody hcaps.2 pc hp hp2
        · rw [show pc = j from by omega, hclose]
          exact ⟨fun hq => by simp at hq, fun hq => by simp at hq,
            fun hq => by simp at hq, fun hq => by simp at hq,
            fun _ => ⟨by show 2 ≤ 2 * cap + 1; omega,
              by show 2 * cap + 1 < novec; omega⟩⟩
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
    2 ≤ (re.code[q]! : Inst).arg ∧ (re.code[q]! : Inst).arg < re.novec

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
        2 ≤ ((compile p).code[q]!).arg ∧
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

/-! ## What the closure argument asks of the program

Six facts about the program travel together from here on: eligibility
itself, the rows describing their own blocks, the repetition cells
standing where their rows name, no edge into the middle of a block, which
way the closure's edges run, and an ovector with room for the whole
match's own two slots. `Eligible` bundles them, so that the statements
below read as claims about the closure rather than as claims about the
compiler. -/

/-- Everything the closure argument reads off the program. -/
structure Eligible (re : Re) : Prop where
  ok : pikeOk re.code re.reps = true
  rows : ∀ i, i < re.reps.size → RowOk re.code re.reps i
  cells : CellsOk re
  mid : NoMidEntry re
  fwd : EpsForward re
  novec : 2 ≤ re.novec

/-- A well-formed pattern whose program the lockstep matcher accepted has
all six. -/
theorem compile_eligible {p : Pat} (hw : Wf p)
    (hpike : (compile p).pike = true) : Eligible (compile p) :=
  ⟨hpike, fun _ hi => compile_rows hw.1.covered hi,
    compile_cellsOk hw.1.covered hw.2, compile_noMidEntry hw.1.covered,
    compile_epsForward hw.1.covered, by
      show 2 ≤ 2 * (p.ncap + 1)
      omega⟩

/-- The acyclicity, read off the bundle: no closure walk takes a step and
comes back where it started. -/
theorem Eligible.noCycle {re : Re} (he : Eligible re) {pc mid : Nat}
    (hmid : mid ∈ epsTargets re.code re.reps pc)
    (hback : EpsReach re.code re.reps mid pc) : False :=
  epsReach_no_cycle he.ok he.rows he.cells he.fwd hmid hback

/-- A walk that ends anywhere but where it started takes a first step. -/
theorem EpsReach.split {code : Array Inst} {reps : Array RepInfo} {a b : Nat}
    (h : EpsReach code reps a b) :
    a = b ∨ ∃ t ∈ epsTargets code reps a, EpsReach code reps t b := by
  cases h with
  | refl => exact Or.inl rfl
  | step hmid hrest => exact Or.inr ⟨_, hmid, hrest⟩

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
      exact getBang_set_other regs _
        (by have := (hcells.save pc hop).2; omega)
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
      have hlow := (hcells.save pc hop).2
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

/-! ## The dedup across attempts

A lockstep thread list is a merge: at one position it carries the live
threads of every attempt still running, earliest attempt first. So the
visited set deduplicates across attempts too — the seed for the position
is built last and against everything already there — and the dedup lemma
has to answer for two threads opened at different offsets.

It does, and the reason is the one cell the attempt is read at. `eff`
mentions its `attempt` argument nowhere but the empty-match refusal at
`accept`, so away from that cell two runs at different attempts make the
same move. At `accept` the refusal asks whether the match is empty for
*that* attempt, and the thread the visited set keeps is the earlier one:
standing at a position no earlier than the later attempt began, it cannot
be standing at its own starting offset, so it never refuses. A run that
came back empty therefore never reached an `accept` at all, and the
thread being dropped does not reach one either. -/

/-- A move never goes backwards along the subject. -/
theorem eff_pos_mono {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos pc' pos' : Nat} {regs regs' : Spec.Regs}
    (heff : eff re s mo start attempt pc pos regs = .goto pc' pos' regs') :
    pos ≤ pos' := by
  cases hop : (re.code[pc]!).op <;> simp only [eff, hop] at heff
  all_goals (repeat' split at heff)
  all_goals first
    | exact absurd_fail heff
    | exact absurd_fork heff
    | exact absurd_give heff
    | (injection heff with _ h5 _
       omega)

/-- The attempt a run was opened with is read at one cell only, so
everywhere else two runs opened at different offsets make the same
move. -/
theorem eff_attempt_congr {re : Re} {s : ByteArray} {mo : MOpts}
    {start a₁ a₂ pc pos : Nat} {regs : Spec.Regs}
    (hop : (re.code[pc]! : Inst).op ≠ Op.accept) :
    eff re s mo start a₁ pc pos regs = eff re s mo start a₂ pc pos regs := by
  cases hq : (re.code[pc]!).op <;> simp only [eff, hq]
  case accept => exact absurd hq hop
  all_goals rfl

/-- And at that cell a run standing anywhere but its own starting offset
delivers: the refusal is about an empty match, and an empty match is one
that ends where the attempt began. -/
theorem eff_accept_give {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {regs : Spec.Regs}
    (hop : (re.code[pc]! : Inst).op = Op.accept) (hne : pos ≠ attempt) :
    ∃ t, eff re s mo start attempt pc pos regs = .give t := by
  simp only [eff, hop]
  rw [if_neg (by simp [hne])]
  exact ⟨_, rfl⟩

/-- Two pending threads the closure would deduplicate across attempts:
same pc, same position, both fit, and standing no earlier than the later
attempt began. -/
def TwinAtt (re : Re) (s : ByteArray) (a : Nat) (e f : Entry) : Prop :=
  e.1 = f.1 ∧ e.2.pos = f.2.pos ∧ a ≤ e.2.pos ∧
    Fit re s e.1 e.2.pos e.2.regs ∧ Fit re s f.1 f.2.pos f.2.regs

theorem forall₂_twin_of_att {re : Re} {s : ByteArray} {a : Nat}
    {stk stk' : List Entry} (h : List.Forall₂ (TwinAtt re s a) stk stk') :
    List.Forall₂ (Twin re s) stk stk' := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hxy _ ih =>
      exact List.Forall₂.cons ⟨hxy.1, hxy.2.1, hxy.2.2.2.1, hxy.2.2.2.2⟩ ih

set_option maxHeartbeats 1000000 in
/-- The dedup lemma across attempts. The later thread searches what the
earlier one searched, so where the earlier comes back empty the later does
too — and the one cell that could tell them apart cannot fire on the
earlier one, because it stands past its own starting offset. -/
theorem run_dedup_att {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    (hok : pikeOk re.code re.reps = true) (hcells : CellsOk re)
    (hrows : ∀ i, i < re.reps.size → RowOk re.code re.reps i)
    (hmid : NoMidEntry re) (hs : s.size ≤ ceiling) {a₁ a₂ : Nat}
    (hle : a₁ ≤ a₂) :
    ∀ (fuel pc pos : Nat) (regs u : Spec.Regs) (stk stk' : List Entry),
      a₂ ≤ pos → Fit re s pc pos regs → Fit re s pc pos u →
      List.Forall₂ (TwinAtt re s a₂) stk stk' →
      run re s mo start a₁ fuel pc pos regs stk = some .nomatch →
      run re s mo start a₂ fuel pc pos u stk' = some .nomatch := by
  by_cases ha : a₁ = a₂
  · subst ha
    intro fuel pc pos regs u stk stk' _ hfit hufit hstk h
    exact run_dedup hok hcells hrows hmid hs fuel pc pos regs u stk stk'
      hfit hufit (forall₂_twin_of_att hstk) h
  · have hlt : a₁ < a₂ := by omega
    intro fuel
    induction fuel with
    | zero => intro _ _ _ _ _ _ _ _ _ _ h; simp [run] at h
    | succ fuel ih =>
        intro pc pos regs u stk stk' hpos hfit hufit hstk h
        by_cases hacc : (re.code[pc]!).op = Op.accept
        · obtain ⟨t, hgive⟩ :=
            eff_accept_give (s := s) (mo := mo) (start := start) (attempt := a₁)
              (pos := pos) (regs := regs) hacc (by omega)
          rw [run, hgive] at h
          exact absurd h (by simp)
        · have hctrl : (eff re s mo start a₁ pc pos regs).ctrl =
              (eff re s mo start a₂ pc pos u).ctrl := by
            rw [eff_attempt_congr (a₂ := a₂) hacc]
            exact eff_ctrl_congr hok hcells hrows (hfit.lt hs) hfit.2.2 hufit.2.2
          rw [run] at h ⊢
          cases heff : eff re s mo start a₁ pc pos regs
          case goto b c rg =>
              simp only [heff] at h
              obtain ⟨u', heffu⟩ : ∃ w, eff re s mo start a₂ pc pos u
                  = .goto b c w := ctrl_goto (by rw [← hctrl, heff]; rfl)
              simp only [heffu]
              refine ih b c rg u' stk stk' (by
                  have := eff_pos_mono heff
                  omega)
                (eff_fit_goto hok hcells hrows hmid hs hfit heff)
                (eff_fit_goto hok hcells hrows hmid hs hufit heffu) hstk h
          case fork b alt =>
              simp only [heff] at h
              have heffu : eff re s mo start a₂ pc pos u = .fork b alt :=
                ctrl_fork (by rw [← hctrl, heff]; rfl)
              simp only [heffu]
              obtain ⟨hf1, hf2⟩ := eff_fit_fork hcells hrows hmid hfit heff
              obtain ⟨hg1, hg2⟩ := eff_fit_fork hcells hrows hmid hufit heffu
              exact ih b pos regs u ((alt, ⟨pos, regs⟩) :: stk)
                ((alt, ⟨pos, u⟩) :: stk') hpos hf1 hg1
                (.cons ⟨rfl, rfl, hpos, hf2, hg2⟩ hstk) h
          case fail =>
              simp only [heff] at h
              have heffu : eff re s mo start a₂ pc pos u = .fail :=
                ctrl_fail (by rw [← hctrl, heff]; rfl)
              simp only [heffu]
              cases hstk with
              | nil => rw [dispatch]
              | cons hpair hrest =>
                  rename_i e f estk fstk
                  obtain ⟨q, t⟩ := e
                  obtain ⟨q', t'⟩ := f
                  obtain ⟨hq, hpp, hap, hfe, hff⟩ := hpair
                  simp only [dispatch] at h ⊢
                  simp only [] at hq hpp hap
                  subst hq
                  rw [← hpp]
                  exact ih q t.pos t.regs t'.regs estk fstk hap hfe
                    (by rw [hpp]; exact hff) hrest h
          case give t => simp only [heff] at h; exact absurd h (by simp)
          case stuck => simp only [heff] at h; exact absurd h (by simp)

/-- The dedup across attempts at the judgment level. -/
theorem runs_dedup_att {re : Re} {s : ByteArray} {mo : MOpts}
    {start a₁ a₂ pc pos : Nat} {regs u : Spec.Regs} {stk stk' : List Entry}
    (he : Eligible re) (hs : s.size ≤ ceiling) (hle : a₁ ≤ a₂) (hpos : a₂ ≤ pos)
    (hfit : Fit re s pc pos regs) (hufit : Fit re s pc pos u)
    (hstk : List.Forall₂ (TwinAtt re s a₂) stk stk')
    (h : Runs re s mo start a₁ pc pos regs stk .nomatch) :
    Runs re s mo start a₂ pc pos u stk' .nomatch := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, run_dedup_att he.ok he.cells he.rows he.mid hs hle fuel pc pos
    regs u stk stk' hpos hfit hufit hstk hf⟩

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
theorem resumes_drop_dup {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc : Nat} {t t₀ : Spec.Thread} {A B : List Entry}
    {r : Out} (he : Eligible re) (hs : s.size ≤ ceiling)
    (hmem : (pc, t₀) ∈ A) (hpos : t₀.pos = t.pos)
    (hfit₀ : Fit re s pc t₀.pos t₀.regs) (hfit : Fit re s pc t.pos t.regs) :
    Resumes re s mo start attempt (A ++ (pc, t) :: B) r ↔
      Resumes re s mo start attempt (A ++ B) r := by
  rw [resumes_append, resumes_append]
  refine or_congr Iff.rfl (and_congr_right fun hA => ?_)
  refine resumes_drop ?_
  obtain ⟨A₁, A₂, rfl⟩ := List.mem_iff_append.mp hmem
  have hmid : Runs re s mo start attempt pc t₀.pos t₀.regs [] .nomatch := by
    have h1 := (resumes_append.mp hA).resolve_left (by simp)
    have h2 := (resumes_cons.mp h1.2)
    exact ((runs_append (stk := []) (stk₂ := A₂)).mp
      (by simpa using h2)).resolve_left (by simp) |>.1
  exact runs_dedup (pos := t.pos) (regs := t₀.regs) (u := t.regs)
    he.ok he.cells he.rows he.mid hs (hpos ▸ hfit₀) hfit List.Forall₂.nil
    (hpos ▸ hmid)

/-! ## The lockstep list is a merge of attempts

The backtracking mirror searches one attempt. A lockstep thread list at
one position carries the live threads of every attempt still running,
earliest attempt first, with the position's own seed last — so what the
list answers is not one attempt's `Resumes` but the merge of several:
the first entry whose own search finds something, read at the attempt that
entry was opened by.

`MergeAfter` is that reading, carrying a verdict already on record below
it, which is what a recorded match is — an accepting thread kills
everything below itself, and only a thread above it can still overwrite
the record. `MergeRuns` is the same with nothing on record.

The tag an entry carries is not bookkeeping the proof invents: a thread's
attempt is slot 0 of its capture block, planted by `pike_seed` and never
written again, since the only `save` a compiled pattern spells belongs to
a numbered group and lands at slot 2 or above. -/

/-- One entry of a merged pending list: the attempt it was opened by, and
the entry itself. -/
abbrev MEntry := Nat × Entry

/-- A single attempt's pending list, read as a merged one. -/
def tagAtt (a : Nat) (L : List Entry) : List MEntry := L.map fun e => (a, e)

theorem tagAtt_append (a : Nat) (L₁ L₂ : List Entry) :
    tagAtt a (L₁ ++ L₂) = tagAtt a L₁ ++ tagAtt a L₂ := List.map_append

/-- What a merged pending list answers, with a verdict already on record
below it. Every entry is run on its own, at its own attempt, and the first
one to find something is the answer — which is what priority order
means. -/
def MergeAfter (re : Re) (s : ByteArray) (mo : MOpts) (start : Nat) :
    List MEntry → Out → Out → Prop
  | [], back, r => r = back
  | (a, e) :: rest, back, r =>
      (∃ t, r = .found t ∧
        Runs re s mo start a e.1 e.2.pos e.2.regs [] (.found t)) ∨
      (Runs re s mo start a e.1 e.2.pos e.2.regs [] .nomatch ∧
        MergeAfter re s mo start rest back r)

/-- The same, with nothing on record. -/
def MergeRuns (re : Re) (s : ByteArray) (mo : MOpts) (start : Nat)
    (L : List MEntry) (r : Out) : Prop :=
  MergeAfter re s mo start L .nomatch r

/-- The frame law of the merge, and the same statement `resumes_append`
makes one attempt at a time. -/
theorem mergeAfter_append {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat} :
    ∀ (L₁ L₂ : List MEntry) (back r : Out),
      MergeAfter re s mo start (L₁ ++ L₂) back r ↔
        ((∃ t, r = .found t ∧ MergeRuns re s mo start L₁ r) ∨
          (MergeRuns re s mo start L₁ .nomatch ∧
            MergeAfter re s mo start L₂ back r)) := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ back r
      constructor
      · intro h
        exact Or.inr ⟨show (Out.nomatch : Out) = .nomatch from rfl, h⟩
      · rintro (⟨t, rfl, hc⟩ | ⟨_, h⟩)
        · exact absurd (show (Out.found t) = Out.nomatch from hc) (by simp)
        · exact h
  | cons x L₁ ih =>
      intro L₂ back r
      obtain ⟨a, e⟩ := x
      show (_ ∨ _) ↔ _
      constructor
      · rintro (⟨t, rfl, hf⟩ | ⟨hn, hrest⟩)
        · exact Or.inl ⟨t, rfl, Or.inl ⟨t, rfl, hf⟩⟩
        · rcases (ih L₂ back r).mp hrest with ⟨t, rfl, hc⟩ | ⟨hc, h2⟩
          · exact Or.inl ⟨t, rfl, Or.inr ⟨hn, hc⟩⟩
          · exact Or.inr ⟨Or.inr ⟨hn, hc⟩, h2⟩
      · rintro (⟨t, rfl, hc⟩ | ⟨hc, h2⟩)
        · rcases (show (_ ∨ _) from hc) with ⟨t', ht', hf⟩ | ⟨hn, hc'⟩
          · exact Or.inl ⟨t', ht', hf⟩
          · exact Or.inr ⟨hn, (ih L₂ back _).mpr (Or.inl ⟨t, rfl, hc'⟩)⟩
        · rcases (show (_ ∨ _) from hc) with ⟨t', ht', _⟩ | ⟨hn, hc'⟩
          · exact absurd ht' (by simp)
          · exact Or.inr ⟨hn, (ih L₂ back r).mpr (Or.inr ⟨hc', h2⟩)⟩

/-- An entry of a merge that came back empty came back empty itself. -/
theorem MergeRuns.mem_nomatch {re : Re} {s : ByteArray} {mo : MOpts}
    {start : Nat} : ∀ {L : List MEntry}, MergeRuns re s mo start L .nomatch →
      ∀ x ∈ L, Runs re s mo start x.1 x.2.1 x.2.2.pos x.2.2.regs [] .nomatch := by
  intro L
  induction L with
  | nil => exact fun _ x hx => absurd hx (by simp)
  | cons y L ih =>
      obtain ⟨a, e⟩ := y
      intro h x hx
      rcases (show _ ∨ _ from h) with ⟨t, ht, _⟩ | ⟨hn, hrest⟩
      · exact absurd ht (by simp)
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact hn
        · exact ih hrest x hx'

/-- One attempt's list, read as a merge: the merge finds what the attempt
finds, and falls through to the record when the attempt finds nothing. -/
theorem runs_split {re : Re} {s : ByteArray} {mo : MOpts}
    {start a pc pos : Nat} {regs : Spec.Regs} {L : List Entry} {r : Out} :
    Runs re s mo start a pc pos regs L r ↔
      ((∃ w, r = .found w ∧ Runs re s mo start a pc pos regs [] r) ∨
        (Runs re s mo start a pc pos regs [] .nomatch ∧
          Resumes re s mo start a L r)) := by
  have h := runs_append (re := re) (s := s) (mo := mo) (start := start)
    (attempt := a) (pc := pc) (pos := pos) (regs := regs) (stk := [])
    (stk₂ := L) (r := r)
  simpa using h

theorem mergeAfter_tagAtt {re : Re} {s : ByteArray} {mo : MOpts}
    {start a : Nat} : ∀ (L : List Entry) (back r : Out),
      MergeAfter re s mo start (tagAtt a L) back r ↔
        ((∃ t, r = .found t ∧ Resumes re s mo start a L r) ∨
          (Resumes re s mo start a L .nomatch ∧ r = back)) := by
  intro L
  induction L with
  | nil =>
      intro back r
      constructor
      · intro h
        exact Or.inr ⟨resumes_nil.mpr rfl, h⟩
      · rintro (⟨t, rfl, hc⟩ | ⟨_, h⟩)
        · exact absurd (resumes_nil.mp hc) (by simp)
        · exact h
  | cons e L ih =>
      intro back r
      obtain ⟨pc, t⟩ := e
      show (_ ∨ _) ↔ _
      simp only [resumes_cons]
      constructor
      · rintro (⟨w, rfl, hf⟩ | ⟨hn, hrest⟩)
        · exact Or.inl ⟨w, rfl, runs_split.mpr (Or.inl ⟨w, rfl, hf⟩)⟩
        · rcases (ih back r).mp hrest with ⟨w, rfl, hc⟩ | ⟨hc, h2⟩
          · exact Or.inl ⟨w, rfl, runs_split.mpr (Or.inr ⟨hn, hc⟩)⟩
          · exact Or.inr ⟨runs_split.mpr (Or.inr ⟨hn, hc⟩), h2⟩
      · rintro (⟨w, rfl, hc⟩ | ⟨hc, h2⟩)
        · rcases runs_split.mp hc with ⟨w', hw', hf⟩ | ⟨hn, hc'⟩
          · exact Or.inl ⟨w, rfl, hf⟩
          · exact Or.inr ⟨hn, (ih back _).mpr (Or.inl ⟨w, rfl, hc'⟩)⟩
        · rcases runs_split.mp hc with ⟨w', hw', _⟩ | ⟨hn, hc'⟩
          · exact absurd hw' (by simp)
          · exact Or.inr ⟨hn, (ih back r).mpr (Or.inr ⟨hc', h2⟩)⟩

/-- The visited set's step on a merged list, and the reason the lockstep
matcher may deduplicate across attempts at all: an entry that a
higher-priority one already covers — same pc, same position, an attempt no
later — is one the merge can do without. -/
theorem mergeAfter_drop_dup {re : Re} {s : ByteArray} {mo : MOpts}
    {start a₁ a₂ pc : Nat} {t₀ t : Spec.Thread} {A B : List MEntry}
    {back r : Out} (he : Eligible re) (hs : s.size ≤ ceiling)
    (hmem : (a₁, (pc, t₀)) ∈ A) (hle : a₁ ≤ a₂) (hpos : t₀.pos = t.pos)
    (hstand : a₂ ≤ t.pos) (hfit₀ : Fit re s pc t₀.pos t₀.regs)
    (hfit : Fit re s pc t.pos t.regs) :
    MergeAfter re s mo start (A ++ (a₂, (pc, t)) :: B) back r ↔
      MergeAfter re s mo start (A ++ B) back r := by
  rw [mergeAfter_append, mergeAfter_append]
  refine or_congr Iff.rfl (and_congr_right fun hA => ?_)
  have hdead : Runs re s mo start a₂ pc t.pos t.regs [] .nomatch :=
    runs_dedup_att he hs hle hstand (hpos ▸ hfit₀) hfit List.Forall₂.nil
      (hpos ▸ hA.mem_nomatch _ hmem)
  show (_ ∨ _) ↔ _
  constructor
  · rintro (⟨w, rfl, hf⟩ | ⟨_, h2⟩)
    · exact absurd (runs_det hf hdead) (by simp)
    · exact h2
  · exact fun h => Or.inr ⟨hdead, h⟩

/-! ## Pending lists that answer alike

The closure rewrites a pending list one entry at a time, and what it has
to preserve is the answer the list gives — not on its own, but under
whatever the caller left below it and behind whatever the closure has
already settled. `MSame` is that relation on merged lists: two stretches
answer alike under every continuation, once the stretch in front of them
is fixed. The prefix is not decoration. The closure's one lossy move,
dropping a pc it has already expanded, is sound only in the shadow of the
stretch that expanded it, and that stretch is exactly what the prefix
holds — possibly at an earlier attempt than the pc being dropped, since
the visited set is shared across the builds that fill one list.

`SameAfter` is the reading a closure build works in: the prefix is the
merge already parked, while the two stretches compared are the build's
own, all at its seed's attempt. -/

/-- A merged list read without its tags. -/
def untag (L : List MEntry) : List Entry := L.map Prod.snd

theorem untag_append (L₁ L₂ : List MEntry) :
    untag (L₁ ++ L₂) = untag L₁ ++ untag L₂ := List.map_append

theorem untag_tagAtt (a : Nat) (L : List Entry) : untag (tagAtt a L) = L := by
  simp [untag, tagAtt, Function.comp_def]

/-- Two merged stretches that answer alike under every continuation, read
behind a common merged prefix. -/
def MSame (re : Re) (s : ByteArray) (mo : MOpts) (start : Nat)
    (A L₁ L₂ : List MEntry) : Prop :=
  ∀ (Y : List MEntry) (back r : Out),
    MergeAfter re s mo start (A ++ L₁ ++ Y) back r ↔
      MergeAfter re s mo start (A ++ L₂ ++ Y) back r

theorem MSame.refl {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    {A L : List MEntry} : MSame re s mo start A L L := fun _ _ _ => Iff.rfl

theorem MSame.symm {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    {A L₁ L₂ : List MEntry} (h : MSame re s mo start A L₁ L₂) :
    MSame re s mo start A L₂ L₁ := fun Y back r => (h Y back r).symm

theorem MSame.trans {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    {A L₁ L₂ L₃ : List MEntry} (h₁ : MSame re s mo start A L₁ L₂)
    (h₂ : MSame re s mo start A L₂ L₃) : MSame re s mo start A L₁ L₃ :=
  fun Y back r => (h₁ Y back r).trans (h₂ Y back r)

/-- Two stretches in a row, each read behind what stands in front of
it. -/
theorem MSame.comp {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    {A L₁ L₂ M₁ M₂ : List MEntry} (h₁ : MSame re s mo start A L₁ L₂)
    (h₂ : MSame re s mo start (A ++ L₂) M₁ M₂) :
    MSame re s mo start A (L₁ ++ M₁) (L₂ ++ M₂) := by
  intro Y back r
  have e1 := h₁ (M₁ ++ Y) back r
  have e2 := h₂ Y back r
  simp only [List.append_assoc] at e1 e2 ⊢
  exact e1.trans e2

/-- A rewrite that holds of a merged stretch on its own holds behind any
prefix. -/
theorem mSame_of_all {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    {A L₁ L₂ : List MEntry}
    (h : ∀ (Y : List MEntry) (back r : Out),
      MergeAfter re s mo start (L₁ ++ Y) back r ↔
        MergeAfter re s mo start (L₂ ++ Y) back r) :
    MSame re s mo start A L₁ L₂ := by
  intro Y back r
  rw [List.append_assoc, List.append_assoc, mergeAfter_append A (L₁ ++ Y),
    mergeAfter_append A (L₂ ++ Y)]
  exact or_congr Iff.rfl (and_congr Iff.rfl (h Y back r))

/-- The relation a closure build works in: the prefix is the merge already
parked, and the two stretches compared are its own seed's. -/
def SameAfter (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (A : List MEntry) (L₁ L₂ : List Entry) : Prop :=
  MSame re s mo start A (tagAtt attempt L₁) (tagAtt attempt L₂)

theorem SameAfter.refl {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {A : List MEntry} {L : List Entry} :
    SameAfter re s mo start attempt A L L := MSame.refl

theorem SameAfter.symm {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {A : List MEntry} {L₁ L₂ : List Entry}
    (h : SameAfter re s mo start attempt A L₁ L₂) :
    SameAfter re s mo start attempt A L₂ L₁ := MSame.symm h

theorem SameAfter.trans {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {A : List MEntry} {L₁ L₂ L₃ : List Entry}
    (h₁ : SameAfter re s mo start attempt A L₁ L₂)
    (h₂ : SameAfter re s mo start attempt A L₂ L₃) :
    SameAfter re s mo start attempt A L₁ L₃ := MSame.trans h₁ h₂

theorem SameAfter.comp {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {A : List MEntry} {L₁ L₂ M₁ M₂ : List Entry}
    (h₁ : SameAfter re s mo start attempt A L₁ L₂)
    (h₂ : SameAfter re s mo start attempt (A ++ tagAtt attempt L₂) M₁ M₂) :
    SameAfter re s mo start attempt A (L₁ ++ M₁) (L₂ ++ M₂) := by
  unfold SameAfter
  rw [tagAtt_append, tagAtt_append]
  exact MSame.comp h₁ h₂

/-- One attempt's lists that answer alike answer alike inside a merge. -/
theorem mergeRuns_congr {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {L₁ L₂ : List Entry}
    (h : ∀ r, Resumes re s mo start attempt L₁ r ↔
      Resumes re s mo start attempt L₂ r) (q : Out) :
    MergeRuns re s mo start (tagAtt attempt L₁) q ↔
      MergeRuns re s mo start (tagAtt attempt L₂) q := by
  rw [MergeRuns, MergeRuns, mergeAfter_tagAtt, mergeAfter_tagAtt]
  exact or_congr (exists_congr fun _ => and_congr Iff.rfl (h _))
    (and_congr (h _) Iff.rfl)

/-- And so one attempt's rewrite is a rewrite of the merge it sits in. -/
theorem sameAfter_of_resumes {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {A : List MEntry} {L₁ L₂ : List Entry}
    (h : ∀ r, Resumes re s mo start attempt L₁ r ↔
      Resumes re s mo start attempt L₂ r) :
    SameAfter re s mo start attempt A L₁ L₂ := by
  refine mSame_of_all (fun Y back r => ?_)
  rw [mergeAfter_append _ Y, mergeAfter_append _ Y]
  exact or_congr (exists_congr fun _ => and_congr Iff.rfl (mergeRuns_congr h _))
    (and_congr (mergeRuns_congr h _) Iff.rfl)

/-- A pc the closure is done with: inside the merge it has already settled
sits a run of entries answering exactly what a thread at that pc would
answer, read behind whatever stands in front of that run. The run may be
an earlier attempt's — the visited set is shared across the builds that
fill one list — which is why it carries an attempt of its own, no later
than the one the dropped copy belongs to. -/
def Settled (re : Re) (s : ByteArray) (mo : MOpts) (start a pos : Nat)
    (P : List MEntry) (q : Nat) : Prop :=
  ∃ (A Sq B : List MEntry) (t₀ : Spec.Thread) (a₀ : Nat),
    P = A ++ Sq ++ B ∧ a₀ ≤ a ∧ t₀.pos = pos ∧ Fit re s q pos t₀.regs ∧
      MSame re s mo start A Sq [(a₀, (q, t₀))]

/-- A pc stays settled as the settled stretch grows behind it. -/
theorem Settled.mono {re : Re} {s : ByteArray} {mo : MOpts}
    {start a pos : Nat} {P : List MEntry} {q : Nat}
    (h : Settled re s mo start a pos P q) (M : List MEntry) :
    Settled re s mo start a pos (P ++ M) q := by
  obtain ⟨A, Sq, B, t₀, a₀, rfl, hle, hp, hfit, hsame⟩ := h
  exact ⟨A, Sq, B ++ M, t₀, a₀, by simp, hle, hp, hfit, hsame⟩

/-- What being settled buys, and the whole point of the visited set: a
thread at a settled pc, standing anywhere below the stretch that settled
it, is one the merge can do without. The stretch answers what the first
copy answered, and the dedup lemma carries that verdict onto a copy
carrying any other register file and opened by any later attempt. -/
theorem Settled.drop {re : Re} {s : ByteArray} {mo : MOpts}
    {start a pos : Nat} {P : List MEntry} {q : Nat}
    (he : Eligible re) (hs : s.size ≤ ceiling)
    (h : Settled re s mo start a pos P q) {t : Spec.Thread}
    (hpos : t.pos = pos) (hstand : a ≤ pos) (hfit : Fit re s q pos t.regs)
    (C Y : List MEntry) (back r : Out) :
    MergeAfter re s mo start (P ++ C ++ (a, (q, t)) :: Y) back r ↔
      MergeAfter re s mo start (P ++ C ++ Y) back r := by
  obtain ⟨A, Sq, B, t₀, a₀, rfl, hle, hp, hfit₀, hsame⟩ := h
  have hkey : ∀ Z : List MEntry, ∀ back r : Out,
      MergeAfter re s mo start (A ++ Sq ++ B ++ C ++ Z) back r ↔
        MergeAfter re s mo start (A ++ (a₀, (q, t₀)) :: (B ++ C ++ Z))
          back r := by
    intro Z back r
    have hx := hsame (B ++ C ++ Z) back r
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hx ⊢
    exact hx
  rw [hkey ((a, (q, t)) :: Y) back r, hkey Y back r]
  have hdup := mergeAfter_drop_dup (re := re) (s := s) (mo := mo)
    (start := start) (a₁ := a₀) (a₂ := a) (pc := q) (t := t) (t₀ := t₀)
    (A := A ++ (a₀, (q, t₀)) :: (B ++ C)) (B := Y) (back := back) (r := r)
    he hs (by simp) hle (by rw [hp, hpos]) (by omega) (by rw [hp]; exact hfit₀)
    (by rw [hpos]; exact hfit)
  simp only [List.append_assoc, List.cons_append] at hdup ⊢
  exact hdup

/-! ## One move, read as a rewrite of the pending list

`pike_add`'s worklist is the mirror's pending stack with the register
files swapped for handles: it pops the top entry, and replaces it by
whatever its instruction defers to. These four lemmas are the mirror's
side of that — a goto replaces the entry, a fork replaces it by its two
arms in preference order, a fail drops it, and a deliver ends the search.
They are `runs_eff` read through `resumes_cons`, and they are the shape
the closure induction follows: `pike_add`'s cases are exactly these,
`repNext` excepted, where the closure takes in one step the return to the
deciding head and the head's own fork together. -/

theorem resumes_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pc' pos' : Nat} {t : Spec.Thread} {regs' : Spec.Regs}
    {rest : List Entry} {r : Out}
    (heff : eff re s mo start attempt pc t.pos t.regs = .goto pc' pos' regs') :
    Resumes re s mo start attempt ((pc, t) :: rest) r ↔
      Resumes re s mo start attempt ((pc', ⟨pos', regs'⟩) :: rest) r := by
  rw [resumes_cons, runs_eff, heff, resumes_cons]
  exact Iff.rfl

theorem resumes_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc a b : Nat} {t : Spec.Thread} {rest : List Entry}
    {r : Out} (heff : eff re s mo start attempt pc t.pos t.regs = .fork a b) :
    Resumes re s mo start attempt ((pc, t) :: rest) r ↔
      Resumes re s mo start attempt ((a, t) :: (b, t) :: rest) r := by
  rw [resumes_cons, runs_eff, heff, resumes_cons]
  exact Iff.rfl

theorem resumes_fail {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc : Nat} {t : Spec.Thread} {rest : List Entry} {r : Out}
    (heff : eff re s mo start attempt pc t.pos t.regs = .fail) :
    Resumes re s mo start attempt ((pc, t) :: rest) r ↔
      Resumes re s mo start attempt rest r := by
  rw [resumes_cons, runs_eff, heff]
  exact Iff.rfl

theorem resumes_give {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc : Nat} {t u : Spec.Thread} {rest : List Entry} {r : Out}
    (heff : eff re s mo start attempt pc t.pos t.regs = .give u) :
    Resumes re s mo start attempt ((pc, t) :: rest) r ↔ r = .found u := by
  rw [resumes_cons, runs_eff, heff]
  exact Iff.rfl

/-- The same three, read behind any prefix, which is the form the closure
induction composes them in. -/
theorem sameAfter_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pc' pos' : Nat} {t : Spec.Thread} {regs' : Spec.Regs}
    {A : List MEntry}
    (heff : eff re s mo start attempt pc t.pos t.regs = .goto pc' pos' regs') :
    SameAfter re s mo start attempt A [(pc, t)] [(pc', ⟨pos', regs'⟩)] :=
  sameAfter_of_resumes (fun _ => resumes_goto heff)

theorem sameAfter_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc a b : Nat} {t : Spec.Thread} {A : List MEntry}
    (heff : eff re s mo start attempt pc t.pos t.regs = .fork a b) :
    SameAfter re s mo start attempt A [(pc, t)] [(a, t), (b, t)] :=
  sameAfter_of_resumes (fun _ => resumes_fork heff)

theorem sameAfter_fail {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc : Nat} {t : Spec.Thread} {A : List MEntry}
    (heff : eff re s mo start attempt pc t.pos t.regs = .fail) :
    SameAfter re s mo start attempt A [(pc, t)] [] :=
  sameAfter_of_resumes (fun _ => resumes_fail heff)

/-- The register file an attempt starts on fits: the position is inside
the subject, the file is exactly as long as the counters need, and the
three invariants hold of it — no entry position is on record, and no
repetition block is live at the program's first cell. -/
theorem fit_seed {p : Pat} {s : ByteArray} {attempt : Nat}
    (hc : Covered p.root) (hs : s.size ≤ ceiling) (hatt : attempt ≤ s.size) :
    Fit (compile p) s 0 attempt
      (Array.replicate (compile p).nregs unset32) := by
  obtain ⟨hfrag, hrsz, _, _⟩ := compile_shape hc
  have hnregs : (compile p).nregs = (compile p).novec + 2 * (compile p).reps.size := by
    show ((compile p).ncap + 1) * 2 + (compile p).reps.size * 2 = _
    show ((compile p).ncap + 1) * 2 + (compile p).reps.size * 2 =
      2 * ((compile p).ncap + 1) + 2 * (compile p).reps.size
    omega
  have hblank : ∀ i, i < (compile p).nregs →
      (Array.replicate (compile p).nregs unset32)[i]! = unset32 := by
    intro i hi
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  refine ⟨hatt, by rw [Array.size_replicate, hnregs]; exact Nat.le_refl _, ?_, ?_, ?_⟩
  · intro r hr
    exact Or.inr (hblank _ (by omega))
  · intro r hr _ heq
    rw [hblank _ (by omega)] at heq
    have hv := congrArg UInt32.toNat heq
    rw [unset32_toNat, toNat_ofNat32 (show attempt < 2 ^ 32 by
      simp only [ceiling] at hs; omega)] at hv
    simp only [ceiling] at hs
    omega
  · intro r hr hge _
    exact absurd hge (by have := (compile_rows hc hr).low; omega)

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

/-! ## What a step leaves a block alone

The correspondence reads every live handle as a register file, so it needs
to know when a reading survives a step. Three of the closure's helpers do
not touch the pool at all, `pike_take` only appends, and `pike_write`
lands in exactly one block — the one it answers with. Together that is
the stability the induction runs on: a block someone holds reads the same
after a step that did not write through its own handle. -/

theorem pikeDefer_pool {st st' : PikeSt} {pc h : Nat} {lim : Limits}
    (hok : pikeDefer st pc h lim = .ok st') : st'.pool = st.pool := by
  unfold pikeDefer at hok
  split at hok
  · exact absurd_error hok
  · injection hok with hok
    subst hok
    rfl

theorem pikeDrop_pool {st st' : PikeSt} {h : Nat} {lim : Limits}
    (hok : pikeDrop st h lim = .ok st') : st'.pool = st.pool := by
  unfold pikeDrop at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    subst hok
    rfl
  · split at hok
    · split at hok
      · exact absurd_error hok
      · injection hok with hok
        subst hok
        rfl
    · injection hok with hok
      subst hok
      rfl

theorem pikePark_pool {st st' : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} (hok : pikePark st intoNext pc h lim = .ok st') :
    st'.pool = st.pool := by
  unfold pikePark at hok
  split at hok <;> split at hok
  · exact absurd_error hok
  · injection hok with hok
    subst hok
    rfl
  · exact absurd_error hok
  · injection hok with hok
    subst hok
    rfl

/-- Taking a block only appends, so one the pool already had room for
reads the same afterwards. -/
theorem pikeTake_block {st st' : PikeSt} {novec hOut k : Nat} {lim : Limits}
    (hroom : k * novec + novec ≤ st.pool.size)
    (hok : pikeTake st novec lim = .ok (st', hOut)) :
    blockAt st'.pool novec k = blockAt st.pool novec k := by
  obtain ⟨_, hkeep⟩ := pikeTake_pool hok
  exact blockAt_congr (fun i hi => hkeep (k * novec + i) (by omega))

/-- And a write lands in one block only: the one the answer names. In
place through an unshared handle that is the block written through, and on
a fresh copy through a shared one; either way every other block reads the
same. -/
theorem pikeWrite_block_keep {st st' : PikeSt} {novec h slot hOut k : Nat}
    {v : UInt32} {lim : Limits} (hslot : slot < novec) (hk : k ≠ hOut)
    (hroom : k * novec + novec ≤ st.pool.size)
    (hroom' : hOut * novec + novec ≤ st'.pool.size)
    (hok : pikeWrite st novec h slot v lim = .ok (st', hOut)) :
    blockAt st'.pool novec k = blockAt st.pool novec k := by
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
        refine Eq.trans (blockAt_set_other
          (fun j hj => block_disjoint (Ne.symm hk) hslot hj)) ?_
        refine Eq.trans (blockAt_congr (novec := novec) (a := k) (b := k)
          (fun m hm => hcopy.2 (k * novec + m)
            (fun j hj => block_disjoint hk hm hj))) ?_
        exact blockAt_congr (fun m hm => hkeep (k * novec + m) (by omega))
  · injection hok with hok
    injection hok with hok hfresh
    subst hfresh
    subst hok
    exact blockAt_set_other (fun j hj => block_disjoint (Ne.symm hk) hslot hj)

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

/-- A write leaves every other held block alone, its room hypotheses
discharged by the pool's own bookkeeping. -/
theorem pikeWrite_block_keep_owned {st st' : PikeSt}
    {novec h slot hOut k : Nat} {v : UInt32} {rest : List Nat} {lim : Limits}
    (hslot : slot < novec) (hk : k ≠ hOut) (hkl : k ∈ h :: rest)
    (how : Owned novec st.rc st.free st.pool (h :: rest))
    (hok : pikeWrite st novec h slot v lim = .ok (st', hOut)) :
    blockAt st'.pool novec k = blockAt st.pool novec k :=
  pikeWrite_block_keep hslot hk (room_of_owned how hkl)
    (room_of_owned (pikeWrite_owned hok how).1 List.mem_cons_self) hok

/-- The last cell of a non-empty array, split off its list. -/
private theorem toList_snoc_back {α : Type _} [Inhabited α] {a : Array α}
    (h : 0 < a.size) : a.toList = a.pop.toList ++ [a.back!] := by
  have hne : a.toList ≠ [] := by
    intro he
    have hz : a.toList.length = 0 := by rw [he]; rfl
    rw [Array.length_toList] at hz
    omega
  have hlast : a.toList.getLast hne = a.back! := by
    rw [Array.back!, getElem!_pos a (a.size - 1) (by omega),
      ← Array.getElem_toList, List.getLast_eq_getElem]
    simp
  rw [Array.toList_pop, ← hlast, List.dropLast_concat_getLast hne]

/-- A block handed out is one nobody was holding. Off the free list it is
a block whose refcount is zero, which is to say a block with no holder;
fresh it is a block the table did not have. -/
theorem pikeTake_fresh {st st' : PikeSt} {novec hOut : Nat} {live : List Nat}
    {lim : Limits} (hok : pikeTake st novec lim = .ok (st', hOut))
    (how : Owned novec st.rc st.free st.pool live) : hOut ∉ live := by
  unfold pikeTake at hok
  simp only [] at hok
  split at hok
  · rename_i hne
    have hpos : 0 < st.free.size := by
      rcases Nat.eq_zero_or_pos st.free.size with hz | hp
      · exact absurd hne (by simp [hz])
      · exact hp
    injection hok with hok
    injection hok with _ hh
    subst hh
    have hmem : st.free.back! ∈ st.free.toList := by
      rw [toList_snoc_back hpos]
      simp
    have hlt : st.free.back! < st.rc.size := how.freeRange _ hmem
    have hcnt : 0 < st.free.toList.count st.free.back! :=
      Nat.pos_of_ne_zero (fun hz => (List.count_eq_zero.mp hz) hmem)
    have hzero : st.rc[st.free.back!]! = 0 := (how.onFree _ hlt).mpr hcnt
    rw [how.count _ hlt] at hzero
    exact List.count_eq_zero.mp hzero
  · split at hok
    · exact absurd_error hok
    · split at hok
      · exact absurd_error hok
      · split at hok
        · exact absurd_error hok
        · injection hok with hok
          injection hok with _ hh
          subst hh
          exact fun hmem => absurd (how.reach _ hmem) (by omega)

/-- And so the handle a write answers with is nobody else's: a fresh block
through a shared handle, and through an unshared one the very block the
write went to, which by then has no other holder. -/
theorem pikeWrite_fresh {st st' : PikeSt} {novec h slot hOut : Nat}
    {v : UInt32} {rest : List Nat} {lim : Limits}
    (how : Owned novec st.rc st.free st.pool (h :: rest))
    (hok : pikeWrite st novec h slot v lim = .ok (st', hOut)) : hOut ∉ rest := by
  have hlt : h < st.rc.size := how.reach h List.mem_cons_self
  unfold pikeWrite at hok
  simp only [] at hok
  split at hok
  · split at hok
    · exact absurd_error hok
    · split at hok
      · exact absurd_error hok
      · rename_i stT fresh hTake
        injection hok with hok
        injection hok with _ hh
        subst hh
        exact fun hmem =>
          pikeTake_fresh hTake how (List.mem_cons_of_mem _ hmem)
  · rename_i hshare
    injection hok with hok
    injection hok with _ hh
    subst hh
    have hcount := how.count h hlt
    have hsplit : (h :: rest).count h = rest.count h + 1 := by simp
    rw [hsplit] at hcount
    exact List.count_eq_zero.mp (by omega)

/-! ## Threads, decoded

A lockstep thread is a pc and a handle where a mirror entry is a pc and a
register file, so the correspondence reads the handle through `blockAt`.
The reading stops at `novec`, because that is how wide a pool block is:
the repetition counters the mirror carries above the ovector are the
machine's to do without, since on an eligible program neither cell that
reads one decides anything. `ThAt` is the reading of one thread, and what
follows is what the closure's arms do to it — a step that leaves the
block alone keeps it, the counter writes the mirror makes land above the
window it looks at, and a `save` is the same register write on both sides
at once. -/

/-- A write above the ovector is invisible to the reading. -/
theorem agree_set_high_right {novec : Nat} {u v : Spec.Regs}
    (h : Agree novec u v) {i : Nat} (hi : novec ≤ i) (x : UInt32) :
    Agree novec u (v.set! i x) := by
  obtain ⟨hu, hv, hag⟩ := h
  refine ⟨hu, by rw [Array.size_set!]; exact hv, fun j hj => ?_⟩
  rw [getBang_set_other v i (by omega)]
  exact hag j hj

/-- A machine thread read as a mirror entry: the same pc, the position the
list is being built for, and a register file agreeing with the block the
handle names. -/
def ThAt (re : Re) (pool : Array UInt32) (pos : Nat) (th : Th) (e : Entry) :
    Prop :=
  e.1 = th.pc ∧ e.2.pos = pos ∧
    Agree re.novec (blockAt pool re.novec th.h) e.2.regs

/-- A whole worklist or thread list, read as a pending list. -/
def ThList (re : Re) (pool : Array UInt32) (pos : Nat) : List Th →
    List Entry → Prop := List.Forall₂ (ThAt re pool pos)

/-- The reading is about the block the handle names and nothing else. -/
theorem ThAt.ofPool {re : Re} {pool pool' : Array UInt32} {pos : Nat}
    {th : Th} {e : Entry} (h : ThAt re pool pos th e)
    (hb : blockAt pool' re.novec th.h = blockAt pool re.novec th.h) :
    ThAt re pool' pos th e := ⟨h.1, h.2.1, hb ▸ h.2.2⟩

/-- Where the closure moves a thread on without touching its block. -/
theorem ThAt.goto {re : Re} {pool : Array UInt32} {pos : Nat} {th : Th}
    {e : Entry} (h : ThAt re pool pos th e) (q : Nat) :
    ThAt re pool pos ⟨q, th.h⟩ (q, e.2) := ⟨rfl, h.2.1, h.2.2⟩

/-- And where the mirror writes a counter the machine does not keep. -/
theorem ThAt.bump {re : Re} {pool : Array UInt32} {pos : Nat} {th : Th}
    {e : Entry} {i : Nat} {x : UInt32} (h : ThAt re pool pos th e)
    (hi : re.novec ≤ i) (q : Nat) :
    ThAt re pool pos ⟨q, th.h⟩ (q, ⟨e.2.pos, e.2.regs.set! i x⟩) :=
  ⟨rfl, h.2.1, agree_set_high_right h.2.2 hi x⟩

/-- The `save` arm, on both sides at once: `pike_write` is a register
write on the block its handle names, the mirror's save is the same write
on the register file, and the reading survives with the answered handle in
place of the old one. -/
theorem ThAt.write {re : Re} {st st' : PikeSt} {pos slot hOut : Nat}
    {v : UInt32} {rest : List Nat} {lim : Limits} {th : Th} {e : Entry}
    (hslot : slot < re.novec)
    (how : Owned re.novec st.rc st.free st.pool (th.h :: rest))
    (hok : pikeWrite st re.novec th.h slot v lim = .ok (st', hOut))
    (h : ThAt re st.pool pos th e) (q : Nat) :
    ThAt re st'.pool pos ⟨q, hOut⟩ (q, ⟨e.2.pos, e.2.regs.set! slot v⟩) :=
  ⟨rfl, h.2.1, by
    rw [pikeWrite_block_owned hslot how hok]
    exact h.2.2.set_both slot v⟩

/-- And what that same write does to everyone else's reading: nothing. -/
theorem ThAt.keepWrite {re : Re} {st st' : PikeSt} {pos slot h hOut : Nat}
    {v : UInt32} {rest : List Nat} {lim : Limits} {th : Th} {e : Entry}
    (hslot : slot < re.novec) (hk : th.h ≠ hOut) (hkl : th.h ∈ h :: rest)
    (how : Owned re.novec st.rc st.free st.pool (h :: rest))
    (hok : pikeWrite st re.novec h slot v lim = .ok (st', hOut))
    (hat : ThAt re st.pool pos th e) : ThAt re st'.pool pos th e :=
  hat.ofPool (pikeWrite_block_keep_owned hslot hk hkl how hok)

/-! ## Lists of threads, and the worklist in priority order

`ThList` reads a whole array of threads as a pending list; what the
closure induction asks of it is that it survives a step that left every
block it looks at alone, and that it takes apart and puts back together
the way the arrays do. The worklist is the one array read backwards: the
closure pops the last cell first, so its priority order is the reverse of
its layout. -/

/-- The worklist read the way the closure pops it, top first. -/
def stkOf (a : Array Th) : List Th := a.toList.reverse

theorem stkOf_push (a : Array Th) (th : Th) :
    stkOf (a.push th) = th :: stkOf a := by
  simp [stkOf]

theorem stkOf_pop {a : Array Th} (h : 0 < a.size) :
    stkOf a = a.back! :: stkOf a.pop := by
  rw [stkOf, stkOf, toList_snoc_back h]
  simp

theorem stkOf_nil {a : Array Th} (h : a.size = 0) : stkOf a = [] := by
  have hl : a.toList = [] := by
    rw [← List.length_eq_zero_iff, Array.length_toList, h]
  rw [stkOf, hl]
  rfl

/-- Reading a list of threads is about the blocks their handles name and
nothing else. -/
theorem ThList.ofPool {re : Re} {pool pool' : Array UInt32} {pos : Nat}
    {ths : List Th} {es : List Entry} (h : ThList re pool pos ths es)
    (hb : ∀ th ∈ ths, blockAt pool' re.novec th.h = blockAt pool re.novec th.h) :
    ThList re pool' pos ths es := by
  revert hb
  unfold ThList at h ⊢
  induction h with
  | nil => exact fun _ => List.Forall₂.nil
  | @cons x y xs ys hxy _ ih =>
      intro hb
      exact List.Forall₂.cons (hxy.ofPool (hb x List.mem_cons_self))
        (ih (fun th hth => hb th (List.mem_cons_of_mem _ hth)))

theorem ThList.append {re : Re} {pool : Array UInt32} {pos : Nat}
    {a₁ a₂ : List Th} {b₁ b₂ : List Entry} (h₁ : ThList re pool pos a₁ b₁)
    (h₂ : ThList re pool pos a₂ b₂) :
    ThList re pool pos (a₁ ++ a₂) (b₁ ++ b₂) := by
  unfold ThList at h₁ h₂ ⊢
  induction h₁ with
  | nil => exact h₂
  | cons hxy _ ih => exact List.Forall₂.cons hxy ih

theorem ThList.length_eq {re : Re} {pool : Array UInt32} {pos : Nat}
    {ths : List Th} {es : List Entry} (h : ThList re pool pos ths es) :
    ths.length = es.length := by
  unfold ThList at h
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- And a reading of two stretches in a row comes apart into the two. -/
theorem ThList.split {re : Re} {pool : Array UInt32} {pos : Nat} :
    ∀ {a₁ a₂ : List Th} {b₁ b₂ : List Entry}, a₁.length = b₁.length →
      ThList re pool pos (a₁ ++ a₂) (b₁ ++ b₂) →
      ThList re pool pos a₁ b₁ ∧ ThList re pool pos a₂ b₂ := by
  intro a₁
  induction a₁ with
  | nil =>
      intro a₂ b₁ b₂ hlen h
      have hb : b₁ = [] := by
        rw [← List.length_eq_zero_iff]
        simpa using hlen.symm
      subst hb
      exact ⟨List.Forall₂.nil, h⟩
  | cons x xs ih =>
      intro a₂ b₁ b₂ hlen h
      cases b₁ with
      | nil => simp at hlen
      | cons y ys =>
          unfold ThList at h
          cases h with
          | cons hxy hrest =>
              obtain ⟨h1, h2⟩ := ih (by simpa using hlen) hrest
              exact ⟨List.Forall₂.cons hxy h1, h2⟩

/-- An entry of a read list is read off one of the array's threads. -/
theorem ThList.mem_left {re : Re} {pool : Array UInt32} {pos : Nat}
    {ths : List Th} {es : List Entry} (h : ThList re pool pos ths es)
    {e : Entry} (hem : e ∈ es) : ∃ th ∈ ths, ThAt re pool pos th e := by
  revert hem
  unfold ThList at h
  induction h with
  | nil => exact fun hem => absurd hem (by simp)
  | @cons x y xs ys hxy _ ih =>
      intro hem
      rcases List.mem_cons.mp hem with rfl | hem'
      · exact ⟨x, List.mem_cons_self, hxy⟩
      · obtain ⟨th, hth, hat⟩ := ih hem'
        exact ⟨th, List.mem_cons_of_mem _ hth, hat⟩

/-- Every handle the worklist carries is one the reckoning counts. -/
theorem mem_handles_of_stkOf {a : Array Th} {th : Th} (h : th ∈ stkOf a) :
    th.h ∈ handles a := by
  rw [stkOf, List.mem_reverse] at h
  exact List.mem_map_of_mem h

theorem mem_handles_of_toList {a : Array Th} {th : Th} (h : th ∈ a.toList) :
    th.h ∈ handles a := List.mem_map_of_mem h

/-! ## One iteration of the closure, read on both sides

Every arm of `pike_add`'s dispatch does the same two things: it takes the
popped entry off the worklist and puts back what the instruction defers
to — nothing, one continuation, two, or the entry itself parked for the
position it waits on. `ArmOk` is that reading, and its last clause is the
one with content: whatever the arm put back answers what the popped entry
answered, which is `runs_eff` read through the four rewrites above. -/

/-- The six opcodes a closure parks a thread at: the five consuming leaves
and the accept. Nothing else ever reaches a built list, which is what
makes the list step's last arm unreachable.

Like everything else here this reads the cell through `getElem!`, so it is
a claim about the opcode the step will dispatch on rather than about the
pc being inside the program — which is all the step asks, and all a pc
past the end could offer: it reads as the default `chr`. -/
def Parked (re : Re) (pc : Nat) : Prop :=
  (re.code[pc]! : Inst).op = Op.chr ∨ (re.code[pc]! : Inst).op = Op.chrCI ∨
    (re.code[pc]! : Inst).op = Op.cls ∨ (re.code[pc]! : Inst).op = Op.any ∨
    (re.code[pc]! : Inst).op = Op.anyNoNL ∨
    (re.code[pc]! : Inst).op = Op.accept

/-- What a fresh pc's arm leaves behind: the worklist with an expansion on
top, whatever the arm parked, the marked pc, the pool undisturbed away from
the handle the arm wrote through, and — the clause with the content — an
expansion answering what the popped entry answered.

Two of the clauses are there for the list step above rather than for the
closure itself: an arm parks only at an opcode the step knows how to
dispatch, and it leaves slot zero alone, since the writes it makes are a
save's — at slot two or above — and the counters', above the ovector
entirely. That slot is where the machine keeps a thread's attempt. -/
structure ArmOk (re : Re) (s : ByteArray) (mo : MOpts) (start attempt pos : Nat)
    (intoNext : Bool) (ext : List Nat) (st stA : PikeSt) (e : Entry)
    (ET Q : List Th) (E QE : List Entry) : Prop where
  stk : stkOf stA.stk = ET ++ stkOf st.stk.pop
  park : (parkList intoNext stA).toList = (parkList intoNext st).toList ++ Q
  seenMono : ∀ q : Nat, st.seen[q]! = true → stA.seen[q]! = true
  seenNew : ∀ q : Nat, stA.seen[q]! = true →
    q = st.stk.back!.pc ∨ st.seen[q]! = true
  seenSize : stA.seen.size = st.seen.size
  owned : Owned re.novec stA.rc stA.free stA.pool (buildLive intoNext stA ext)
  keep : ∀ k ∈ handles st.stk.pop ++ handles (parkList intoNext st) ++ ext,
    blockAt stA.pool re.novec k = blockAt st.pool re.novec k
  head : ThList re stA.pool pos ET E
  parked : ThList re stA.pool pos Q QE
  targets : ∀ x ∈ ET, x.pc ∈ epsTargets re.code re.reps st.stk.back!.pc
  fits : ∀ f ∈ E ++ QE, f.2.pos = pos ∧ Fit re s f.1 pos f.2.regs
  tag : ∀ f ∈ E ++ QE, (f.2.regs)[0]! = (e.2.regs)[0]!
  parks : ∀ f ∈ QE, Parked re f.1
  same : ∀ A : List MEntry, SameAfter re s mo start attempt A [e] (QE ++ E)

/-- And what an already marked pc's arm leaves behind: the worklist one
shorter and nothing else touched. -/
structure PopOk (re : Re) (intoNext : Bool) (ext : List Nat) (st stA : PikeSt) :
    Prop where
  stk : stkOf stA.stk = stkOf st.stk.pop
  park : (parkList intoNext stA).toList = (parkList intoNext st).toList
  seen : stA.seen = st.seen
  owned : Owned re.novec stA.rc stA.free stA.pool (buildLive intoNext stA ext)
  pool : stA.pool = st.pool

/-- A cell that reads as marked is a cell of the visited set: past its end
every read hands back the default. -/
private theorem lt_size_of_marked {seen : Array Bool} {q : Nat}
    (h : seen[q]! = true) : q < seen.size := by
  rcases Nat.lt_or_ge q seen.size with hlt | hge
  · exact hlt
  · rw [getElem!_neg seen q (by omega)] at h
    exact absurd h (by simp)

private theorem seen_mark_mono {seen : Array Bool} (pc : Nat) {q : Nat}
    (h : seen[q]! = true) : (seen.set! pc true)[q]! = true := by
  by_cases hq : q = pc
  · subst hq
    exact getBang_set_self seen (lt_size_of_marked h)
  · rw [getBang_set_other seen pc hq]
    exact h

private theorem seen_mark_new {seen : Array Bool} {pc q : Nat}
    (h : (seen.set! pc true)[q]! = true) : q = pc ∨ seen[q]! = true := by
  by_cases hq : q = pc
  · exact Or.inl hq
  · exact Or.inr (by rwa [getBang_set_other seen pc hq] at h)

set_option maxHeartbeats 4000000 in
/-- One iteration of the closure, read on both sides. The machine pops the
top of the worklist and either drops it as already marked or marks it and
puts back what its instruction defers to; the mirror at the same
configuration makes the very move `eff` names, and the four rewrites turn
that into an equivalence between the popped entry and what replaced it.
The two repetition cells are where eligibility is spent: the deciding head
always forks and a `repNext` always returns to it, so the machine's one
step through both is the mirror's two. -/
theorem pikeAdd_go_step {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {intoNext : Bool} {start attempt pos : Nat} {ext : List Nat} {fuel : Nat}
    {st st' : PikeSt} {u : Spec.Thread}
    (he : Eligible re) (hs : s.size ≤ ceiling)
    (hgo : pikeAdd.go re s mo lim intoNext pos (fuel + 1) st = .ok st')
    (hne : 0 < st.stk.size)
    (how : Owned re.novec st.rc st.free st.pool (buildLive intoNext st ext))
    (hat : ThAt re st.pool pos st.stk.back! (st.stk.back!.pc, u))
    (hpos : u.pos = pos) (hfit : Fit re s st.stk.back!.pc pos u.regs) :
    ∃ stA, pikeAdd.go re s mo lim intoNext pos fuel stA = .ok st' ∧
      ((st.seen[st.stk.back!.pc]! = true ∧ PopOk re intoNext ext st stA) ∨
        (st.seen[st.stk.back!.pc]! = false ∧ ∃ ET Q E QE,
          ArmOk re s mo start attempt pos intoNext ext st stA
            (st.stk.back!.pc, u) ET Q E QE)) := by
  subst hpos
  have hflight := owned_pop (intoNext := intoNext) (ext := ext) hne how
  have hlt31 : u.pos < 2 ^ 31 := hfit.lt hs
  have hnov := he.novec
  -- The four shapes an arm can take, each read off the marked state
  -- through the fields the reading looks at.
  have harmPark : ∀ (stA stB : PikeSt),
      pikePark stA intoNext st.stk.back!.pc st.stk.back!.h lim = .ok stB →
      stA.stk = st.stk.pop → stA.seen = st.seen.set! st.stk.back!.pc true →
      stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
      stA.clist = st.clist → stA.nlist = st.nlist →
      Parked re st.stk.back!.pc →
      ∃ ET Q E QE, ArmOk re s mo start attempt u.pos intoNext ext st stB
        (st.stk.back!.pc, u) ET Q E QE := by
    intro stA stB hpk hstkA hseenA hrcA hfreeA hpoolA hclA hnlA hpark0
    have hparkA : parkList intoNext stA = parkList intoNext st :=
      parkList_eq hclA hnlA
    have hstA : Owned re.novec stA.rc stA.free stA.pool
        (st.stk.back!.h :: buildLive intoNext stA ext) := by
      rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
      exact hflight
    obtain ⟨hkP, heP⟩ := pikePark_ok hpk
    obtain ⟨hT, hF⟩ := pikePark_lists hpk
    have hplP : stB.pool = stA.pool := pikePark_pool hpk
    refine ⟨[], [st.stk.back!], [], [(st.stk.back!.pc, u)], ?_, ?_, ?_, ?_, ?_,
      park_owned hpk hstA, ?_, List.Forall₂.nil, ?_, ?_, ?_, ?_, ?_,
      fun _ => .refl⟩
    · rw [hkP, hstkA]
      rfl
    · rw [parkList_push hT hF, hparkA, Array.toList_push]
    · intro q hq
      rw [heP, hseenA]
      exact seen_mark_mono _ hq
    · intro q hq
      rw [heP, hseenA] at hq
      exact seen_mark_new hq
    · rw [heP, hseenA, Array.size_set!]
    · intro k _
      rw [hplP, hpoolA]
    · exact List.Forall₂.cons (by rw [hplP, hpoolA]; exact hat) List.Forall₂.nil
    · intro x hx
      simp at hx
    · intro f hf
      simp only [List.nil_append, List.mem_singleton] at hf
      subst hf
      exact ⟨rfl, hfit⟩
    · intro f hf
      simp only [List.nil_append, List.mem_singleton] at hf
      subst hf
      rfl
    · intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact hpark0
  have harmFail : ∀ (stA stB : PikeSt),
      pikeDrop stA st.stk.back!.h lim = .ok stB →
      stA.stk = st.stk.pop → stA.seen = st.seen.set! st.stk.back!.pc true →
      stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
      stA.clist = st.clist → stA.nlist = st.nlist →
      (∀ A : List MEntry,
        SameAfter re s mo start attempt A [(st.stk.back!.pc, u)] []) →
      ∃ ET Q E QE, ArmOk re s mo start attempt u.pos intoNext ext st stB
        (st.stk.back!.pc, u) ET Q E QE := by
    intro stA stB hdr hstkA hseenA hrcA hfreeA hpoolA hclA hnlA hsame
    have hparkA : parkList intoNext stA = parkList intoNext st :=
      parkList_eq hclA hnlA
    have hstA : Owned re.novec stA.rc stA.free stA.pool
        (st.stk.back!.h :: buildLive intoNext stA ext) := by
      rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
      exact hflight
    obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
    obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
    have hplD : stB.pool = stA.pool := pikeDrop_pool hdr
    refine ⟨[], [], [], [], ?_, ?_, ?_, ?_, ?_, drop_owned hdr hstA, ?_,
      List.Forall₂.nil, List.Forall₂.nil, ?_, ?_, ?_, ?_, hsame⟩
    · rw [hkD, hstkA]
      simp
    · rw [parkList_eq hclD hnlD, hparkA]
      simp
    · intro q hq
      rw [heD, hseenA]
      exact seen_mark_mono _ hq
    · intro q hq
      rw [heD, hseenA] at hq
      exact seen_mark_new hq
    · rw [heD, hseenA, Array.size_set!]
    · intro k _
      rw [hplD, hpoolA]
    · intro x hx
      simp at hx
    · intro f hf
      simp at hf
    · intro f hf
      simp at hf
    · intro f hf
      simp at hf
  have harmGoto : ∀ (stA stB : PikeSt) (pcT : Nat) (v : Spec.Thread),
      pikeDefer stA pcT st.stk.back!.h lim = .ok stB →
      stA.stk = st.stk.pop → stA.seen = st.seen.set! st.stk.back!.pc true →
      stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
      stA.clist = st.clist → stA.nlist = st.nlist →
      pcT ∈ epsTargets re.code re.reps st.stk.back!.pc →
      ThAt re st.pool u.pos ⟨pcT, st.stk.back!.h⟩ (pcT, v) →
      v.pos = u.pos → Fit re s pcT u.pos v.regs →
      (v.regs)[0]! = (u.regs)[0]! →
      (∀ A : List MEntry, SameAfter re s mo start attempt A
        [(st.stk.back!.pc, u)] [(pcT, v)]) →
      ∃ ET Q E QE, ArmOk re s mo start attempt u.pos intoNext ext st stB
        (st.stk.back!.pc, u) ET Q E QE := by
    intro stA stB pcT v hdf hstkA hseenA hrcA hfreeA hpoolA hclA hnlA htgt
      hthat hvpos hvfit hlow hsame
    have hparkA : parkList intoNext stA = parkList intoNext st :=
      parkList_eq hclA hnlA
    have hstA : Owned re.novec stA.rc stA.free stA.pool
        (st.stk.back!.h :: buildLive intoNext stA ext) := by
      rw [hrcA, hfreeA, hpoolA, buildLive, hstkA, hparkA]
      exact hflight
    obtain ⟨hkD, heD⟩ := pikeDefer_ok hdf
    obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdf
    have hplD : stB.pool = stA.pool := pikeDefer_pool hdf
    refine ⟨[⟨pcT, st.stk.back!.h⟩], [], [(pcT, v)], [], ?_, ?_, ?_, ?_, ?_,
      defer_owned hdf hstA, ?_, ?_, List.Forall₂.nil, ?_, ?_, ?_, ?_, hsame⟩
    · rw [hkD, hstkA, stkOf_push]
      rfl
    · rw [parkList_eq hclD hnlD, hparkA]
      simp
    · intro q hq
      rw [heD, hseenA]
      exact seen_mark_mono _ hq
    · intro q hq
      rw [heD, hseenA] at hq
      exact seen_mark_new hq
    · rw [heD, hseenA, Array.size_set!]
    · intro k _
      rw [hplD, hpoolA]
    · exact List.Forall₂.cons (by rw [hplD, hpoolA]; exact hthat) List.Forall₂.nil
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact htgt
    · intro f hf
      simp only [List.append_nil, List.mem_singleton] at hf
      subst hf
      exact ⟨hvpos, hvfit⟩
    · intro f hf
      simp only [List.append_nil, List.mem_singleton] at hf
      subst hf
      exact hlow
    · intro f hf
      simp at hf
  have harmFork : ∀ (stR stB stC : PikeSt) (p q : Nat) (v : Spec.Thread),
      pikeDefer stR q st.stk.back!.h lim = .ok stB →
      pikeDefer stB p st.stk.back!.h lim = .ok stC →
      stR.stk = st.stk.pop → stR.seen = st.seen.set! st.stk.back!.pc true →
      stR.rc = st.rc.set! st.stk.back!.h (st.rc[st.stk.back!.h]! + 1) →
      stR.free = st.free → stR.pool = st.pool →
      stR.clist = st.clist → stR.nlist = st.nlist →
      p ∈ epsTargets re.code re.reps st.stk.back!.pc →
      q ∈ epsTargets re.code re.reps st.stk.back!.pc →
      ThAt re st.pool u.pos ⟨p, st.stk.back!.h⟩ (p, v) →
      ThAt re st.pool u.pos ⟨q, st.stk.back!.h⟩ (q, v) →
      v.pos = u.pos → Fit re s p u.pos v.regs → Fit re s q u.pos v.regs →
      (v.regs)[0]! = (u.regs)[0]! →
      (∀ A : List MEntry, SameAfter re s mo start attempt A
        [(st.stk.back!.pc, u)] [(p, v), (q, v)]) →
      ∃ ET Q E QE, ArmOk re s mo start attempt u.pos intoNext ext st stC
        (st.stk.back!.pc, u) ET Q E QE := by
    intro stR stB stC p q v hd1 hd2 hstkR hseenR hrcR hfreeR hpoolR hclR hnlR
      htgtP htgtQ hthatP hthatQ hvpos hfitP hfitQ hlow hsame
    have hparkR : parkList intoNext stR = parkList intoNext st :=
      parkList_eq hclR hnlR
    have hstR : Owned re.novec stR.rc stR.free stR.pool
        (st.stk.back!.h :: st.stk.back!.h :: buildLive intoNext stR ext) := by
      rw [hrcR, hfreeR, hpoolR, buildLive, hstkR, hparkR]
      exact owned_share hflight
    obtain ⟨hk1, he1⟩ := pikeDefer_ok hd1
    obtain ⟨hcl1, hnl1⟩ := pikeDefer_lists hd1
    have hpl1 : stB.pool = stR.pool := pikeDefer_pool hd1
    obtain ⟨hk2, he2⟩ := pikeDefer_ok hd2
    obtain ⟨hcl2, hnl2⟩ := pikeDefer_lists hd2
    have hpl2 : stC.pool = stB.pool := pikeDefer_pool hd2
    refine ⟨[⟨p, st.stk.back!.h⟩, ⟨q, st.stk.back!.h⟩], [],
      [(p, v), (q, v)], [], ?_, ?_, ?_, ?_, ?_,
      defer_owned hd2 (defer_owned_two hd1 hstR), ?_, ?_, List.Forall₂.nil,
      ?_, ?_, ?_, ?_, hsame⟩
    · rw [hk2, hk1, hstkR, stkOf_push, stkOf_push]
      rfl
    · rw [parkList_eq hcl2 hnl2, parkList_eq hcl1 hnl1, hparkR]
      simp
    · intro x hx
      rw [he2, he1, hseenR]
      exact seen_mark_mono _ hx
    · intro x hx
      rw [he2, he1, hseenR] at hx
      exact seen_mark_new hx
    · rw [he2, he1, hseenR, Array.size_set!]
    · intro k _
      rw [hpl2, hpl1, hpoolR]
    · exact List.Forall₂.cons (by rw [hpl2, hpl1, hpoolR]; exact hthatP)
        (List.Forall₂.cons (by rw [hpl2, hpl1, hpoolR]; exact hthatQ)
          List.Forall₂.nil)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact htgtP
      · exact htgtQ
    · intro f hf
      simp only [List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hf
      rcases hf with rfl | rfl
      · exact ⟨hvpos, hfitP⟩
      · exact ⟨hvpos, hfitQ⟩
    · intro f hf
      simp only [List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hf
      rcases hf with rfl | rfl
      · exact hlow
      · exact hlow
    · intro f hf
      simp at hf
  have harmSave : ∀ (stR stW stB : PikeSt) (slot hOut : Nat),
      pikeWrite stR re.novec st.stk.back!.h slot u.pos.toUInt32 lim
        = .ok (stW, hOut) →
      pikeDefer stW (st.stk.back!.pc + 1) hOut lim = .ok stB →
      stR.stk = st.stk.pop → stR.seen = st.seen.set! st.stk.back!.pc true →
      stR.rc = st.rc → stR.free = st.free → stR.pool = st.pool →
      stR.clist = st.clist → stR.nlist = st.nlist →
      slot < re.novec → slot ≠ 0 →
      st.stk.back!.pc + 1 ∈ epsTargets re.code re.reps st.stk.back!.pc →
      Fit re s (st.stk.back!.pc + 1) u.pos (u.regs.set! slot u.pos.toUInt32) →
      (∀ A : List MEntry, SameAfter re s mo start attempt A
        [(st.stk.back!.pc, u)]
        [(st.stk.back!.pc + 1, ⟨u.pos, u.regs.set! slot u.pos.toUInt32⟩)]) →
      ∃ ET Q E QE, ArmOk re s mo start attempt u.pos intoNext ext st stB
        (st.stk.back!.pc, u) ET Q E QE := by
    intro stR stW stB slot hOut hw hdf hstkR hseenR hrcR hfreeR hpoolR hclR hnlR
      hslot hslot0 htgt hvfit hsame
    have hparkR : parkList intoNext stR = parkList intoNext st :=
      parkList_eq hclR hnlR
    have hlive : buildLive intoNext stR ext =
        handles st.stk.pop ++ handles (parkList intoNext st) ++ ext := by
      rw [buildLive, hstkR, hparkR]
    have hstR : Owned re.novec stR.rc stR.free stR.pool
        (st.stk.back!.h :: buildLive intoNext stR ext) := by
      rw [hrcR, hfreeR, hpoolR, hlive]
      exact hflight
    obtain ⟨hwo, _⟩ := write_owned hw hstR
    obtain ⟨hkW, heW⟩ := pikeWrite_ok hw
    obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hw
    obtain ⟨hkD, heD⟩ := pikeDefer_ok hdf
    obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdf
    have hplD : stB.pool = stW.pool := pikeDefer_pool hdf
    have hfresh : hOut ∉ buildLive intoNext stR ext := pikeWrite_fresh hstR hw
    have hkeep : ∀ k ∈ handles st.stk.pop ++ handles (parkList intoNext st) ++ ext,
        blockAt stW.pool re.novec k = blockAt stR.pool re.novec k := by
      intro k hk
      rw [← hlive] at hk
      refine pikeWrite_block_keep_owned hslot ?_ (List.mem_cons_of_mem _ hk)
        hstR hw
      intro hkk
      rw [hkk] at hk
      exact hfresh hk
    refine ⟨[⟨st.stk.back!.pc + 1, hOut⟩], [],
      [(st.stk.back!.pc + 1, ⟨u.pos, u.regs.set! slot u.pos.toUInt32⟩)], [],
      ?_, ?_, ?_, ?_, ?_, defer_owned hdf hwo, ?_, ?_, List.Forall₂.nil,
      ?_, ?_, ?_, ?_, hsame⟩
    · rw [hkD, hkW, hstkR, stkOf_push]
      rfl
    · rw [parkList_eq hclD hnlD, parkList_eq hclW hnlW, hparkR]
      simp
    · intro x hx
      rw [heD, heW, hseenR]
      exact seen_mark_mono _ hx
    · intro x hx
      rw [heD, heW, hseenR] at hx
      exact seen_mark_new hx
    · rw [heD, heW, hseenR, Array.size_set!]
    · intro k hk
      rw [hplD, hkeep k hk, hpoolR]
    · refine List.Forall₂.cons ?_ List.Forall₂.nil
      rw [hplD]
      exact ThAt.write (st := stR) hslot hstR hw (by rw [hpoolR]; exact hat) _
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact htgt
    · intro f hf
      simp only [List.append_nil, List.mem_singleton] at hf
      subst hf
      exact ⟨rfl, hvfit⟩
    · intro f hf
      simp only [List.append_nil, List.mem_singleton] at hf
      subst hf
      exact getBang_set_other u.regs slot (Ne.symm hslot0)
    · intro f hf
      simp at hf
  simp only [pikeAdd.go] at hgo
  split at hgo
  · rename_i hemp
    simp only [beq_iff_eq] at hemp
    omega
  · split at hgo
    · rename_i hseenT
      have hmark : st.seen[st.stk.back!.pc]! = true := by simpa using hseenT
      split at hgo
      · exact absurd_error hgo
      · rename_i stD hdr
        obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
        obtain ⟨hclD, hnlD⟩ := pikeDrop_lists hdr
        refine ⟨stD, hgo, Or.inl ⟨hmark, ?_, ?_, ?_, drop_owned hdr hflight, ?_⟩⟩
        · rw [hkD]
        · rw [parkList_eq hclD hnlD]
          rfl
        · rw [heD]
        · rw [pikeDrop_pool hdr]
    · rename_i hseenF
      have hfalse : st.seen[st.stk.back!.pc]! = false := by simpa using hseenF
      split at hgo
      · exact absurd_error hgo
      · cases hop : (re.code[(st.stk.back!).pc]!).op <;> simp only [hop] at hgo
        case bsr => exact absurd hop (op_ne_bsr he.ok _)
        case chr | chrCI | cls | any | anyNoNL | accept =>
          split at hgo
          · exact absurd_error hgo
          · rename_i stB hpk
            exact ⟨stB, hgo, Or.inr ⟨hfalse,
              harmPark _ _ hpk rfl rfl rfl rfl rfl rfl rfl
                (by simp [Parked, hop])⟩⟩
        case «split» =>
          have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
              .fork (re.code[st.stk.back!.pc]!).arg
                (re.code[st.stk.back!.pc]!).alt := by
            simp only [eff, hop]
          obtain ⟨hf1, hf2⟩ := eff_fit_fork he.cells he.rows he.mid hfit heff
          split at hgo
          · exact absurd_error hgo
          · rename_i stB hd1
            split at hgo
            · exact absurd_error hgo
            · rename_i stC hd2
              exact ⟨stC, hgo, Or.inr ⟨hfalse,
                harmFork _ _ _ _ _ u hd1 hd2 rfl rfl rfl rfl rfl rfl rfl
                  (by simp [epsTargets, hop]) (by simp [epsTargets, hop])
                  (hat.goto _) (hat.goto _) rfl hf1 hf2 rfl
                  (fun A => sameAfter_fork heff)⟩⟩
        case jump =>
          have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
              .goto (re.code[st.stk.back!.pc]!).arg u.pos u.regs := by
            simp only [eff, hop]
          split at hgo
          · exact absurd_error hgo
          · rename_i stB hdf
            exact ⟨stB, hgo, Or.inr ⟨hfalse,
              harmGoto _ _ _ u hdf rfl rfl rfl rfl rfl rfl rfl
                (by simp [epsTargets, hop]) (hat.goto _) rfl
                (eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff) rfl
                (fun A => sameAfter_goto heff)⟩⟩
        case save =>
          have hslot2 := (he.cells.save st.stk.back!.pc hop).1
          have hslot := (he.cells.save st.stk.back!.pc hop).2
          have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
              .goto (st.stk.back!.pc + 1) u.pos
                (u.regs.set! (re.code[st.stk.back!.pc]!).arg
                  u.pos.toUInt32) := by
            simp only [eff, hop]
          split at hgo
          · exact absurd_error hgo
          · rename_i stW hOut hw
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hdf
              exact ⟨stB, hgo, Or.inr ⟨hfalse,
                harmSave _ _ _ _ _ hw hdf rfl rfl rfl rfl rfl rfl rfl hslot
                  (by omega) (by simp [epsTargets, hop])
                  (eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff)
                  (fun A => sameAfter_goto heff)⟩⟩
        case repZero =>
          have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
              .goto (st.stk.back!.pc + 1) u.pos
                (u.regs.set! (re.novec + (re.code[st.stk.back!.pc]!).arg * 2)
                  0) := by
            simp only [eff, hop]
          split at hgo
          · exact absurd_error hgo
          · rename_i stB hdf
            exact ⟨stB, hgo, Or.inr ⟨hfalse,
              harmGoto _ _ _ _ hdf rfl rfl rfl rfl rfl rfl rfl
                (by simp [epsTargets, hop]) (hat.bump (by omega) _) rfl
                (eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff)
                (getBang_set_other u.regs
                  (re.novec + (re.code[st.stk.back!.pc]!).arg * 2) (by omega))
                (fun A => sameAfter_goto heff)⟩⟩
        case repEnter =>
          have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
              .goto (st.stk.back!.pc + 1) u.pos
                (u.regs.set!
                  (re.novec + (re.code[st.stk.back!.pc]!).arg * 2 + 1)
                  u.pos.toUInt32) := by
            simp only [eff, hop]
          split at hgo
          · exact absurd_error hgo
          · rename_i stB hdf
            exact ⟨stB, hgo, Or.inr ⟨hfalse,
              harmGoto _ _ _ _ hdf rfl rfl rfl rfl rfl rfl rfl
                (by simp [epsTargets, hop]) (hat.bump (by omega) _) rfl
                (eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff)
                (getBang_set_other u.regs
                  (re.novec + (re.code[st.stk.back!.pc]!).arg * 2 + 1)
                  (by omega))
                (fun A => sameAfter_goto heff)⟩⟩
        case repLoop =>
          have heff := eff_repLoop_forks (s := s) (mo := mo) (start := start)
            (attempt := attempt) he.ok he.cells he.rows hop hlt31 hfit.2.2.1
            hfit.2.2.2.2
          split at hgo <;> rename_i hgr
          · rw [if_pos hgr] at heff
            obtain ⟨hf1, hf2⟩ := eff_fit_fork he.cells he.rows he.mid hfit heff
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hd1
              split at hgo
              · exact absurd_error hgo
              · rename_i stC hd2
                exact ⟨stC, hgo, Or.inr ⟨hfalse,
                  harmFork _ _ _ _ _ u hd1 hd2 rfl rfl rfl rfl rfl rfl rfl
                    (by simp [epsTargets, hop, hgr])
                    (by simp [epsTargets, hop, hgr])
                    (hat.goto _) (hat.goto _) rfl hf1 hf2 rfl
                    (fun A => sameAfter_fork heff)⟩⟩
          · rw [if_neg (by simpa using hgr)] at heff
            obtain ⟨hf1, hf2⟩ := eff_fit_fork he.cells he.rows he.mid hfit heff
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hd1
              split at hgo
              · exact absurd_error hgo
              · rename_i stC hd2
                exact ⟨stC, hgo, Or.inr ⟨hfalse,
                  harmFork _ _ _ _ _ u hd1 hd2 rfl rfl rfl rfl rfl rfl rfl
                    (by simp [epsTargets, hop, hgr])
                    (by simp [epsTargets, hop, hgr])
                    (hat.goto _) (hat.goto _) rfl hf1 hf2 rfl
                    (fun A => sameAfter_fork heff)⟩⟩
        case repNext =>
          obtain ⟨harg, hnextq⟩ := he.cells.next st.stk.back!.pc hop
          have hrow := he.rows _ harg
          have heff1 := eff_repNext_loops (s := s) (mo := mo) (start := start)
            (attempt := attempt) hop harg hnextq hfit.2.2.2.1
          have hvfit := eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff1
          have hhop : (re.code[(re.reps[(re.code[st.stk.back!.pc]!).arg]!).head]!).op
              = Op.repLoop := by rw [hrow.head]
          have hharg : (re.code[(re.reps[(re.code[st.stk.back!.pc]!).arg]!).head]!).arg
              = (re.code[st.stk.back!.pc]!).arg := by rw [hrow.head]
          have heff2 := eff_repLoop_forks (s := s) (mo := mo) (start := start)
            (attempt := attempt) he.ok he.cells he.rows hhop hlt31 hvfit.2.2.1
            hvfit.2.2.2.2
          rw [hharg] at heff2
          split at hgo <;> rename_i hgr
          · rw [if_pos hgr] at heff2
            obtain ⟨hf1, hf2⟩ := eff_fit_fork he.cells he.rows he.mid hvfit heff2
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hd1
              split at hgo
              · exact absurd_error hgo
              · rename_i stC hd2
                exact ⟨stC, hgo, Or.inr ⟨hfalse,
                  harmFork _ _ _ _ _ _ hd1 hd2 rfl rfl rfl rfl rfl rfl rfl
                    (by simp [epsTargets, hop, hgr])
                    (by simp [epsTargets, hop, hgr])
                    (hat.bump (by omega) _) (hat.bump (by omega) _) rfl hf1 hf2
                    (getBang_set_other u.regs
                      (re.novec + (re.code[st.stk.back!.pc]!).arg * 2)
                      (by omega))
                    (fun A => (sameAfter_goto heff1).trans
                      (sameAfter_fork heff2))⟩⟩
          · rw [if_neg (by simpa using hgr)] at heff2
            obtain ⟨hf1, hf2⟩ := eff_fit_fork he.cells he.rows he.mid hvfit heff2
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hd1
              split at hgo
              · exact absurd_error hgo
              · rename_i stC hd2
                exact ⟨stC, hgo, Or.inr ⟨hfalse,
                  harmFork _ _ _ _ _ _ hd1 hd2 rfl rfl rfl rfl rfl rfl rfl
                    (by simp [epsTargets, hop, hgr])
                    (by simp [epsTargets, hop, hgr])
                    (hat.bump (by omega) _) (hat.bump (by omega) _) rfl hf1 hf2
                    (getBang_set_other u.regs
                      (re.novec + (re.code[st.stk.back!.pc]!).arg * 2)
                      (by omega))
                    (fun A => (sameAfter_goto heff1).trans
                      (sameAfter_fork heff2))⟩⟩
        case circ | doll | dollE | sod | eod | eodn | wordB | notWordB =>
          split at hgo <;> rename_i hcnd
          · have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
                .goto (st.stk.back!.pc + 1) u.pos u.regs := by
              simp only [eff, hop]
              rw [if_pos hcnd]
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hdf
              exact ⟨stB, hgo, Or.inr ⟨hfalse,
                harmGoto _ _ _ u hdf rfl rfl rfl rfl rfl rfl rfl
                  (by simp [epsTargets, hop]) (hat.goto _) rfl
                  (eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff) rfl
                  (fun A => sameAfter_goto heff)⟩⟩
          · have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
                .fail := by
              simp only [eff, hop]
              rw [if_neg hcnd]
            split at hgo
            · exact absurd_error hgo
            · rename_i stB hdr
              exact ⟨stB, hgo, Or.inr ⟨hfalse,
                harmFail _ _ hdr rfl rfl rfl rfl rfl rfl rfl
                  (fun A => sameAfter_fail heff)⟩⟩
        case circM | dollM =>
          split at hgo <;> rename_i hz <;> split at hgo <;> rename_i hcnd
          all_goals first
            | (have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
                   .goto (st.stk.back!.pc + 1) u.pos u.regs := by
                 simp only [eff, hop]
                 first
                   | rw [if_pos hz, if_pos hcnd]
                   | rw [if_neg hz, if_pos hcnd]
               split at hgo
               · exact absurd_error hgo
               · rename_i stB hdf
                 exact ⟨stB, hgo, Or.inr ⟨hfalse,
                   harmGoto _ _ _ u hdf rfl rfl rfl rfl rfl rfl rfl
                     (by simp [epsTargets, hop]) (hat.goto _) rfl
                     (eff_fit_goto he.ok he.cells he.rows he.mid hs hfit heff)
                     rfl (fun A => sameAfter_goto heff)⟩⟩)
            | (have heff : eff re s mo start attempt st.stk.back!.pc u.pos u.regs =
                   .fail := by
                 simp only [eff, hop]
                 first
                   | rw [if_pos hz, if_neg hcnd]
                   | rw [if_neg hz, if_neg hcnd]
               split at hgo
               · exact absurd_error hgo
               · rename_i stB hdr
                 exact ⟨stB, hgo, Or.inr ⟨hfalse,
                   harmFail _ _ hdr rfl rfl rfl rfl rfl rfl rfl
                     (fun A => sameAfter_fail heff)⟩⟩)

/-! ## The closure correspondence

The worklist drains top down, so a stretch of it can be watched on its own:
`pikeAdd_go_refine` runs the loop until the entries above a chosen point
are gone, and says what the parked list gained in their place. Two things
travel with it.

The first is the answer: what the closure parked answers what the stretch
it consumed answered, read behind the parked list already settled. That is
`SameAfter`, and it composes down the recursion because every arm is one
of the four rewrites and the loop only ever replaces the top entry.

The second is what makes the visited set sound, and it is where the
acyclicity is spent. A marked pc is one of two things: settled, meaning a
stretch of the parked list already answers for it, or out of reach of
everything still on the stretch being drained. When the closure marks a pc
and pushes its expansion, the pc is neither settled nor reachable from its
own expansion — that would be a walk that stepped out and came back — so
the expansion runs under the second reading, and by the time it is done
the stretch it parked is the pc's own settlement. That is why the
invariant has to speak about the stack rather than about the parked prefix
alone: at the moment of marking the expansion is on the worklist, and only
draining it moves the settlement into place. -/

set_option maxHeartbeats 2000000 in
/-- One stretch of the worklist, drained. The entries below it are
untouched, the parked list grew by a stretch answering what the drained
one answered, and every pc the drain marked is one the parked list now
answers for. -/
theorem pikeAdd_go_refine {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {intoNext : Bool} {start attempt pos : Nat} {tag : UInt32} {ext : List Nat}
    (he : Eligible re) (hs : s.size ≤ ceiling) :
    attempt ≤ pos →
    ∀ (fuel : Nat) (st st' : PikeSt) (KT AT : List Th) (KL AL : List Entry)
      (P : List MEntry),
      pikeAdd.go re s mo lim intoNext pos fuel st = .ok st' →
      stkOf st.stk = KT ++ AT →
      Owned re.novec st.rc st.free st.pool (buildLive intoNext st ext) →
      ThList re st.pool pos KT KL → ThList re st.pool pos AT AL →
      ThList re st.pool pos (parkList intoNext st).toList (untag P) →
      (∀ e ∈ KL, e.2.pos = pos ∧ Fit re s e.1 pos e.2.regs) →
      (∀ e ∈ KL, (e.2.regs)[0]! = tag) →
      (∀ q : Nat, st.seen[q]! = true →
        Settled re s mo start attempt pos P q ∨
          ∀ e ∈ KL, ¬ EpsReach re.code re.reps e.1 q) →
      ∃ (stM : PikeSt) (fuelM : Nat) (N : List Entry),
        fuelM ≤ fuel ∧
        pikeAdd.go re s mo lim intoNext pos fuelM stM = .ok st' ∧
        stkOf stM.stk = AT ∧
        Owned re.novec stM.rc stM.free stM.pool (buildLive intoNext stM ext) ∧
        ThList re stM.pool pos AT AL ∧
        ThList re stM.pool pos (parkList intoNext stM).toList (untag P ++ N) ∧
        SameAfter re s mo start attempt P KL N ∧
        (∀ e ∈ N, e.2.pos = pos ∧ Fit re s e.1 pos e.2.regs) ∧
        (∀ e ∈ N, (e.2.regs)[0]! = tag) ∧
        (∀ e ∈ N, Parked re e.1) ∧
        (∀ k ∈ ext, blockAt stM.pool re.novec k = blockAt st.pool re.novec k) ∧
        (∀ q : Nat, st.seen[q]! = true → stM.seen[q]! = true) ∧
        (∀ q : Nat, stM.seen[q]! = true →
          Settled re s mo start attempt pos (P ++ tagAtt attempt N) q ∨
            (st.seen[q]! = true ∧
              ∀ e ∈ KL, ¬ EpsReach re.code re.reps e.1 q)) := by
  intro hatt fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro st st' KT AT KL AL P hgo hstk how hKT hAT hP hfitK hlowK hseen
  unfold ThList at hKT
  cases hKT with
  | nil =>
      exact ⟨st, fuel, [], Nat.le_refl _, hgo, by simpa using hstk, how,
        hAT, by simpa using hP, SameAfter.refl, by simp, by simp, by simp,
        fun _ _ => rfl, fun _ h => h, fun q hq => Or.inr ⟨hq, by simp⟩⟩
  | @cons th e KT' KL' hate hrest =>
      obtain ⟨eP, eT⟩ := e
      have hthpc : eP = th.pc := hate.1
      subst hthpc
      have hpos0 : 0 < st.stk.size := by
        rcases Nat.eq_zero_or_pos st.stk.size with hz | hp
        · rw [stkOf_nil hz] at hstk
          simp at hstk
        · exact hp
      have hcons : th :: (KT' ++ AT) = st.stk.back! :: stkOf st.stk.pop := by
        rw [← stkOf_pop hpos0, hstk]
        rfl
      injection hcons with hthb hrestk
      subst hthb
      have hfitE := hfitK (st.stk.back!.pc, eT) List.mem_cons_self
      cases fuel with
      | zero =>
          rw [pikeAdd.go] at hgo
          exact absurd hgo (by simp)
      | succ f =>
          obtain ⟨stA, hgoA, harm⟩ :=
            pikeAdd_go_step (start := start) (attempt := attempt) he hs hgo
              hpos0 how hate hfitE.1 hfitE.2
          rcases harm with ⟨hmark, hpop⟩ | ⟨hfresh, ET, Q, E, QE, harm⟩
          · have hset : Settled re s mo start attempt pos P st.stk.back!.pc := by
              rcases hseen _ hmark with h | h
              · exact h
              · exact absurd EpsReach.refl (h (st.stk.back!.pc, eT) List.mem_cons_self)
            have hdrop :
                SameAfter re s mo start attempt P [(st.stk.back!.pc, eT)] [] := by
              intro Y back r
              have hd := hset.drop he hs hfitE.1 hatt hfitE.2 [] Y back r
              simpa [tagAtt] using hd
            have hpool : stA.pool = st.pool := hpop.pool
            obtain ⟨stM, fuelM, N, hfM, hgoM, hstkM, howM, hATM, hPM, hsameM,
              hfitN, hlowN, hparkN, hextM, hmonoM, hqM⟩ :=
              ih f (by omega) stA st' KT' AT KL' AL P hgoA
                (by rw [hpop.stk, ← hrestk]) hpop.owned
                (ThList.ofPool hrest (fun _ _ => by rw [hpool]))
                (hAT.ofPool (fun _ _ => by rw [hpool]))
                (by rw [hpop.park]; exact hP.ofPool (fun _ _ => by rw [hpool]))
                (fun x hx => hfitK x (List.mem_cons_of_mem _ hx))
                (fun x hx => hlowK x (List.mem_cons_of_mem _ hx))
                (fun q hq => by
                  rw [hpop.seen] at hq
                  rcases hseen q hq with h | h
                  · exact Or.inl h
                  · exact Or.inr (fun x hx => h x (List.mem_cons_of_mem _ hx)))
            refine ⟨stM, fuelM, N, by omega, hgoM, hstkM, howM, hATM, hPM, ?_,
              hfitN, hlowN, hparkN, ?_, ?_, ?_⟩
            · refine SameAfter.comp hdrop ?_
              rw [show tagAtt attempt ([] : List Entry) = [] from rfl,
                List.append_nil]
              exact hsameM
            · intro k hk
              rw [hextM k hk, hpool]
            · exact fun q hq => hmonoM q (by rw [hpop.seen]; exact hq)
            · intro q hq
              rcases hqM q hq with h | ⟨h1, _⟩
              · exact Or.inl h
              · rw [hpop.seen] at h1
                rcases hseen q h1 with hA | hA
                · exact Or.inl (hA.mono (tagAtt attempt N))
                · exact Or.inr ⟨h1, hA⟩
          · have hstkA : stkOf stA.stk = ET ++ (KT' ++ AT) := by
              rw [harm.stk, hrestk]
            have hkeepP : ∀ x ∈ (parkList intoNext st).toList,
                blockAt stA.pool re.novec x.h
                  = blockAt st.pool re.novec x.h := fun x hx =>
              harm.keep x.h (List.mem_append_left _
                (List.mem_append_right _ (mem_handles_of_toList hx)))
            have hkeepS : ∀ x ∈ KT' ++ AT,
                blockAt stA.pool re.novec x.h
                  = blockAt st.pool re.novec x.h := by
              intro x hx
              refine harm.keep x.h
                (List.mem_append_left _ (List.mem_append_left _ ?_))
              exact mem_handles_of_stkOf (by rw [← hrestk]; exact hx)
            have hPA : ThList re stA.pool pos (parkList intoNext stA).toList
                (untag (P ++ tagAtt attempt QE)) := by
              rw [untag_append, untag_tagAtt, harm.park]
              exact ThList.append (ThList.ofPool hP hkeepP) harm.parked
            have hSA : ThList re stA.pool pos (KT' ++ AT) (KL' ++ AL) :=
              ThList.append
                (ThList.ofPool hrest (fun x hx => hkeepS x (List.mem_append_left _ hx)))
                (hAT.ofPool (fun x hx => hkeepS x (List.mem_append_right _ hx)))
            have htgtE : ∀ x ∈ E,
                x.1 ∈ epsTargets re.code re.reps st.stk.back!.pc := by
              intro x hx
              obtain ⟨y, hy, hya⟩ := harm.head.mem_left hx
              rw [hya.1]
              exact harm.targets y hy
            have hseenA : ∀ q : Nat, stA.seen[q]! = true →
                Settled re s mo start attempt pos (P ++ tagAtt attempt QE) q ∨
                  ∀ x ∈ E, ¬ EpsReach re.code re.reps x.1 q := by
              intro q hq
              rcases harm.seenNew q hq with rfl | hq'
              · exact Or.inr (fun x hx hr => he.noCycle (htgtE x hx) hr)
              · rcases hseen q hq' with hS | hS
                · exact Or.inl (hS.mono (tagAtt attempt QE))
                · exact Or.inr (fun x hx hr =>
                    hS (st.stk.back!.pc, eT) List.mem_cons_self
                      ((EpsReach.one (htgtE x hx)).trans hr))
            have hlowE : ∀ x ∈ E, (x.2.regs)[0]! = tag := fun x hx =>
              (harm.tag x (List.mem_append_left _ hx)).trans
                (hlowK (st.stk.back!.pc, eT) List.mem_cons_self)
            obtain ⟨stM₁, fuelM₁, N₁, hf1, hgo1, hstk1, how1, hAT1, hP1, hsame1,
              hfitN1, hlow1, hpark1, hext1, hmono1, hq1⟩ :=
              ih f (by omega) stA st' ET (KT' ++ AT) E (KL' ++ AL)
                (P ++ tagAtt attempt QE) hgoA hstkA harm.owned harm.head hSA hPA
                (fun x hx => harm.fits x (List.mem_append_left _ hx)) hlowE
                hseenA
            have hsetP : Settled re s mo start attempt pos
                ((P ++ tagAtt attempt QE) ++ tagAtt attempt N₁)
                st.stk.back!.pc := by
              refine ⟨P, tagAtt attempt (QE ++ N₁), [], eT, attempt,
                by simp [tagAtt_append], Nat.le_refl _, hfitE.1, hfitE.2, ?_⟩
              exact SameAfter.symm
                ((harm.same P).trans (SameAfter.comp SameAfter.refl hsame1))
            obtain ⟨hSK, hSA2⟩ := ThList.split (ThList.length_eq hrest) hAT1
            obtain ⟨stM, fuelM, N₂, hf2, hgoM, hstkM, howM, hATM, hPM, hsame2,
              hfitN2, hlow2, hpark2, hext2, hmono2, hq2⟩ :=
              ih fuelM₁ (by omega) stM₁ st' KT' AT KL' AL
                ((P ++ tagAtt attempt QE) ++ tagAtt attempt N₁)
                hgo1 hstk1 how1 hSK hSA2
                (by rw [untag_append, untag_tagAtt]; exact hP1)
                (fun x hx => hfitK x (List.mem_cons_of_mem _ hx))
                (fun x hx => hlowK x (List.mem_cons_of_mem _ hx))
                (fun q hq => by
                  rcases hq1 q hq with h | ⟨h1, _⟩
                  · exact Or.inl h
                  · rcases harm.seenNew q h1 with rfl | h1'
                    · exact Or.inl hsetP
                    · rcases hseen q h1' with hS | hS
                      · exact Or.inl
                          ((hS.mono (tagAtt attempt QE)).mono
                            (tagAtt attempt N₁))
                      · exact Or.inr
                          (fun x hx => hS x (List.mem_cons_of_mem _ hx)))
            refine ⟨stM, fuelM, QE ++ N₁ ++ N₂, by omega, hgoM, hstkM, howM,
              hATM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [untag_append, untag_tagAtt] using hPM
            · refine SameAfter.comp
                ((harm.same P).trans (SameAfter.comp SameAfter.refl hsame1)) ?_
              simpa [tagAtt_append] using hsame2
            · intro x hx
              rcases List.mem_append.mp hx with hx' | hx'
              · rcases List.mem_append.mp hx' with hx'' | hx''
                · exact harm.fits x (List.mem_append_right _ hx'')
                · exact hfitN1 x hx''
              · exact hfitN2 x hx'
            · intro x hx
              rcases List.mem_append.mp hx with hx' | hx'
              · rcases List.mem_append.mp hx' with hx'' | hx''
                · exact (harm.tag x (List.mem_append_right _ hx'')).trans
                    (hlowK (st.stk.back!.pc, eT) List.mem_cons_self)
                · exact hlow1 x hx''
              · exact hlow2 x hx'
            · intro x hx
              rcases List.mem_append.mp hx with hx' | hx'
              · rcases List.mem_append.mp hx' with hx'' | hx''
                · exact harm.parks x hx''
                · exact hpark1 x hx''
              · exact hpark2 x hx'
            · intro k hk
              rw [hext2 k hk, hext1 k hk]
              exact harm.keep k (List.mem_append_right _ hk)
            · exact fun q hq => hmono2 q (hmono1 q (harm.seenMono q hq))
            · intro q hq
              rcases hq2 q hq with h | ⟨h1, _⟩
              · exact Or.inl (by simpa [tagAtt_append] using h)
              · rcases hq1 q h1 with h2 | ⟨h2, _⟩
                · exact Or.inl (by
                    simpa [tagAtt_append] using h2.mono (tagAtt attempt N₂))
                · rcases harm.seenNew q h2 with rfl | h2'
                  · exact Or.inl (by
                      simpa [tagAtt_append] using
                        hsetP.mono (tagAtt attempt N₂))
                  · rcases hseen q h2' with hS | hS
                    · exact Or.inl (by
                        simpa [tagAtt_append] using
                          (((hS.mono (tagAtt attempt QE)).mono
                            (tagAtt attempt N₁)).mono (tagAtt attempt N₂)))
                    · exact Or.inr ⟨h2', hS⟩

/-- One whole closure build. The seed is the only thing on the worklist,
so what the build parks answers exactly what a thread at the seed's pc
would answer, read behind the list already parked. The premise about the
visited set is the one a caller inside a position step has to carry: a pc
the build will find marked is one an earlier build in the same position
already settled, or one out of the seed's reach — and the build hands the
same premise back, with its own output settled into the parked list, which
is what lets the next build in the same position take over.

Three things travel with what it parks: the entries fit, they still carry
in slot zero whatever the seed carried there, and each of them stands at
an opcode the list step knows how to dispatch. -/
theorem pikeAdd_refine {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {intoNext : Bool} {start attempt pos pc0 h0 : Nat} {tag : UInt32}
    {ext : List Nat} {st st' : PikeSt} {t0 : Spec.Thread} {P : List MEntry}
    (he : Eligible re) (hs : s.size ≤ ceiling) (hatt : attempt ≤ pos)
    (hok : pikeAdd re s mo lim intoNext pos pc0 h0 st = .ok st')
    (hstk : st.stk.size = 0)
    (how : Owned re.novec st.rc st.free st.pool
      (h0 :: buildLive intoNext st ext))
    (hat : ThAt re st.pool pos ⟨pc0, h0⟩ (pc0, t0))
    (hpos : t0.pos = pos) (hfit : Fit re s pc0 pos t0.regs)
    (hlow : (t0.regs)[0]! = tag)
    (hP : ThList re st.pool pos (parkList intoNext st).toList (untag P))
    (hseen : ∀ q : Nat, st.seen[q]! = true →
      Settled re s mo start attempt pos P q ∨
        ¬ EpsReach re.code re.reps pc0 q) :
    ∃ N : List Entry,
      Owned re.novec st'.rc st'.free st'.pool (buildLive intoNext st' ext) ∧
      st'.stk.size = 0 ∧
      ThList re st'.pool pos (parkList intoNext st').toList (untag P ++ N) ∧
      SameAfter re s mo start attempt P [(pc0, t0)] N ∧
      (∀ e ∈ N, e.2.pos = pos ∧ Fit re s e.1 pos e.2.regs) ∧
      (∀ e ∈ N, (e.2.regs)[0]! = tag) ∧
      (∀ e ∈ N, Parked re e.1) ∧
      (∀ k ∈ ext, blockAt st'.pool re.novec k = blockAt st.pool re.novec k) ∧
      (∀ q : Nat, st'.seen[q]! = true →
        Settled re s mo start attempt pos (P ++ tagAtt attempt N) q ∨
          (st.seen[q]! = true ∧ ¬ EpsReach re.code re.reps pc0 q)) := by
  rw [pikeAdd] at hok
  split at hok
  · exact absurd_error hok
  · rename_i stD hdef
    obtain ⟨hkD, heD⟩ := pikeDefer_ok hdef
    obtain ⟨hclD, hnlD⟩ := pikeDefer_lists hdef
    have hplD : stD.pool = st.pool := pikeDefer_pool hdef
    obtain ⟨stM, fuelM, N, -, hgoM, hstkM, howM, -, hPM, hsameM, hfitN, hlowN,
      hparkN, hextM, -, hqM⟩ :=
      pikeAdd_go_refine (start := start) (attempt := attempt) (tag := tag)
        he hs hatt
        (2 * re.code.size + 2) stD st' [⟨pc0, h0⟩] [] [(pc0, t0)] [] P hok
        (by rw [hkD, stkOf_push, stkOf_nil hstk]; simp) (defer_owned hdef how)
        (List.Forall₂.cons (by rw [hplD]; exact hat) List.Forall₂.nil)
        List.Forall₂.nil
        (by rw [parkList_eq hclD hnlD, hplD]; exact hP)
        (by
          intro e he
          simp only [List.mem_singleton] at he
          subst he
          exact ⟨hpos, hfit⟩)
        (by
          intro e he
          simp only [List.mem_singleton] at he
          subst he
          exact hlow)
        (by
          intro q hq
          rw [heD] at hq
          rcases hseen q hq with h | h
          · exact Or.inl h
          · refine Or.inr (fun e he => ?_)
            simp only [List.mem_singleton] at he
            subst he
            exact h)
    have hsz0 : stM.stk.size = 0 := by
      have hnil : stM.stk.toList = [] := by
        have hrev := hstkM
        rw [stkOf] at hrev
        simpa using hrev
      rw [← Array.length_toList, hnil]
      rfl
    have hfin : stM = st' := by
      cases fuelM with
      | zero =>
          rw [pikeAdd.go] at hgoM
          exact absurd hgoM (by simp)
      | succ g =>
          simp only [pikeAdd.go, hsz0] at hgoM
          simpa using hgoM
    subst hfin
    refine ⟨N, howM, hsz0, hPM, hsameM, hfitN, hlowN, hparkN,
      fun k hk => by rw [hextM k hk, hplD], fun q hq => ?_⟩
    rcases hqM q hq with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by rwa [heD] at h1,
        fun hr => h2 (pc0, t0) List.mem_cons_self hr⟩

/-! ## The one cell the mirror never reads

A thread's block carries its attempt in slot zero, planted by `pike_seed`,
and the reading of a thread against the mirror asks for agreement over the
whole ovector — so the mirror's register file carries the attempt there
too, where the specification's blank file carries nothing. The two differ
in that one cell and nowhere else, and no search can tell them apart: the
mirror reads slot zero at no instruction and writes it only at the accept,
where it writes the attempt. That is what lets the list step hand a
completed search to `runs_attempt_refines`, which wants the blank file. -/

/-- Two register files that differ at most in slot zero. -/
def OffTag (u v : Spec.Regs) : Prop :=
  u.size = v.size ∧ ∀ i, i ≠ 0 → u[i]! = v[i]!

theorem OffTag.refl {u : Spec.Regs} : OffTag u u := ⟨rfl, fun _ _ => rfl⟩

/-- The same write on both sides leaves them apart in slot zero alone. -/
theorem OffTag.set {u v : Spec.Regs} (h : OffTag u v) (i : Nat) (x : UInt32) :
    OffTag (u.set! i x) (v.set! i x) := by
  refine ⟨by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
    h.1], fun j hj => ?_⟩
  by_cases hij : j = i
  · subst hij
    by_cases hb : j < u.size
    · rw [getBang_set_self u hb, getBang_set_self v (h.1 ▸ hb)]
    · rw [Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds,
        getElem!_neg _ j (by simpa using hb),
        getElem!_neg _ j (by
          simp only [Array.size_setIfInBounds, ← h.1]
          simpa using hb)]
  · rw [getBang_set_other u i hij, getBang_set_other v i hij]
    exact h.2 j hj

/-- And once slot zero itself is written on both sides they are the same
file, which is what the accept does. -/
theorem OffTag.setZero {u v : Spec.Regs} (h : OffTag u v) (x : UInt32) :
    u.set! 0 x = v.set! 0 x := by
  apply Array.ext
  · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, h.1]
  · intro j h1 h2
    have hjs : j < u.size := by
      simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using h1
    rw [← getElem!_pos _ j h1, ← getElem!_pos _ j h2]
    by_cases hj : j = 0
    · subst hj
      rw [getBang_set_self u hjs, getBang_set_self v (h.1 ▸ hjs)]
    · rw [getBang_set_other u 0 hj, getBang_set_other v 0 hj]
      exact h.2 j hj

/-- Two moves that differ no more than the files they carry. -/
def EffOffTag : Eff → Eff → Prop
  | .goto a b w, .goto a' b' w' => a = a' ∧ b = b' ∧ OffTag w w'
  | .fork a b, .fork a' b' => a = a' ∧ b = b'
  | .fail, .fail => True
  | .give t, .give t' => t = t'
  | .stuck, .stuck => True
  | _, _ => False

/-- One move, on two files apart in slot zero: the same move. The only
cells the mirror reads out of a file are a repetition's counters, which
live above the ovector, and the only cell it writes low is the accept's
own record of the attempt. -/
theorem eff_offTag {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {u v : Spec.Regs} (hnov : 0 < re.novec)
    (h : OffTag u v) :
    EffOffTag (eff re s mo start attempt pc pos u)
      (eff re s mo start attempt pc pos v) := by
  cases hop : (re.code[pc]! : Inst).op <;> simp only [eff, hop]
  case save => exact ⟨rfl, rfl, h.set _ _⟩
  case repZero => exact ⟨rfl, rfl, h.set _ _⟩
  case repEnter => exact ⟨rfl, rfl, h.set _ _⟩
  case repLoop =>
      rw [h.2 (re.novec + (re.code[pc]! : Inst).arg * 2) (by omega)]
      repeat' split
      all_goals first
        | exact ⟨rfl, rfl, h⟩
        | exact ⟨rfl, rfl⟩
  case repNext =>
      rw [h.2 (re.novec + (re.code[pc]! : Inst).arg * 2) (by omega),
        h.2 (re.novec + (re.code[pc]! : Inst).arg * 2 + 1) (by omega)]
      split
      · exact ⟨rfl, rfl, h.set _ _⟩
      · exact ⟨rfl, rfl, h.set _ _⟩
  case accept =>
      split
      · exact True.intro
      · rw [h.setZero attempt.toUInt32]
        exact rfl
  all_goals
    (repeat' split)
    all_goals first
      | exact ⟨rfl, rfl, h⟩
      | exact ⟨rfl, rfl⟩
      | exact True.intro

/-- The four shapes of that agreement, read off one side. -/
theorem eff_offTag_goto {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos a b : Nat} {u v w : Spec.Regs}
    (hnov : 0 < re.novec) (h : OffTag u v)
    (heff : eff re s mo start attempt pc pos u = .goto a b w) :
    ∃ w', eff re s mo start attempt pc pos v = .goto a b w' ∧ OffTag w w' := by
  have hrel := eff_offTag (s := s) (mo := mo) (start := start)
    (attempt := attempt) (pc := pc) (pos := pos) (v := v) hnov h
  rw [heff] at hrel
  revert hrel
  cases eff re s mo start attempt pc pos v
  case goto a' b' w' =>
      rintro ⟨rfl, rfl, hw⟩
      exact ⟨w', rfl, hw⟩
  all_goals exact fun hrel => False.elim hrel

theorem eff_offTag_fork {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos a b : Nat} {u v : Spec.Regs}
    (hnov : 0 < re.novec) (h : OffTag u v)
    (heff : eff re s mo start attempt pc pos u = .fork a b) :
    eff re s mo start attempt pc pos v = .fork a b := by
  have hrel := eff_offTag (s := s) (mo := mo) (start := start)
    (attempt := attempt) (pc := pc) (pos := pos) (v := v) hnov h
  rw [heff] at hrel
  revert hrel
  cases eff re s mo start attempt pc pos v
  case fork a' b' =>
      rintro ⟨rfl, rfl⟩
      rfl
  all_goals exact fun hrel => False.elim hrel

theorem eff_offTag_fail {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {u v : Spec.Regs}
    (hnov : 0 < re.novec) (h : OffTag u v)
    (heff : eff re s mo start attempt pc pos u = .fail) :
    eff re s mo start attempt pc pos v = .fail := by
  have hrel := eff_offTag (s := s) (mo := mo) (start := start)
    (attempt := attempt) (pc := pc) (pos := pos) (v := v) hnov h
  rw [heff] at hrel
  revert hrel
  cases eff re s mo start attempt pc pos v
  case fail => exact fun _ => rfl
  all_goals exact fun hrel => False.elim hrel

theorem eff_offTag_give {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {u v : Spec.Regs} {t : Spec.Thread}
    (hnov : 0 < re.novec) (h : OffTag u v)
    (heff : eff re s mo start attempt pc pos u = .give t) :
    eff re s mo start attempt pc pos v = .give t := by
  have hrel := eff_offTag (s := s) (mo := mo) (start := start)
    (attempt := attempt) (pc := pc) (pos := pos) (v := v) hnov h
  rw [heff] at hrel
  revert hrel
  cases eff re s mo start attempt pc pos v
  case give t' => exact fun hrel => by rw [hrel]
  all_goals exact fun hrel => False.elim hrel

theorem eff_offTag_stuck {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {u v : Spec.Regs}
    (hnov : 0 < re.novec) (h : OffTag u v)
    (heff : eff re s mo start attempt pc pos u = .stuck) :
    eff re s mo start attempt pc pos v = .stuck := by
  have hrel := eff_offTag (s := s) (mo := mo) (start := start)
    (attempt := attempt) (pc := pc) (pos := pos) (v := v) hnov h
  rw [heff] at hrel
  revert hrel
  cases eff re s mo start attempt pc pos v
  case stuck => exact fun _ => rfl
  all_goals exact fun hrel => False.elim hrel

/-- Two pending stacks apart in slot zero, entry for entry. -/
def StkOffTag : List Entry → List Entry → Prop :=
  List.Forall₂ fun e f =>
    e.1 = f.1 ∧ e.2.pos = f.2.pos ∧ OffTag e.2.regs f.2.regs

/-- A whole search cannot tell the two files apart, answer included: the
accept writes the attempt into slot zero before it delivers, so the very
cell they differ in is the one the answer overwrites. -/
theorem run_offTag {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} (hnov : 0 < re.novec) :
    ∀ (fuel pc pos : Nat) (u v : Spec.Regs) (stk stk' : List Entry),
      OffTag u v → StkOffTag stk stk' →
      run re s mo start attempt fuel pc pos u stk =
        run re s mo start attempt fuel pc pos v stk' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _; simp only [run]
  | succ fuel ih =>
      intro pc pos u v stk stk' huv hstk
      rw [run, run]
      cases heffU : eff re s mo start attempt pc pos u
      case goto a b w =>
          obtain ⟨w', heffV, hw⟩ := eff_offTag_goto hnov huv heffU
          rw [heffV]
          exact ih a b w w' stk stk' hw hstk
      case fork a b =>
          rw [eff_offTag_fork hnov huv heffU]
          exact ih a pos u v ((b, ⟨pos, u⟩) :: stk) ((b, ⟨pos, v⟩) :: stk') huv
            (List.Forall₂.cons ⟨rfl, rfl, huv⟩ hstk)
      case fail =>
          rw [eff_offTag_fail hnov huv heffU]
          cases hstk with
          | nil => rfl
          | cons hxy hrest =>
              rename_i e f estk fstk
              obtain ⟨q, t⟩ := e
              obtain ⟨q', t'⟩ := f
              obtain ⟨hq, hpp, hrr⟩ := hxy
              simp only [] at hq hpp
              subst hq
              rw [dispatch, dispatch, ← hpp]
              exact ih q t.pos t.regs t'.regs estk fstk hrr hrest
      case give t => rw [eff_offTag_give hnov huv heffU]
      case stuck => rw [eff_offTag_stuck hnov huv heffU]

/-- The same at the judgment level, on an empty pending stack. -/
theorem runs_offTag {re : Re} {s : ByteArray} {mo : MOpts}
    {start attempt pc pos : Nat} {u v : Spec.Regs} {r : Out}
    (hnov : 0 < re.novec) (huv : OffTag u v) :
    Runs re s mo start attempt pc pos u [] r ↔
      Runs re s mo start attempt pc pos v [] r :=
  exists_congr fun fuel => by
    rw [run_offTag hnov fuel pc pos u v [] [] huv List.Forall₂.nil]

/-! ## One position, stepped

`step_threads` walks the built list in priority order, and every entry it
walks is one more move of the mirror: a consuming leaf whose byte matches
opens a closure into the next list at `pos + 1`, one whose byte does not
simply goes, and an accepting thread delivers and kills everything below
it. That last arm is where the merge earns its shape — a recorded match is
a verdict standing under whatever is still above it, and only a thread
above it can overwrite one.

The attempt an entry belongs to is not bookkeeping the proof invents: it
is slot zero of the thread's own block, which `pike_seed` plants and no
compiled save can reach. `Live` says that of one entry and `MList` of a
whole list, with the attempts ordered earliest first — which is what lets
a build drop a pc an earlier attempt already expanded. -/

/-- What one entry of a built list carries: an attempt no later than the
position the list is for, still on record in slot zero of its own file; a
configuration that fits; and an opcode the step knows how to dispatch. -/
def Live (re : Re) (s : ByteArray) (pos : Nat) (x : MEntry) : Prop :=
  x.1 ≤ pos ∧ x.2.2.pos = pos ∧ Fit re s x.2.1 pos x.2.2.regs ∧
    (x.2.2.regs)[0]! = (x.1 : Nat).toUInt32 ∧ Parked re x.2.1

/-- A whole thread list read as a merged pending list: the handles decode
to the entries, every entry is live, and the attempts run earliest
first. -/
def MList (re : Re) (s : ByteArray) (pool : Array UInt32) (pos : Nat)
    (ths : List Th) (L : List MEntry) : Prop :=
  ThList re pool pos ths (untag L) ∧ (∀ x ∈ L, Live re s pos x) ∧
    L.Pairwise fun x y => x.1 ≤ y.1

/-- What the machine has on record, read as the mirror's verdict: nothing
yet, or the accepted thread whose block the match handle names. -/
def OnRecord (re : Re) (pool : Array UInt32) (mh : Nat) (matched : Bool)
    (back : Out) : Prop :=
  (matched = false ∧ mh = none32 ∧ back = .nomatch) ∨
    (matched = true ∧ mh ≠ none32 ∧ ∃ t : Spec.Thread, back = .found t ∧
      Agree re.novec (blockAt pool re.novec mh) t.regs)

/-- A pc settled for one attempt is settled for any later one: the stretch
that settled it was opened no later still. -/
theorem Settled.attMono {re : Re} {s : ByteArray} {mo : MOpts}
    {start a a' pos : Nat} {P : List MEntry} {q : Nat}
    (h : Settled re s mo start a pos P q) (hle : a ≤ a') :
    Settled re s mo start a' pos P q := by
  obtain ⟨A, Sq, B, t₀, a₀, hP, hle0, hp, hfit, hsame⟩ := h
  exact ⟨A, Sq, B, t₀, a₀, hP, by omega, hp, hfit, hsame⟩

/-- An entry of a merge that delivers is the merge's answer, and it makes
the record below it and everything after it beside the point. -/
theorem mergeAfter_give {re : Re} {s : ByteArray} {mo : MOpts}
    {start a pc : Nat} {t tx : Spec.Thread} {rest : List MEntry}
    {back r : Out}
    (h : Runs re s mo start a pc t.pos t.regs [] (.found tx)) :
    MergeAfter re s mo start ((a, (pc, t)) :: rest) back r ↔ r = .found tx := by
  show (_ ∨ _) ↔ _
  constructor
  · rintro (⟨w, rfl, hw⟩ | ⟨hn, _⟩)
    · rw [runs_det hw h]
    · exact absurd (runs_det hn h) (by simp)
  · rintro rfl
    exact Or.inl ⟨tx, rfl, h⟩

/-- Dropping the threads a recorded match outranks touches nothing the
reading looks at. -/
private theorem dropRest_frame {lim : Limits} :
    ∀ (rest : List Th) (st st' : PikeSt), dropRest lim rest st = .ok st' →
      st'.pool = st.pool ∧ st'.nlist = st.nlist ∧ st'.stk = st.stk ∧
        st'.seen = st.seen := by
  intro rest
  induction rest with
  | nil =>
      intro st st' h
      rw [dropRest] at h
      injection h with h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons th rest ih =>
      intro st st' h
      rw [dropRest] at h
      split at h
      · exact absurd_error h
      · rename_i stD hd
        obtain ⟨o1, o2, o3, o4⟩ := ih stD st' h
        obtain ⟨hk, he⟩ := pikeDrop_ok hd
        obtain ⟨_, hnl⟩ := pikeDrop_lists hd
        exact ⟨o1.trans (pikeDrop_pool hd), o2.trans hnl, o3.trans hk,
          o4.trans he⟩

/-- Below the wrap the machine's 32-bit spelling of an offset tells two
offsets apart. -/
private theorem toUInt32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : (a : Nat).toUInt32 = (b : Nat).toUInt32) : a = b := by
  have hn := congrArg UInt32.toNat h
  rwa [toNat_ofNat32 ha, toNat_ofNat32 hb] at hn

private theorem beq_ofNat32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((a : Nat).toUInt32 == (b : Nat).toUInt32) = (a == b) := by
  by_cases hab : a = b
  · subst hab
    simp
  · rw [beq_eq_false_iff_ne.mpr (fun hq => hab (toUInt32_inj ha hb hq)),
      beq_eq_false_iff_ne.mpr hab]

private theorem beq_nat_comm (a b : Nat) : (a == b) = (b == a) := by
  by_cases hab : a = b
  · subst hab
    rfl
  · rw [beq_eq_false_iff_ne.mpr hab, beq_eq_false_iff_ne.mpr (Ne.symm hab)]

/-- The attempt a thread carries, read off the pool: slot zero of its own
block, which is where `pike_seed` planted it and where the reading against
the mirror keeps it. -/
theorem attempt_of_pool {re : Re} {pool : Array UInt32} {pos : Nat} {th : Th}
    {e : Entry} (hnov : 0 < re.novec) (hat : ThAt re pool pos th e)
    (hlow : (e.2.regs)[0]! = (a : Nat).toUInt32) :
    pool[th.h * re.novec]! = (a : Nat).toUInt32 := by
  have hag := hat.2.2.2.2 0 hnov
  rw [blockAt_get hnov] at hag
  simpa using hag.trans hlow

/-- The list a build writes into, named. -/
private theorem parkList_true (st : PikeSt) : parkList true st = st.nlist := rfl

/-- Every entry of one attempt's stretch is that attempt's. -/
private theorem fst_of_tagAtt {a : Nat} {L : List Entry} {y : MEntry}
    (hy : y ∈ tagAtt a L) : y.1 = a := by
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp hy
  rfl

private theorem pairwise_tagAtt (a : Nat) (L : List Entry) :
    (tagAtt a L).Pairwise fun x y : MEntry => x.1 ≤ y.1 := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons e L ih =>
      exact List.Pairwise.cons
        (fun y hy => Nat.le_of_eq (fst_of_tagAtt hy).symm) ih

/-- A file whose slot zero already holds the tag agrees with the same file
written there. -/
theorem agree_set_tag {novec : Nat} {u v : Spec.Regs} (hnov : 0 < novec)
    (h : Agree novec u v) {x : UInt32} (hx : v[0]! = x) :
    Agree novec u (v.set! 0 x) := by
  obtain ⟨hu, hv, hag⟩ := h
  refine ⟨hu, by simp only [Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds]; exact hv, fun i hi => ?_⟩
  by_cases h0 : i = 0
  · subst h0
    rw [getBang_set_self v (by omega)]
    exact (hag 0 hnov).trans hx
  · rw [getBang_set_other v 0 h0]
    exact hag i hi

set_option maxHeartbeats 2000000 in
/-- One position's list, stepped against the mirror. The list is a merge
of the attempts still running, and stepping it rewrites that merge: a
consuming leaf whose byte matches is replaced by the closure it opens into
the next list, one whose byte does not is dropped, and an accepting thread
puts its own answer on record and takes everything below it with it —
which is what `MergeAfter`'s record is for, since the threads still above
it can overwrite one.

The visited set travels with the list rather than with a build: it is
cleared once per position and spans every build that fills one list, so
what a build finds marked is what an earlier build in the same list
already settled. The attempts run earliest first, which is what makes that
settlement usable across them. -/
theorem stepThreads_refine {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start pos : Nat} (he : Eligible re) (hs : s.size ≤ ceiling)
    (hstart : start ≤ s.size) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (matched : Bool)
      (out : StepOut) (L P : List MEntry) (back : Out) (aPrev : Nat),
      stepThreads re s mo lim start pos threads st mh (!matched) matched
        = .ok out →
      st.stk.size = 0 →
      Owned re.novec st.rc st.free st.pool
        (buildLive true st (threads.map Th.h ++ mhList mh)) →
      MList re s st.pool pos threads L →
      MList re s st.pool (pos + 1) st.nlist.toList P →
      OnRecord re st.pool mh matched back →
      aPrev ≤ pos → (∀ x ∈ L, aPrev ≤ x.1) → (∀ x ∈ P, x.1 ≤ aPrev) →
      (∀ q : Nat, st.seen[q]! = true →
        Settled re s mo start aPrev (pos + 1) P q) →
      ∃ (N : List MEntry) (back' : Out),
        MList re s out.st.pool (pos + 1) out.st.nlist.toList (P ++ N) ∧
        OnRecord re out.st.pool out.mh out.matched back' ∧
        (∀ r, MergeAfter re s mo start (P ++ L) back r ↔
          MergeAfter re s mo start (P ++ N) back' r) ∧
        out.seeding = !out.matched ∧
        (matched = true → out.matched = true) ∧
        (∀ x ∈ N, x.1 ≤ pos) ∧
        (∀ q : Nat, out.st.seen[q]! = true →
          Settled re s mo start pos (pos + 1) (P ++ N) q) := by
  have hnov : 0 < re.novec := by have := he.novec; omega
  have hslot1 : 1 < re.novec := by have := he.novec; omega
  have hceil : s.size < 2 ^ 32 := by simp only [ceiling] at hs; omega
  intro threads
  induction threads with
  | nil =>
      intro st mh matched out L P back aPrev hgo _ _ hL hP hrec haP _ _ hseen
      rw [stepThreads] at hgo
      injection hgo with hgo
      subst hgo
      have hLnil : L = [] := by
        have hlen := ThList.length_eq hL.1
        simp only [List.length_nil, untag, List.length_map] at hlen
        exact List.eq_nil_of_length_eq_zero hlen.symm
      subst hLnil
      exact ⟨[], back, by simpa using hP, hrec, fun r => by simp,
        rfl, fun h => h, by simp, fun q hq => by
          simpa using (hseen q hq).attMono haP⟩
  | cons th rest ih =>
      intro st mh matched out L P back aPrev hgo hstk how hL hP hrec haP hLge
        hPle hseen
      obtain ⟨hLth, hLive, hLsort⟩ := hL
      cases L with
      | nil =>
          exfalso
          have hlen := ThList.length_eq hLth
          simp [untag] at hlen
      | cons x Lrest =>
          obtain ⟨a, pc0, t⟩ := x
          obtain ⟨tp, tr⟩ := t
          unfold ThList at hLth
          cases hLth with
          | cons hat hrestL =>
          have hpc0 : pc0 = th.pc := hat.1
          subst hpc0
          have htp : pos = tp := hat.2.1.symm
          subst htp
          obtain ⟨hale, -, hfitx, hlowx, hparkx⟩ :=
            hLive (a, (th.pc, ⟨pos, tr⟩)) List.mem_cons_self
          have hposle : pos ≤ s.size := hfitx.1
          have hLtail : ∀ y ∈ Lrest, a ≤ y.1 :=
            (List.pairwise_cons.mp hLsort).1
          have hmid : Owned re.novec st.rc st.free st.pool
              (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)) := by
            refine how.perm ?_
            have hcons : (th :: rest).map Th.h ++ mhList mh =
                th.h :: (rest.map Th.h ++ mhList mh) := by simp
            rw [hcons, buildLive, buildLive]
            exact List.perm_middle.symm
          -- The thread dies: the mirror fails where the machine drops.
          have harmDrop : ∀ (stA stB : PikeSt),
              (∀ A : List MEntry,
                MSame re s mo start A [(a, (th.pc, (⟨pos, tr⟩ : Spec.Thread)))]
                  []) →
              pikeDrop stA th.h lim = .ok stB →
              stepThreads re s mo lim start pos rest stB mh (!matched) matched
                = .ok out →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              stA.seen = st.seen → stA.stk = st.stk → stA.nlist = st.nlist →
              ∃ (N : List MEntry) (back' : Out),
                MList re s out.st.pool (pos + 1) out.st.nlist.toList (P ++ N) ∧
                OnRecord re out.st.pool out.mh out.matched back' ∧
                (∀ r, MergeAfter re s mo start
                    (P ++ (a, (th.pc, (⟨pos, tr⟩ : Spec.Thread))) :: Lrest)
                    back r ↔
                  MergeAfter re s mo start (P ++ N) back' r) ∧
                out.seeding = !out.matched ∧
                (matched = true → out.matched = true) ∧
                (∀ x ∈ N, x.1 ≤ pos) ∧
                (∀ q : Nat, out.st.seen[q]! = true →
                  Settled re s mo start pos (pos + 1) (P ++ N) q) := by
            intro stA stB hsame hdr hgo' hrcA hfreeA hpoolA hseenA hstkA hnlA
            have howA : Owned re.novec stA.rc stA.free stA.pool
                (th.h :: buildLive true stA
                  (rest.map Th.h ++ mhList mh)) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, parkList_true, hstkA, hnlA]
              exact hmid
            obtain ⟨hkD, heD⟩ := pikeDrop_ok hdr
            obtain ⟨-, hnlD⟩ := pikeDrop_lists hdr
            have hplB : stB.pool = st.pool := by
              rw [pikeDrop_pool hdr, hpoolA]
            have hnlB : stB.nlist = st.nlist := by rw [hnlD, hnlA]
            obtain ⟨N, back', hMN, hrecN, hansN, hsdN, hmatN, hleN,
              hseenN⟩ :=
              ih stB mh matched out Lrest P back aPrev hgo'
                (by rw [hkD, hstkA]; exact hstk) (drop_owned hdr howA)
                (by
                  rw [hplB]
                  exact ⟨hrestL, fun y hy => hLive y (List.mem_cons_of_mem _ hy),
                    (List.pairwise_cons.mp hLsort).2⟩)
                (by rw [hplB, hnlB]; exact hP)
                (by rw [hplB]; exact hrec) haP
                (fun y hy => hLge y (List.mem_cons_of_mem _ hy)) hPle
                (by rw [heD, hseenA]; exact hseen)
            refine ⟨N, back', hMN, hrecN, fun r => ?_, hsdN, hmatN, hleN,
              hseenN⟩
            have h1 := hsame P Lrest back r
            simp only [List.append_assoc, List.singleton_append,
              List.nil_append] at h1
            exact h1.trans (hansN r)
          -- The thread lives on: the closure it opens is the mirror's move.
          have harmAdd : ∀ (stA stB : PikeSt),
              eff re s mo start a th.pc pos tr = .goto (th.pc + 1) (pos + 1) tr →
              pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h stA = .ok stB →
              stepThreads re s mo lim start pos rest stB mh (!matched) matched
                = .ok out →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              stA.seen = st.seen → stA.stk = st.stk → stA.nlist = st.nlist →
              ∃ (N : List MEntry) (back' : Out),
                MList re s out.st.pool (pos + 1) out.st.nlist.toList (P ++ N) ∧
                OnRecord re out.st.pool out.mh out.matched back' ∧
                (∀ r, MergeAfter re s mo start
                    (P ++ (a, (th.pc, (⟨pos, tr⟩ : Spec.Thread))) :: Lrest)
                    back r ↔
                  MergeAfter re s mo start (P ++ N) back' r) ∧
                out.seeding = !out.matched ∧
                (matched = true → out.matched = true) ∧
                (∀ x ∈ N, x.1 ≤ pos) ∧
                (∀ q : Nat, out.st.seen[q]! = true →
                  Settled re s mo start pos (pos + 1) (P ++ N) q) := by
            intro stA stB heff hadd hgo' hrcA hfreeA hpoolA hseenA hstkA hnlA
            have howA : Owned re.novec stA.rc stA.free stA.pool
                (th.h :: buildLive true stA
                  (rest.map Th.h ++ mhList mh)) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, parkList_true, hstkA, hnlA]
              exact hmid
            obtain ⟨Nx, howB, hstkB, hPB, hsameB, hfitB, htagB, hparkB, hextB,
              hseenB⟩ :=
              pikeAdd_refine (start := start) (attempt := a)
                (tag := (a : Nat).toUInt32) (P := P)
                (ext := rest.map Th.h ++ mhList mh) (t0 := ⟨pos + 1, tr⟩)
                he hs (by omega) hadd (by rw [hstkA]; exact hstk) howA
                (by rw [hpoolA]; exact ⟨rfl, rfl, hat.2.2⟩) rfl
                (eff_fit_goto he.ok he.cells he.rows he.mid hs hfitx heff)
                hlowx
                (by rw [parkList_true, hnlA, hpoolA]; exact hP.1)
                (fun q hq => Or.inl
                  ((hseen q (by rw [← hseenA]; exact hq)).attMono
                    (hLge (a, (th.pc, ⟨pos, tr⟩)) List.mem_cons_self)))
            have hkeep : ∀ k ∈ rest.map Th.h ++ mhList mh,
                blockAt stB.pool re.novec k = blockAt st.pool re.novec k :=
              fun k hk => (hextB k hk).trans (by rw [hpoolA])
            have hliveNx : ∀ y ∈ tagAtt a Nx, Live re s (pos + 1) y := by
              intro y hy
              obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
              exact ⟨by omega, (hfitB f hf).1, (hfitB f hf).2, htagB f hf,
                hparkB f hf⟩
            obtain ⟨N, back', hMN, hrecN, hansN, hsdN, hmatN, hleN,
              hseenN⟩ :=
              ih stB mh matched out Lrest (P ++ tagAtt a Nx) back a hgo' hstkB
                howB
                ⟨ThList.ofPool hrestL (fun y hy =>
                    hkeep y.h (List.mem_append_left _ (List.mem_map_of_mem hy))),
                  fun y hy => hLive y (List.mem_cons_of_mem _ hy),
                  (List.pairwise_cons.mp hLsort).2⟩
                ⟨by
                    rw [untag_append, untag_tagAtt, ← parkList_true]
                    exact hPB,
                  by
                    intro y hy
                    rcases List.mem_append.mp hy with hy' | hy'
                    · exact hP.2.1 y hy'
                    · exact hliveNx y hy',
                  by
                    refine List.pairwise_append.mpr
                      ⟨hP.2.2, pairwise_tagAtt a Nx, fun y hy z hz => ?_⟩
                    rw [fst_of_tagAtt hz]
                    exact Nat.le_trans (hPle y hy)
                      (hLge (a, (th.pc, ⟨pos, tr⟩)) List.mem_cons_self)⟩
                (by
                  rcases hrec with ⟨h1, h2, h3⟩ | ⟨h1, h2, w, h3, h4⟩
                  · exact Or.inl ⟨h1, h2, h3⟩
                  · refine Or.inr ⟨h1, h2, w, h3, ?_⟩
                    rw [hkeep mh (List.mem_append_right _
                      (by rw [mhList, if_neg h2]; simp))]
                    exact h4)
                hale hLtail
                (by
                  intro y hy
                  rcases List.mem_append.mp hy with hy' | hy'
                  · exact Nat.le_trans (hPle y hy')
                      (hLge (a, (th.pc, ⟨pos, tr⟩)) List.mem_cons_self)
                  · exact Nat.le_of_eq (fst_of_tagAtt hy'))
                (fun q hq => by
                  rcases hseenB q hq with h | ⟨h1, -⟩
                  · exact h
                  · exact ((hseen q (by rw [← hseenA]; exact h1)).attMono
                      (hLge (a, (th.pc, ⟨pos, tr⟩)) List.mem_cons_self)).mono
                      (tagAtt a Nx))
            have hkey : MSame re s mo start P
                [(a, (th.pc, (⟨pos, tr⟩ : Spec.Thread)))] (tagAtt a Nx) :=
              SameAfter.trans (sameAfter_goto heff) hsameB
            refine ⟨tagAtt a Nx ++ N, back', by
                simpa only [List.append_assoc] using hMN, hrecN, fun r => ?_,
              hsdN, hmatN, ?_, ?_⟩
            · have h1 := hkey Lrest back r
              have h2 := hansN r
              simp only [List.append_assoc, List.singleton_append] at h1
              simp only [List.append_assoc] at h2 ⊢
              exact h1.trans h2
            · intro y hy
              rcases List.mem_append.mp hy with hy' | hy'
              · rw [fst_of_tagAtt hy']; exact hale
              · exact hleN y hy'
            · intro q hq
              simpa only [List.append_assoc] using hseenN q hq
          -- The thread accepts: it records its match and kills the rest.
          have harmAccept : ∀ (stA stW stD stF : PikeSt) (hv : Nat),
              Runs re s mo start a th.pc pos tr []
                (.found ⟨pos, (tr.set! 0 (a : Nat).toUInt32).set! 1
                  pos.toUInt32⟩) →
              pikeWrite stA re.novec th.h 1 pos.toUInt32 lim = .ok (stW, hv) →
              pikeDrop stW mh lim = .ok stD →
              dropRest lim rest stD = .ok stF →
              (Except.ok ⟨stF, hv, false, true⟩ : POut StepOut) = .ok out →
              stA.rc = st.rc → stA.free = st.free → stA.pool = st.pool →
              stA.seen = st.seen → stA.stk = st.stk → stA.nlist = st.nlist →
              ∃ (N : List MEntry) (back' : Out),
                MList re s out.st.pool (pos + 1) out.st.nlist.toList (P ++ N) ∧
                OnRecord re out.st.pool out.mh out.matched back' ∧
                (∀ r, MergeAfter re s mo start
                    (P ++ (a, (th.pc, (⟨pos, tr⟩ : Spec.Thread))) :: Lrest)
                    back r ↔
                  MergeAfter re s mo start (P ++ N) back' r) ∧
                out.seeding = !out.matched ∧
                (matched = true → out.matched = true) ∧
                (∀ x ∈ N, x.1 ≤ pos) ∧
                (∀ q : Nat, out.st.seen[q]! = true →
                  Settled re s mo start pos (pos + 1) (P ++ N) q) := by
            intro stA stW stD stF hv hruns hw hdr hrst hout hrcA hfreeA hpoolA
              hseenA hstkA hnlA
            injection hout with hout
            subst hout
            have howA : Owned re.novec stA.rc stA.free stA.pool
                (th.h :: buildLive true stA
                  (rest.map Th.h ++ mhList mh)) := by
              rw [hrcA, hfreeA, hpoolA, buildLive, parkList_true, hstkA, hnlA]
              exact hmid
            have hwb := pikeWrite_block_owned hslot1 howA hw
            have hfreshv := pikeWrite_fresh howA hw
            have hkeepW : ∀ k ∈ handles st.nlist,
                blockAt stW.pool re.novec k
                  = blockAt stA.pool re.novec k := by
              intro k hk
              have hkl : k ∈ buildLive true stA
                  (rest.map Th.h ++ mhList mh) := by
                rw [buildLive, parkList_true, hnlA]
                exact List.mem_append_left _ (List.mem_append_right _ hk)
              refine pikeWrite_block_keep_owned hslot1 ?_
                (List.mem_cons_of_mem _ hkl) howA hw
              intro hkv
              exact hfreshv (hkv ▸ hkl)
            obtain ⟨-, heW⟩ := pikeWrite_ok hw
            obtain ⟨-, hnlW⟩ := pikeWrite_lists hw
            obtain ⟨-, heD⟩ := pikeDrop_ok hdr
            obtain ⟨-, hnlD⟩ := pikeDrop_lists hdr
            obtain ⟨hplF, hnlF, -, heF⟩ := dropRest_frame rest _ _ hrst
            have hplA : stF.pool = stW.pool := by
              rw [hplF, pikeDrop_pool hdr]
            have hnlS : stF.nlist = st.nlist := by
              rw [hnlF, hnlD, hnlW, hnlA]
            have hseF : stF.seen = st.seen := by rw [heF, heD, heW, hseenA]
            have hmhv : mhList hv = [hv] :=
              (write_owned hw howA).1.mhList_head
            have hvne : hv ≠ none32 := by
              intro hq
              rw [mhList, if_pos hq] at hmhv
              exact absurd hmhv (by simp)
            refine ⟨[], .found ⟨pos, (tr.set! 0 (a : Nat).toUInt32).set! 1
              pos.toUInt32⟩, ?_, ?_, ?_, rfl, fun _ => rfl, by simp, ?_⟩
            · refine ⟨?_, by simpa using hP.2.1, by simpa using hP.2.2⟩
              rw [List.append_nil]
              show ThList re stF.pool (pos + 1) stF.nlist.toList (untag P)
              rw [hnlS]
              refine ThList.ofPool hP.1 (fun y hy => ?_)
              rw [hplA, hkeepW y.h (mem_handles_of_toList hy), hpoolA]
            · refine Or.inr ⟨rfl, hvne, _, rfl, ?_⟩
              show Agree re.novec (blockAt stF.pool re.novec hv) _
              rw [hplA, hwb, hpoolA]
              exact (agree_set_tag hnov hat.2.2 hlowx).set_both 1 pos.toUInt32
            · intro r
              rw [mergeAfter_append P
                  ((a, (th.pc, (⟨pos, tr⟩ : Spec.Thread))) :: Lrest),
                mergeAfter_append P []]
              refine or_congr Iff.rfl (and_congr Iff.rfl ?_)
              rw [mergeAfter_give hruns]
              exact Iff.rfl
            · intro q hq
              rw [show (⟨stF, hv, false, true⟩ : StepOut).st = stF from rfl,
                hseF] at hq
              simpa using (hseen q hq).attMono haP
          -- The dispatch itself.
          have ha32 : a < 2 ^ 32 := by omega
          have hpos32 : pos < 2 ^ 32 := by omega
          have hstart32 : start < 2 ^ 32 := by omega
          simp only [stepThreads] at hgo
          split at hgo
          · exact absurd_error hgo
          · cases hop : (re.code[th.pc]! : Inst).op <;> simp only [hop] at hgo
            case chr | chrCI | cls | any | anyNoNL =>
              all_goals
                (split at hgo
                 · rename_i hcond
                   have heff : eff re s mo start a th.pc pos tr
                       = .goto (th.pc + 1) (pos + 1) tr := by
                     simp only [eff, hop]
                     rw [if_pos hcond]
                   split at hgo
                   · exact absurd_error hgo
                   · rename_i stB hadd
                     exact harmAdd _ _ heff hadd hgo rfl rfl rfl rfl rfl rfl
                 · rename_i hcond
                   have heff : eff re s mo start a th.pc pos tr = .fail := by
                     simp only [eff, hop]
                     rw [if_neg hcond]
                   split at hgo
                   · exact absurd_error hgo
                   · rename_i stB hdr
                     exact harmDrop _ _ (fun A => sameAfter_fail heff) hdr hgo
                       rfl rfl rfl rfl rfl rfl)
            case accept =>
              have hbeg : st.pool[th.h * re.novec]! = (a : Nat).toUInt32 :=
                attempt_of_pool hnov hat hlowx
              simp only [hbeg, beq_ofNat32 ha32 hpos32, beq_ofNat32 ha32 hstart32,
                beq_nat_comm a pos] at hgo
              split at hgo
              · rename_i hrefuse
                have heff : eff re s mo start a th.pc pos tr = .fail := by
                  simp only [eff, hop]
                  rw [if_pos hrefuse]
                split at hgo
                · exact absurd_error hgo
                · rename_i stB hdr
                  exact harmDrop _ _ (fun A => sameAfter_fail heff) hdr hgo
                    rfl rfl rfl rfl rfl rfl
              · rename_i hrefuse
                have heff : eff re s mo start a th.pc pos tr =
                    .give ⟨pos, (tr.set! 0 (a : Nat).toUInt32).set! 1
                      pos.toUInt32⟩ := by
                  simp only [eff, hop]
                  rw [if_neg hrefuse]
                have hruns : Runs re s mo start a th.pc pos tr []
                    (.found ⟨pos, (tr.set! 0 (a : Nat).toUInt32).set! 1
                      pos.toUInt32⟩) := by
                  rw [runs_eff, heff]
                  rfl
                split at hgo
                · exact absurd_error hgo
                · rename_i stW hv hw
                  split at hgo
                  · exact absurd_error hgo
                  · rename_i stD hdr
                    split at hgo
                    · exact absurd_error hgo
                    · rename_i stF hrst
                      exact harmAccept _ _ _ _ _ hruns hw hdr hrst hgo rfl rfl
                        rfl rfl rfl rfl
            all_goals exact absurd hparkx (by simp [Parked, hop])

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

/-! ## Seeding a position

A seed is a fresh block, blanked and stamped with the attempt, and a
closure build on top of it. It goes in at the bottom of the list, which is
what makes an earlier start outrank a later one — the leftmost rule, read
as priority order. -/

/-- A write inside the ovector leaves the counters above it alone, so a
configuration that fits still fits. -/
theorem Fit.setLow {re : Re} {s : ByteArray} {pc pos i : Nat}
    {regs : Spec.Regs} (h : Fit re s pc pos regs) (hi : i < re.novec)
    (x : UInt32) : Fit re s pc pos (regs.set! i x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hkey : ∀ j, re.novec ≤ j → (regs.set! i x)[j]! = regs[j]! :=
    fun j hj => getBang_set_other regs i (by omega)
  refine ⟨h1, by
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    exact h2, fun r hr => ?_, fun r hr hre => ?_, fun r hr hge hlt => ?_⟩
  · rw [hkey _ (by omega)]
    exact h3 r hr
  · rw [hkey _ (by omega)]
    exact h4 r hr hre
  · refine ⟨fun hb => ?_, fun hb => ?_⟩
    · rw [hkey _ (by omega)]
      exact (h5 r hr hge hlt).1 hb
    · rw [hkey _ (by omega), hkey _ (by omega)]
      exact (h5 r hr hge hlt).2 hb

/-- Blanking a block and stamping the attempt into it touches that block
and no other. -/
private theorem blank_other (pool : Array UInt32) (novec h : Nat) :
    ∀ m, ∀ j, (∀ i, i < m → j ≠ h * novec + i) →
      ((List.range m).foldl (fun (p : Array UInt32) i =>
        p.set! (h * novec + i) unset32) pool)[j]! = pool[j]! := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hj
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [getBang_set_other _ _ (hj m (by omega))]
      exact ih j (fun i hi => hj i (by omega))

private theorem blockAt_seed_keep (pool : Array UInt32) (novec sh k pos : Nat)
    (hnov : 0 < novec) (hne : k ≠ sh) :
    blockAt (((List.range novec).foldl
        (fun (p : Array UInt32) i => p.set! (sh * novec + i) unset32)
        pool).set! (sh * novec) pos.toUInt32) novec k
      = blockAt pool novec k := by
  refine blockAt_congr (fun i hi => ?_)
  rw [getBang_set_other _ _ (by
      simpa using block_disjoint hne hi hnov),
    blank_other pool novec sh novec (k * novec + i)
      (fun j hj => block_disjoint hne hi hj)]

set_option maxHeartbeats 1000000 in
/-- Seeding a position, read against the mirror. The block a seed takes is
blank but for the attempt in slot zero, which is the register file the
specification hands an attempt with the machine's one pre-write already in
it; on top of it sits one more closure build, parked at the bottom of the
list the position is running. -/
theorem pikeSeed_refine {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start pos : Nat} {ext : List Nat} {st st' : PikeSt} {L : List MEntry}
    (he : Eligible re) (hs : s.size ≤ ceiling)
    (hfit0 : Fit re s 0 pos
      ((Array.replicate re.nregs unset32).set! 0 pos.toUInt32))
    (hok : pikeSeed re s mo lim start pos st = .ok st')
    (hnoskip : ¬ (pos > start ∧ Re.skipsAttempt re s pos = true))
    (hstk : st.stk.size = 0)
    (how : Owned re.novec st.rc st.free st.pool (buildLive false st ext))
    (hcl : MList re s st.pool pos st.clist.toList L)
    (hseen : ∀ q : Nat, st.seen[q]! = true →
      Settled re s mo start pos pos L q) :
    ∃ N : List Entry,
      MList re s st'.pool pos st'.clist.toList (L ++ tagAtt pos N) ∧
      MSame re s mo start L
        [(pos, (0, (⟨pos, (Array.replicate re.nregs unset32).set! 0
          pos.toUInt32⟩ : Spec.Thread)))] (tagAtt pos N) ∧
      st'.stk.size = 0 ∧
      (∀ k ∈ ext, blockAt st'.pool re.novec k = blockAt st.pool re.novec k) ∧
      (∀ q : Nat, st'.seen[q]! = true →
        Settled re s mo start pos pos (L ++ tagAtt pos N) q) := by
  have hnov : 0 < re.novec := by have := he.novec; omega
  have hnreg : re.novec ≤ re.nregs := by
    have h2 := hfit0.2.1
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      Array.size_replicate] at h2
    omega
  have hlow0 : ((Array.replicate re.nregs unset32).set! 0 pos.toUInt32)[0]!
      = pos.toUInt32 :=
    getBang_set_self _ (by rw [Array.size_replicate]; omega)
  simp only [pikeSeed] at hok
  split at hok
  · rename_i hsk
    refine absurd ?_ hnoskip
    rw [Re.skipsAttempt]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsk ⊢
    refine ⟨?_, ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩ <;> simp_all
  · split at hok
    · exact absurd_error hok
    · rename_i stT sh ht
      obtain ⟨hkT, heT⟩ := pikeTake_ok ht
      obtain ⟨hclT, hnlT⟩ := pikeTake_lists ht
      obtain ⟨htake, -⟩ := pikeTake_owned ht how
      have hfresh : sh ∉ buildLive false st ext := pikeTake_fresh ht how
      have hbl : buildLive false stT ext = buildLive false st ext := by
        simp only [buildLive, hkT, parkList_eq hclT hnlT]
      have hroom : sh * re.novec + re.novec ≤ stT.pool.size :=
        room_of_owned htake List.mem_cons_self
      have hkeepT : ∀ k ∈ buildLive false st ext,
          blockAt stT.pool re.novec k = blockAt st.pool re.novec k := fun k hk =>
        pikeTake_block (room_of_owned how hk) ht
      split at hok
      · exact absurd_error hok
      · -- The blanked, stamped state the build starts from.
        have hbody : ∀ stS : PikeSt,
            pikeAdd re s mo lim false pos 0 sh stS = .ok st' →
            stS.rc = stT.rc → stS.free = stT.free →
            stS.pool = ((List.range re.novec).foldl
              (fun (p : Array UInt32) k =>
                p.set! (sh * re.novec + k) unset32) stT.pool).set!
                (sh * re.novec) pos.toUInt32 →
            stS.stk = stT.stk → stS.seen = stT.seen →
            stS.clist = stT.clist → stS.nlist = stT.nlist →
            ∃ N : List Entry,
              MList re s st'.pool pos st'.clist.toList (L ++ tagAtt pos N) ∧
              MSame re s mo start L
                [(pos, (0, (⟨pos, (Array.replicate re.nregs unset32).set! 0
                  pos.toUInt32⟩ : Spec.Thread)))] (tagAtt pos N) ∧
              st'.stk.size = 0 ∧
              (∀ k ∈ ext,
                blockAt st'.pool re.novec k = blockAt st.pool re.novec k) ∧
              (∀ q : Nat, st'.seen[q]! = true →
                Settled re s mo start pos pos (L ++ tagAtt pos N) q) := by
          intro stS hadd hrcS hfreeS hpoolS hstkS hseenS hclS hnlS
          have hsizeS : stS.pool.size = stT.pool.size := by
            rw [hpoolS, Array.size_set!]
            exact blank_size _ _ _ _
          have hblS : buildLive false stS ext = buildLive false stT ext := by
            simp only [buildLive, hstkS, parkList_eq hclS hnlS]
          have hownS : Owned re.novec stS.rc stS.free stS.pool
              (sh :: buildLive false stS ext) := by
            rw [hrcS, hfreeS, hblS, hbl]
            exact Owned.ofPool htake hsizeS
          have hblkS : blockAt stS.pool re.novec sh
              = (Array.replicate re.novec unset32).set! 0 pos.toUInt32 := by
            rw [hpoolS]
            exact blockAt_seed stT.pool re.novec sh pos hnov hroom
          have hkeepS : ∀ k, k ≠ sh →
              blockAt stS.pool re.novec k = blockAt stT.pool re.novec k := by
            intro k hk
            rw [hpoolS]
            exact blockAt_seed_keep stT.pool re.novec sh k pos hnov hk
          have hagS : Agree re.novec (blockAt stS.pool re.novec sh)
              ((Array.replicate re.nregs unset32).set! 0 pos.toUInt32) := by
            rw [hblkS]
            refine ⟨by
                simp [Array.set!_eq_setIfInBounds], by
                simp only [Array.set!_eq_setIfInBounds,
                  Array.size_setIfInBounds, Array.size_replicate]
                exact hnreg, fun i hi => ?_⟩
            by_cases h0 : i = 0
            · subst h0
              rw [getBang_set_self _ (by rw [Array.size_replicate]; omega),
                getBang_set_self _ (by rw [Array.size_replicate]; omega)]
            · rw [getBang_set_other _ 0 h0, getBang_set_other _ 0 h0,
                getElem!_pos _ i (by rw [Array.size_replicate]; omega),
                getElem!_pos _ i (by rw [Array.size_replicate]; omega)]
              simp
          obtain ⟨N, -, hstk', hPN, hsameN, hfitN, htagN, hparkN, hextN,
            hseenN⟩ :=
            pikeAdd_refine (start := start) (attempt := pos)
              (tag := pos.toUInt32) (P := L) (ext := ext)
              (t0 := ⟨pos, (Array.replicate re.nregs unset32).set! 0
                pos.toUInt32⟩)
              he hs (Nat.le_refl _) hadd (by rw [hstkS, hkT]; exact hstk)
              hownS ⟨rfl, rfl, hagS⟩ rfl hfit0 hlow0
              (by
                show ThList re stS.pool pos stS.clist.toList (untag L)
                rw [hclS, hclT]
                refine ThList.ofPool hcl.1 (fun y hy => ?_)
                have hy' : y.h ∈ buildLive false st ext :=
                  List.mem_append_left _ (List.mem_append_right _
                    (mem_handles_of_toList hy))
                rw [hkeepS y.h (fun hq => hfresh (hq ▸ hy')), hkeepT y.h hy'])
              (fun q hq => Or.inl (hseen q (by rw [← heT, ← hseenS]; exact hq)))
          refine ⟨N, ⟨?_, ?_, ?_⟩, hsameN, hstk', ?_, ?_⟩
          · show ThList re st'.pool pos st'.clist.toList
              (untag (L ++ tagAtt pos N))
            rw [untag_append, untag_tagAtt]
            exact hPN
          · intro y hy
            rcases List.mem_append.mp hy with hy' | hy'
            · exact hcl.2.1 y hy'
            · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy'
              exact ⟨Nat.le_refl _, (hfitN f hf).1, (hfitN f hf).2,
                htagN f hf, hparkN f hf⟩
          · refine List.pairwise_append.mpr
              ⟨hcl.2.2, pairwise_tagAtt pos N, fun y hy z hz => ?_⟩
            rw [fst_of_tagAtt hz]
            exact (hcl.2.1 y hy).1
          · intro k hk
            have hk' : k ∈ buildLive false st ext :=
              List.mem_append_right _ hk
            rw [hextN k hk, hkeepS k (fun hq => hfresh (hq ▸ hk')),
              hkeepT k hk']
          · intro q hq
            rcases hseenN q hq with h | ⟨h1, -⟩
            · exact h
            · exact (hseen q (by rw [← heT, ← hseenS]; exact h1)).mono
                (tagAtt pos N)
        exact hbody _ hok rfl rfl rfl rfl rfl rfl rfl

/-! ## What one attempt's seed answers

The seed the machine plants is the specification's blank register file
with the attempt already in slot zero, and that is the one cell no search
reads. So a completed search from it answers what `Spec.attemptThreads`
filters out of the specification's own search, which is the last thing the
position loop needs before it can be read against `Spec.scan`. -/

/-- The register file a seed starts on fits, the machine's one pre-write
included: the write lands inside the ovector, where none of the three
invariants looks. -/
theorem fit_seed_tag {p : Pat} {s : ByteArray} {attempt : Nat}
    (hc : Covered p.root) (hs : s.size ≤ ceiling) (hatt : attempt ≤ s.size) :
    Fit (compile p) s 0 attempt
      ((Array.replicate (compile p).nregs unset32).set! 0 attempt.toUInt32) :=
  (fit_seed hc hs hatt).setLow (show 0 < 2 * (p.ncap + 1) by omega) _

/-- One attempt's whole search, read against the specification. -/
theorem seed_attempt_refines {p : Pat} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {r : Out} (hw : Wf p) (hs : s.size ≤ ceiling)
    (hatt : attempt ≤ s.size)
    (hruns : Runs (compile p) s mo start attempt 0 attempt
      ((Array.replicate (compile p).nregs unset32).set! 0 attempt.toUInt32)
      [] r) :
    ∃ tsO, Spec.attemptThreads (Spec.suffFuel s.size p.root) p s mo start
        attempt = some tsO ∧
      OutAgrees (2 * (p.ncap + 1)) attempt r tsO := by
  have hnreg : 2 * (p.ncap + 1) ≤ (compile p).nregs := by
    show 2 * (p.ncap + 1) ≤ (p.ncap + 1) * 2 + (compile p).reps.size * 2
    omega
  obtain ⟨ts, hden⟩ := Option.isSome_iff_exists.mp
    (denot_some (c := mctx (compile p) s mo) (novec := 2 * (p.ncap + 1))
      (fuel := Spec.suffFuel s.size p.root) (r0 := 0) (a := p.root)
      (pos := attempt) (regs := Array.replicate (compile p).nregs unset32)
      hatt (by rw [Array.size_replicate]; exact hnreg) (Nat.le_refl _))
  refine runs_attempt_refines hw.1.covered hw.2 hs hatt (hw.repCap_lt hs)
    hden ?_
  refine (runs_offTag (show 0 < (compile p).novec from by
    show 0 < 2 * (p.ncap + 1)
    omega) ?_).mp hruns
  exact ⟨by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds],
    fun i hi => getBang_set_other _ 0 hi⟩

/-! ## The position loop

The loop walks the subject one position at a time, seeding at each and
stepping the list it has. `Spec.scan` walks attempts instead, and the two
sequences are the same one: the positions the loop seeds are the attempts
the scan opens, since both apply the same bumpalong skip. `Link` is the
one piece of bookkeeping that costs anything — where the machine declines
a position the scan is already standing one further on. -/

/-- A build that parks into the current list leaves the next one alone:
none of its arms touches the list it is not writing. -/
private theorem pikeAdd_go_nlist (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (pos : Nat) :
    ∀ (fuel : Nat) (st st' : PikeSt),
      pikeAdd.go re s mo lim false pos fuel st = .ok st' →
      st'.nlist = st.nlist := by
  intro fuel
  induction fuel with
  | zero =>
      intro st st' hok
      rw [pikeAdd.go] at hok
      exact absurd_error hok
  | succ fuel ih =>
      intro st st' hok
      simp only [pikeAdd.go] at hok
      split at hok
      · injection hok with hok
        subst hok
        rfl
      · split at hok
        · split at hok
          · exact absurd_error hok
          · rename_i stD hD
            exact (ih _ _ hok).trans (pikeDrop_lists hD).2
        · split at hok
          · exact absurd_error hok
          · repeat' split at hok
            all_goals first
              | exact absurd_error hok
              | (rename_i _ stA hA _ stB hB
                 exact ((ih _ _ hok).trans (pikeDefer_lists hB).2).trans
                   (pikeDefer_lists hA).2)
              | (rename_i _ stW _ hW _ stD hD
                 exact ((ih _ _ hok).trans (pikeDefer_lists hD).2).trans
                   (pikeWrite_lists hW).2)
              | (rename_i _ stD hD
                 exact (ih _ _ hok).trans (pikeDefer_lists hD).2)
              | (rename_i _ stD hD
                 exact (ih _ _ hok).trans (pikeDrop_lists hD).2)
              | (rename_i _ stP hP
                 exact (ih _ _ hok).trans (((pikePark_lists hP).2 rfl).1))

private theorem pikeAdd_nlist {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {pos pc0 h0 : Nat} {st st' : PikeSt}
    (hok : pikeAdd re s mo lim false pos pc0 h0 st = .ok st') :
    st'.nlist = st.nlist := by
  rw [pikeAdd] at hok
  split at hok
  · exact absurd_error hok
  · rename_i stD hdef
    exact (pikeAdd_go_nlist re s mo lim pos _ _ _ hok).trans
      (pikeDefer_lists hdef).2

/-- And so does a seed, which is a build with a fresh block under it. -/
theorem pikeSeed_nlist {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start pos : Nat} {st st' : PikeSt}
    (hok : pikeSeed re s mo lim start pos st = .ok st') :
    st'.nlist = st.nlist := by
  simp only [pikeSeed] at hok
  split at hok
  · injection hok with hok
    subst hok
    rfl
  · split at hok
    · exact absurd_error hok
    · rename_i stT sh ht
      split at hok
      · exact absurd_error hok
      · exact (pikeAdd_nlist hok).trans (pikeTake_lists ht).2

/-- The bumpalong never declines a position past the subject's end. -/
theorem Re.skipsAttempt_lt {re : Re} {s : ByteArray} {pos : Nat}
    (h : Re.skipsAttempt re s pos = true) : pos < s.size := by
  rw [Re.skipsAttempt] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- And a position it declines carries LF, not CR, so the next one is not
declined in turn. -/
theorem Re.skipsAttempt_byte {re : Re} {s : ByteArray} {pos : Nat}
    (h : Re.skipsAttempt re s pos = true) : (byteAt s pos == 0x0A) = true := by
  rw [Re.skipsAttempt] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem Re.skipsAttempt_next {re : Re} {s : ByteArray} {pos : Nat}
    (h : Re.skipsAttempt re s pos = true) :
    Re.skipsAttempt re s (pos + 1) = false := by
  have hlf := Re.skipsAttempt_byte h
  rw [Re.skipsAttempt]
  simp only [Bool.and_eq_false_iff]
  simp only [beq_iff_eq] at hlf
  refine Or.inl (Or.inl (Or.inr ?_))
  simp only [Nat.add_sub_cancel, beq_eq_false_iff_ne, hlf]
  decide

/-- Agreement over the ovector reads the same both ways round. -/
theorem Agree.symm {novec : Nat} {u v : Spec.Regs} (h : Agree novec u v) :
    Agree novec v u := ⟨h.2.1, h.1, fun i hi => (h.2.2 i hi).symm⟩

/-- A cleared visited set marks nothing. -/
private theorem replicate_false_get (n q : Nat) :
    (Array.replicate n false)[q]! = false := by
  by_cases h : q < n
  · rw [getElem!_pos _ q (by simpa using h)]
    simp
  · rw [getElem!_neg _ q (by simpa using h)]
    rfl

/-- A merge standing on a recorded match can only answer found. -/
theorem mergeAfter_found {re : Re} {s : ByteArray} {mo : MOpts} {start : Nat}
    {t : Spec.Thread} : ∀ {L : List MEntry} {r : Out},
      MergeAfter re s mo start L (.found t) r → ∃ w, r = .found w := by
  intro L
  induction L with
  | nil => exact fun h => ⟨t, h⟩
  | cons x L ih =>
      intro r h
      obtain ⟨a, e⟩ := x
      rcases (show _ ∨ _ from h) with ⟨w, hw, -⟩ | ⟨-, hrest⟩
      · exact ⟨w, hw⟩
      · exact ih hrest

/-- Where the scan stands against a position the loop is about to seed: at
that position, or one past it where the bumpalong declines to start
there. -/
def Link (re : Re) (s : ByteArray) (start q att : Nat) : Prop :=
  (att = q ∧ ¬ (start < q ∧ Re.skipsAttempt re s q = true)) ∨
    (att = q + 1 ∧ start < q ∧ Re.skipsAttempt re s q = true)

/-- What the live merge decides: a found answer settles the whole call, and
an empty one hands the question on to the attempts the loop has not opened
yet, which is the scan's own tail. -/
def Decides (p : Pat) (tail top : Option Spec.MatchAnswer) : Out → Prop
  | .found t => top = some (.found (t.regs.extract 0 (2 * (p.ncap + 1))))
  | .nomatch => top = tail

/-- And what an answer of the position loop means for the whole call. A
budget refusal claims nothing. -/
def PikeAgrees (p : Pat) (top : Option Spec.MatchAnswer) :
    PikeSt × Nat × PikeEnd → Prop
  | (st, mh, .matched) =>
      top = some (.found (blockAt st.pool (2 * (p.ncap + 1)) mh))
  | (_, _, .noMatch) => top = some .notFound
  | (_, _, .exceeded) => True

set_option maxHeartbeats 4000000 in
/-- The position loop against the scan. Each iteration seeds the position
it stands at, steps the list it has into the next one, and stops where the
specification's scan runs out of attempts: past the subject's end, or with
nothing live and nothing left to open. The merge decides the call outright
where it finds something, and hands it to the scan's own tail where it does
not — which is what `Decides` says and what `Link` keeps aligned. -/
theorem pikeLoop_refine {p : Pat} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {anchored : Bool} {words : Nat}
    (hw : Wf p) (hpike : (compile p).pike = true) (hs : s.size ≤ ceiling)
    (hstart : start ≤ s.size)
    (hanch : anchored = (p.opts.anchored || mo.anchored)) :
    ∀ (steps pos : Nat) (st : PikeSt) (mh : Nat) (matched : Bool)
      (L : List MEntry) (back : Out) (tail top : Option Spec.MatchAnswer),
      st.stk.size = 0 → st.nlist.size = 0 →
      st.seen.size = (compile p).code.size →
      Owned (compile p).novec st.rc st.free st.pool
        (buildLive false st (mhList mh)) →
      MList (compile p) s st.pool pos st.clist.toList L →
      OnRecord (compile p) st.pool mh matched back →
      (∀ q : Nat, st.seen[q]! = true →
        Settled (compile p) s mo start pos pos L q) →
      start ≤ pos → pos ≤ s.size →
      (∀ r, MergeAfter (compile p) s mo start L back r →
        Decides p tail top r) →
      (matched = false → (!anchored || pos == start) = true →
        ∃ att sc, s.size + 1 - att ≤ sc ∧ Link (compile p) s start pos att ∧
          tail = Spec.scan (Spec.suffFuel s.size p.root) p s mo start att sc) →
      (matched = false → (!anchored || pos == start) = false →
        tail = some .notFound) →
      PikeAgrees p top
        (pikeLoop (compile p) s mo lim start anchored words steps pos st mh
          (!matched) matched) := by
  have he : Eligible (compile p) := compile_eligible hw hpike
  have hnov : 0 < (compile p).novec := by have := he.novec; omega
  intro steps
  induction steps with
  | zero =>
      intro pos st mh matched L back tail top _ _ _ _ _ _ _ _ _ _ _ _
      rw [pikeLoop]
      exact True.intro
  | succ steps ih =>
      intro pos st mh matched L back tail top hstk hnl hsz how hL hrec hseen
        hposge hposle hdec hlinkT hlinkF
      -- What the seed leaves behind, and where the scan then stands.
      have hseedStage : ∀ stS : PikeSt,
          (if (!matched) && (!anchored || pos == start) then
              pikeSeed (compile p) s mo lim start pos st
            else (Except.ok st : POut PikeSt)) = .ok stS →
          ∃ (L' : List MEntry) (tail' : Option Spec.MatchAnswer),
            stS.stk.size = 0 ∧ stS.nlist = st.nlist ∧
            stS.seen.size = (compile p).code.size ∧
            Owned (compile p).novec stS.rc stS.free stS.pool
              (buildLive false stS (mhList mh)) ∧
            MList (compile p) s stS.pool pos stS.clist.toList L' ∧
            OnRecord (compile p) stS.pool mh matched back ∧
            (∀ q : Nat, stS.seen[q]! = true →
              Settled (compile p) s mo start pos pos L' q) ∧
            (∀ r, MergeAfter (compile p) s mo start L' back r →
              Decides p tail' top r) ∧
            (matched = false → (anchored = true ∨ s.size ≤ pos) →
              tail' = some .notFound) ∧
            (matched = false → pos < s.size →
              (!anchored || (pos + 1) == start) = true →
              ∃ att sc, s.size + 1 - att ≤ sc ∧
                Link (compile p) s start (pos + 1) att ∧
                tail' = Spec.scan (Spec.suffFuel s.size p.root) p s mo start
                  att sc) ∧
            (matched = false → pos < s.size →
              (!anchored || (pos + 1) == start) = false →
              tail' = some .notFound) := by
        intro stS hsd
        split at hsd
        · -- The loop offers this position.
          rename_i hcond
          have hcc : (!matched) = true ∧ (!anchored || pos == start) = true := by
            simpa only [Bool.and_eq_true] using hcond
          have hmf : matched = false := by
            cases matched
            · rfl
            · exact absurd hcc.1 (by simp)
          have hseedTest := hcc.2
          obtain ⟨-, hmhn, hbn⟩ : matched = false ∧ mh = none32 ∧
              back = Out.nomatch := by
            rcases hrec with h | ⟨h, -⟩
            · exact h
            · exact absurd h (by rw [hmf]; simp)
          by_cases hsk : start < pos ∧ Re.skipsAttempt (compile p) s pos = true
          · -- The bumpalong declines this start; the scan already skipped it.
            rw [pikeSeed_skip hsk.1 hsk.2] at hsd
            injection hsd with hsd
            subst hsd
            have hanchF : anchored = false := by
              cases hA : anchored
              · rfl
              · exfalso
                rw [hA] at hseedTest
                simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hseedTest
                omega
            have hposlt : pos < s.size := Re.skipsAttempt_lt hsk.2
            refine ⟨L, tail, hstk, rfl, hsz, how, hL, hrec, hseen, hdec,
              ?_, ?_, ?_⟩
            · intro _ hq
              exfalso
              rcases hq with hq | hq
              · rw [hanchF] at hq
                exact absurd hq (by simp)
              · omega
            · intro _ _ _
              obtain ⟨att, sc, hsc, hlink, htail⟩ := hlinkT hmf hseedTest
              refine ⟨att, sc, hsc, ?_, htail⟩
              rcases hlink with ⟨-, hno⟩ | ⟨hat, -, -⟩
              · exact absurd hsk hno
              · refine Or.inl ⟨hat, fun hq => ?_⟩
                rw [Re.skipsAttempt_next hsk.2] at hq
                exact absurd hq.2 (by simp)
            · intro _ _ hq
              exfalso
              rw [hanchF] at hq
              simp at hq
          · -- The seed goes in at the bottom of the list.
            obtain ⟨N, hMLN, hmsN, hstkN, hextN, hseenN⟩ :=
              pikeSeed_refine (ext := mhList mh) he hs
                (fit_seed_tag hw.1.covered hs hposle) hsd hsk hstk how hL hseen
            obtain ⟨howN, -, hszN, -, -⟩ :=
              pikeSeed_owned (compile p) s mo lim start pos (mhList mh) hsd hsz
                hstk how
            obtain ⟨att, sc, hsc, hlink, htail⟩ := hlinkT hmf hseedTest
            have hatt : att = pos := by
              rcases hlink with ⟨h, -⟩ | ⟨-, h1, h2⟩
              · exact h
              · exact absurd ⟨h1, h2⟩ hsk
            rw [hatt] at hsc htail
            obtain ⟨sc0, rfl⟩ : ∃ sc0, sc = sc0 + 1 := ⟨sc - 1, by omega⟩
            obtain ⟨t0, ht0⟩ : ∃ t0 : Spec.Thread, t0 =
                ⟨pos, (Array.replicate (compile p).nregs unset32).set! 0
                  pos.toUInt32⟩ := ⟨_, rfl⟩
            rw [← ht0] at hmsN
            -- The list with the seed at the bottom answers what the seed's
            -- own thread answers, read behind it.
            have hkey : ∀ r, MergeAfter (compile p) s mo start
                (L ++ tagAtt pos N) back r ↔
                MergeAfter (compile p) s mo start (L ++ [(pos, (0, t0))])
                  back r := by
              intro r
              have h := hmsN [] back r
              simpa only [List.append_nil] using h.symm
            -- What the seed's own attempt answers, read against the scan.
            have hseedScan : ∀ r, MergeAfter (compile p) s mo start
                [(pos, (0, t0))] back r →
                (∀ w, r = .found w →
                  Spec.scan (Spec.suffFuel s.size p.root) p s mo start pos
                      (sc0 + 1) =
                    some (.found (w.regs.extract 0 (2 * (p.ncap + 1))))) ∧
                (r = .nomatch →
                  Spec.scan (Spec.suffFuel s.size p.root) p s mo start pos
                      (sc0 + 1) =
                    if (p.opts.anchored || mo.anchored ||
                        decide (pos ≥ s.size)) = true then some .notFound
                    else Spec.scan (Spec.suffFuel s.size p.root) p s mo start
                      (if Spec.skipsAttempt p s (pos + 1) then pos + 1 + 1
                       else pos + 1) sc0) := by
              intro r hr
              rcases (show _ ∨ _ from hr) with ⟨w, rfl, hrun⟩ | ⟨hrun, rfl⟩
              · rw [ht0] at hrun
                obtain ⟨tsO, hthreads, hout⟩ :=
                  seed_attempt_refines hw hs hposle hrun
                cases htsO : tsO with
                | nil =>
                    rw [htsO] at hout
                    exact absurd hout (by simp [OutAgrees])
                | cons t rest =>
                    rw [htsO] at hout hthreads
                    obtain ⟨hpw, hag⟩ := hout
                    have hszt : t.regs.size = 2 * (p.ncap + 1) := by
                      rw [Spec.attemptThreads] at hthreads
                      obtain ⟨ths, hths, hfil⟩ :=
                        Option.bind_eq_some_iff.mp hthreads
                      simp only [Option.pure_def, Option.some.injEq] at hfil
                      have hmem : t ∈ ths := by
                        have : t ∈ ths.filter (fun t =>
                            Spec.acceptable mo start pos t &&
                              Spec.endOk p s t) := hfil ▸ List.mem_cons_self ..
                        exact (List.mem_filter.mp this).1
                      have := search_size hths t hmem
                      rw [this, Array.size_replicate]
                    refine ⟨fun w' hw' => ?_, fun hq => absurd hq (by simp)⟩
                    injection hw' with hw'
                    subst hw'
                    rw [Spec.scan.eq_def]
                    simp only []
                    rw [hthreads]
                    show some (Spec.MatchAnswer.found
                      ((t.regs.set! 0 pos.toUInt32).set! 1 t.pos.toUInt32)) = _
                    rw [extract_eq_of_agree hag (by
                      simp only [Array.set!_eq_setIfInBounds,
                        Array.size_setIfInBounds]
                      exact hszt)]
              · rw [ht0] at hrun
                obtain ⟨tsO, hthreads, hout⟩ :=
                  seed_attempt_refines hw hs hposle hrun
                have htsO : tsO = [] := by
                  cases tsO with
                  | nil => rfl
                  | cons t rest => exact absurd hout (by simp [OutAgrees])
                rw [htsO] at hthreads
                refine ⟨fun w hw' => absurd (hbn ▸ hw') (by simp), fun _ => ?_⟩
                rw [Spec.scan.eq_def]
                simp only []
                rw [hthreads]
                rfl
            by_cases hstop : (p.opts.anchored || mo.anchored ||
                decide (pos ≥ s.size)) = true
            · refine ⟨L ++ tagAtt pos N, some .notFound, hstkN,
                pikeSeed_nlist hsd, hszN, howN, hMLN, ?_, hseenN, ?_,
                fun _ _ => rfl, ?_, ?_⟩
              · exact Or.inl ⟨hmf, hmhn, hbn⟩
              · intro r hr
                rcases (mergeAfter_append L [(pos, (0, t0))] back r).mp
                  ((hkey r).mp hr) with ⟨w, rfl, hf⟩ | ⟨hn, hsa⟩
                · exact hdec (.found w) (by rw [hbn]; exact hf)
                · have htop : top = tail := hdec .nomatch (by rw [hbn]; exact hn)
                  rcases (show _ ∨ _ from hsa) with ⟨w, rfl, hrun⟩ | ⟨hrun, rfl⟩
                  · show top = some (.found (w.regs.extract 0 (2 * (p.ncap + 1))))
                    rw [htop, htail]
                    exact (hseedScan (.found w) hsa).1 w rfl
                  · rw [hbn]
                    show top = some .notFound
                    rw [htop, htail, (hseedScan r hsa).2 hbn, if_pos hstop]
              · intro _ hlt htest
                exfalso
                have hab : (p.opts.anchored || mo.anchored) = true := by
                  cases hA : (p.opts.anchored || mo.anchored)
                  · exfalso
                    rw [hA] at hstop
                    simp only [Bool.false_or, decide_eq_true_eq] at hstop
                    omega
                  · rfl
                rw [hanch, hab] at htest
                simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at htest
                omega
              · intro _ _ _
                rfl
            · have hanchF : anchored = false := by
                have h1 : (p.opts.anchored || mo.anchored) = false := by
                  cases hA : p.opts.anchored
                  · cases hB : mo.anchored
                    · rfl
                    · exact absurd (by simp [hB]) hstop
                  · exact absurd (by simp [hA]) hstop
                rw [hanch, h1]
              have hposlt : pos < s.size := by
                rcases Nat.lt_or_ge pos s.size with h | h
                · exact h
                · exact absurd (by
                    simp only [Bool.or_eq_true, decide_eq_true_eq]
                    exact Or.inr h) hstop
              refine ⟨L ++ tagAtt pos N,
                Spec.scan (Spec.suffFuel s.size p.root) p s mo start
                  (if Spec.skipsAttempt p s (pos + 1) then pos + 1 + 1
                   else pos + 1) sc0,
                hstkN, pikeSeed_nlist hsd, hszN, howN, hMLN, ?_, hseenN, ?_,
                ?_, ?_, ?_⟩
              · exact Or.inl ⟨hmf, hmhn, hbn⟩
              · intro r hr
                rcases (mergeAfter_append L [(pos, (0, t0))] back r).mp
                  ((hkey r).mp hr) with ⟨w, rfl, hf⟩ | ⟨hn, hsa⟩
                · exact hdec (.found w) (by rw [hbn]; exact hf)
                · have htop : top = tail := hdec .nomatch (by rw [hbn]; exact hn)
                  rcases (show _ ∨ _ from hsa) with ⟨w, rfl, hrun⟩ | ⟨hrun, rfl⟩
                  · show top = some (.found (w.regs.extract 0 (2 * (p.ncap + 1))))
                    rw [htop, htail]
                    exact (hseedScan (.found w) hsa).1 w rfl
                  · rw [hbn]
                    show top = _
                    rw [htop, htail, (hseedScan r hsa).2 hbn, if_neg hstop]
              · intro _ hq
                exfalso
                rcases hq with hq | hq
                · rw [hanchF] at hq
                  exact absurd hq (by simp)
                · omega
              · intro _ _ _
                refine ⟨_, sc0, ?_, ?_, rfl⟩
                · split <;> omega
                · rw [← skipsAttempt_agrees hw.1 s (pos + 1)]
                  by_cases hsp : Re.skipsAttempt (compile p) s (pos + 1) = true
                  · rw [if_pos hsp]
                    exact Or.inr ⟨rfl, by omega, hsp⟩
                  · rw [if_neg hsp]
                    exact Or.inl ⟨rfl, fun hq => hsp hq.2⟩
              · intro _ _ hq
                exfalso
                rw [hanchF] at hq
                simp at hq
        · -- The loop offers nothing here: anchored elsewhere, or a match on
          -- record.
          rename_i hcond
          injection hsd with hsd
          subst hsd
          have hfalseTest : matched = false →
              (!anchored || pos == start) = false := by
            intro hmf
            cases hq : (!anchored || pos == start)
            · rfl
            · exact absurd (by rw [hmf, hq]; rfl) hcond
          refine ⟨L, tail, hstk, rfl, hsz, how, hL, hrec, hseen, hdec,
            ?_, ?_, ?_⟩
          · intro hmf _
            exact hlinkF hmf (hfalseTest hmf)
          · intro hmf _ hq
            exfalso
            have hfalse := hfalseTest hmf
            rw [Bool.or_eq_false_iff] at hfalse
            have hA : anchored = true := by
              cases hA : anchored
              · rw [hA] at hfalse
                exact absurd hfalse.1 (by simp)
              · rfl
            rw [hA] at hq
            simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hq
            omega
          · intro hmf _ _
            exact hlinkF hmf (hfalseTest hmf)
      -- The loop body itself.
      simp only [pikeLoop]
      split
      · exact True.intro
      · rename_i stS hsd
        obtain ⟨L', tail', hstkS, hnlS, hszS, howS, hLS, hrecS, hseenS, hdecS,
          hstopS, hlinkTS, hlinkFS⟩ := hseedStage stS hsd
        have hnlS0 : stS.nlist.size = 0 := by rw [hnlS]; exact hnl
        have hnlnil : stS.nlist.toList = [] := by
          rw [← List.length_eq_zero_iff, Array.length_toList, hnlS0]
        split
        · exact True.intro
        · split
          · exact True.intro
          · rename_i out hstep
            have hlists : buildLive true { stS with
                m := { stS.m with cost := stS.m.cost + words }
                seen := Array.replicate (compile p).code.size false }
                (stS.clist.toList.map Th.h ++ mhList mh) =
                buildLive false stS (mhList mh) := by
              show handles stS.stk ++ handles stS.nlist ++
                  (stS.clist.toList.map Th.h ++ mhList mh) =
                handles stS.stk ++ handles stS.clist ++ mhList mh
              rw [handles_empty hnlS0]
              simp [handles]
            obtain ⟨N, back', hMN, hrecN, hansN, hsdN, hmatN, hleN, hseenN⟩ :=
              stepThreads_refine he hs hstart stS.clist.toList _ mh matched out
                L' [] back 0 hstep hstkS (by rw [hlists]; exact howS) hLS
                ⟨by rw [hnlnil]; exact List.Forall₂.nil, by simp, by simp⟩
                hrecS (Nat.zero_le _) (fun _ _ => Nat.zero_le _) (by simp)
                (fun q hq => absurd ((replicate_false_get _ q).symm.trans hq)
                  (by simp))
            obtain ⟨howO, -, hszO, hstkO, -⟩ :=
              stepThreads_owned (compile p) s mo lim start pos
                (addMeasure true { stS with
                  m := { stS.m with cost := stS.m.cost + words }
                  seen := Array.replicate (compile p).code.size false } +
                  stS.clist.toList.length + 1)
                stS.clist.toList _ mh (!matched) matched out hstep (by simp)
                hstkS (Nat.le_refl _) (by rw [hlists]; exact howS)
            have hmfOut : out.matched = false → matched = false := by
              intro hom
              cases hm : matched
              · rfl
              · exact absurd (hmatN hm) (by rw [hom]; simp)
            have hdecN : ∀ r, MergeAfter (compile p) s mo start N back' r →
                Decides p tail' top r := by
              intro r hr
              exact hdecS r ((hansN r).mpr (by simpa using hr))
            have hMN' : MList (compile p) s out.st.pool (pos + 1)
                out.st.nlist.toList N := by simpa using hMN
            have hemptyPast : s.size ≤ pos → N = [] := by
              intro hq
              refine List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_)
              have := (hMN'.2.1 x hx).2.2.1.1
              omega
            have hemptyList : out.st.nlist.size = 0 → N = [] := by
              intro hq
              have hlen := ThList.length_eq hMN'.1
              rw [Array.length_toList, hq] at hlen
              simp only [untag, List.length_map] at hlen
              exact List.eq_nil_of_length_eq_zero hlen.symm
            -- What a settled loop delivers: with nothing live the merge is
            -- its own record.
            have hdeliver : ∀ stE : PikeSt, stE.pool = out.st.pool → N = [] →
                (out.matched = false → tail' = some .notFound) →
                PikeAgrees p top (stE, out.mh,
                  if out.matched then PikeEnd.matched else .noMatch) := by
              intro stE hpl hnil hnf
              subst hnil
              have hd := hdecN back' (show (back' = back') from rfl)
              cases hom : out.matched with
              | true =>
                  rcases hrecN with ⟨hm, -, -⟩ | ⟨-, -, t, hb, hag⟩
                  · exact absurd hm (by rw [hom]; simp)
                  · rw [hb] at hd
                    rw [show (compile p).novec = 2 * (p.ncap + 1) from rfl]
                      at hag
                    show top = some (.found
                      (blockAt stE.pool (2 * (p.ncap + 1)) out.mh))
                    rw [hd, hpl,
                      extract_eq_of_agree hag.symm (blockAt_size _ _ _)]
              | false =>
                  rcases hrecN with ⟨-, -, hb⟩ | ⟨hm, -, -⟩
                  · rw [hb] at hd
                    show top = some .notFound
                    rw [hd, hnf hom]
                  · exact absurd hm (by rw [hom]; simp)
            split
            · -- Past the subject's end there is no next list at all.
              rename_i hend
              exact hdeliver _ rfl (hemptyPast hend)
                (fun hom => hstopS (hmfOut hom) (Or.inr hend))
            · rename_i hend
              split
              · -- Nothing live, and nothing left to open.
                rename_i hstop2
                have hstop2' : out.st.nlist.size = 0 ∧
                    (!out.seeding || anchored) = true := by
                  simpa only [Bool.and_eq_true, beq_iff_eq] using hstop2
                exact hdeliver _ rfl (hemptyList hstop2'.1)
                  (fun hom => hstopS (hmfOut hom)
                    (Or.inl (by
                      have h := hstop2'.2
                      rw [hsdN, hom] at h
                      simpa using h)))
              · rename_i hstop2
                have hlt : pos < s.size := by omega
                rw [hsdN]
                exact ih (pos + 1) _ out.mh out.matched N back' tail' top
                  hstkO rfl hszO howO hMN' hrecN
                  (fun q hq => ((by simpa using hseenN q hq :
                    Settled (compile p) s mo start pos (pos + 1) N q).attMono
                      (by omega)))
                  (by omega) (by omega) hdecN
                  (fun hom => hlinkTS (hmfOut hom) hlt)
                  (fun hom => hlinkFS (hmfOut hom) hlt)

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

/-! ## S-8, the lockstep half

The claim, spelled the way `BtRunRefinesMatches` is spelled and read
against the same three hypotheses — the parser facts, the documented
subject cap, the counter-wrap bound — plus the one the lockstep matcher
adds: the program is eligible, since an ineligible one is refused at the
door for a reason the specification has no opinion about.

The three clauses come from three places. BadInput is
`pikeRun_badInput_agrees`. The other two are the position loop read
against the scan, and then delivery: at the last position the next list is
empty, because `Live` asks for a position inside the subject, so the merge
is its own record — and `deliver_eq_blockAt` says the ovector handed back
is the block that record names.

`Pcrevera/Proofs/ExecPike.lean` composes this into `Exec`, as
`ExecBacktrack.lean` does for the other matcher, and with both halves in
hand `matchers_agree` keeps only the premise that was always inherent:
neither run blew its budget. -/

/-- Whenever the lockstep run reports matched or no-match on an eligible
program, its answer is the specification's — found with the very ovector,
or not found — and the two layers agree on bad input. A budget refusal is
the one answer that claims nothing, so completion is not asserted here any
more than it is in `BtRunRefinesMatches`. -/
def PikeRunRefinesMatches : Prop :=
  ∀ (p : Pat) (s : ByteArray) (start : Nat) (mo : MOpts) (lim : Limits)
    (init : PikeSt),
    Wf p → s.size ≤ ceiling → (compile p).pike = true →
    RefinesMatches (pikeRun (compile p) s start mo lim init) p s start mo

/-- The whole scan, read against the specification. The loop enters on an
empty list with nothing on record, so what it answers is the merge of every
attempt the specification opens — and the scan from the first attempt is
`Spec.Matches` itself. -/
theorem pikeRun_loop_agrees {p : Pat} {s : ByteArray} {start : Nat}
    {mo : MOpts} {lim : Limits} {init : PikeSt} (hw : Wf p)
    (hpike : (compile p).pike = true) (hs : s.size ≤ ceiling)
    (hstart : start ≤ s.size) (setup words : Nat) :
    PikeAgrees p (some (Spec.Matches p s start mo))
      (pikeLoop (compile p) s mo lim start
        ((compile p).anchored || mo.anchored) words (s.size + 2) start
        { init with
          clist := #[], nlist := #[], stk := #[]
          pool := #[], rc := #[], free := #[]
          seen := Array.replicate (compile p).code.size false
          m := ⟨setup, setup, setup⟩ } none32 true false) := by
  have hscan : Spec.scan (Spec.suffFuel s.size p.root) p s mo start start
      (s.size + 1 - start) = some (Spec.Matches p s start mo) := by
    have hst := Spec.matches_stable p s start mo _ (Nat.le_refl _)
    have hcond : ¬ (decide (start > s.size) || decide (s.size > ceiling)) =
        true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
    rwa [Spec.matchesF, if_neg hcond] at hst
  exact pikeLoop_refine hw hpike hs hstart rfl
    (s.size + 2) start _ none32 false [] .nomatch
    (some (Spec.Matches p s start mo)) (some (Spec.Matches p s start mo))
    rfl rfl (by simp) (pikeRun_posOk (compile p) init setup).owned
    ⟨List.Forall₂.nil, by simp, by simp⟩ (Or.inl ⟨rfl, rfl, rfl⟩)
    (fun q hq => absurd ((replicate_false_get _ q).symm.trans hq) (by simp))
    (Nat.le_refl _) hstart
    (fun r hr => by subst hr; exact rfl)
    (fun _ _ => ⟨start, s.size + 1 - start, Nat.le_refl _,
      Or.inl ⟨rfl, fun hq => absurd hq.1 (by omega)⟩, hscan.symm⟩)
    (fun _ hq => absurd hq (by simp))

/-- The loop's answer, read off the end it reports. -/
theorem PikeAgrees.destruct {p : Pat} {top : Option Spec.MatchAnswer}
    {tr : PikeSt × Nat × PikeEnd} (h : PikeAgrees p top tr) :
    (tr.2.2 = .matched →
      top = some (.found (blockAt tr.1.pool (2 * (p.ncap + 1)) tr.2.1))) ∧
    (tr.2.2 = .noMatch → top = some .notFound) := by
  obtain ⟨st, mh, e⟩ := tr
  cases e
  · exact ⟨fun _ => h, fun hq => absurd hq (by simp)⟩
  · exact ⟨fun hq => absurd hq (by simp), fun _ => h⟩
  · exact ⟨fun hq => absurd hq (by simp), fun hq => absurd hq (by simp)⟩

/-- S-8's lockstep half. The position loop against the scan, and delivery:
what a match hands back is the block its handle names, which is the very
ovector `Spec.scan` computes. -/
theorem pikeRun_refines_matches : PikeRunRefinesMatches := by
  intro p s start mo lim init hw hs hpike
  have hmain :
      ((pikeRun (compile p) s start mo lim init).outcome = .matched →
        Spec.Matches p s start mo =
          .found (pikeRun (compile p) s start mo lim init).ovec) ∧
      ((pikeRun (compile p) s start mo lim init).outcome = .noMatch →
        Spec.Matches p s start mo = .notFound) := by
    by_cases hstart : start > s.size
    · rw [pikeRun, if_neg (by simp [hpike]), if_pos hstart]
      exact ⟨fun h => Outcome.noConfusion h, fun h => Outcome.noConfusion h⟩
    · have hstart' : start ≤ s.size := by omega
      have hagree := pikeRun_loop_agrees (init := init) (lim := lim)
        (mo := mo) hw hpike hs hstart'
        ((compile p).novec * regSize + ((compile p).code.size / 8 + 1))
        ((compile p).code.size / 8 + 1)
      rw [pikeRun, if_neg (by simp [hpike]), if_neg hstart]
      simp only []
      split
      · exact ⟨fun h => Outcome.noConfusion h, fun h => Outcome.noConfusion h⟩
      · split <;> rename_i hend <;> first
          | exact ⟨fun h => Outcome.noConfusion h,
              fun h => Outcome.noConfusion h⟩
          | exact ⟨fun h => Outcome.noConfusion h,
              fun _ => Option.some.inj (hagree.destruct.2 hend)⟩
          | (split
             · exact ⟨fun h => Outcome.noConfusion h,
                 fun h => Outcome.noConfusion h⟩
             · exact ⟨fun _ => Option.some.inj (hagree.destruct.1 hend),
                 fun h => Outcome.noConfusion h⟩)
  exact ⟨hmain.1, hmain.2, pikeRun_badInput_agrees hs hpike⟩

end Pcrevera.Refine
