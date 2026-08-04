import Pcrevera.Ref.VM
import Pcrevera.Spec.Total
import Pcrevera.Proofs.Meter
import Pcrevera.Proofs.CrFirst
import Batteries.Tactic.OpenPrivate
import Batteries.Data.List.Basic

/-!
# S-8, the backtracking half

The whole claim, proved here: whenever `btRun` completes a call — matched
or no-match, never resource-exceeded — its answer is `Spec.Matches`, the
trusted semantics, ovector included; and the two layers call an input bad
on exactly the same offsets. `btRun_refines_matches` is that theorem, and
`BtRunRefinesMatches` at the end of the file is its statement, read
against three hypotheses: the parser facts (`Wf`), the documented subject
cap, and the counter-wrap bound.

The development is a chain of four joints.

* **The mirror.** `eff` classifies what one instruction does — goto (with
  a register write folded in), fork, fail, or deliver — so the unmetered
  `run`/`dispatch`, their monotonicity and the frame laws
  (`runs_append`/`resumes_append`) case on four shapes instead of
  twenty-four opcodes, and `runs_eff` is the single one-step lemma every
  per-opcode fact reduces to. Every test in `eff` is copied from `btStep`
  verbatim; the metered bridge depends on that.

* **The reference enumeration.** The spec's threads carry only the
  ovector; the machine's carry the repetition counters above it. `denot`
  is `Spec.search` re-run on the full register file, with the counter
  writes the VM makes and repetition indices threaded compile-style;
  `denot_search` projects it back onto `Spec.search`, `denot_frame` says
  a node disturbs no counter but its own, and `denot_some` says it always
  answers at the sufficient fuel.

* **The fragment theorem.** `FragAt` records where a node's compiled form
  sits — one cell per leaf, the split/branch/jump chain, a group's save
  brackets, and the counted repetition's `repZero; repLoop; repEnter;
  body; repNext` block with the repetition row it runs on — and
  `frag_runs` says that running the mirror from a fragment's entry is
  queuing `denot`'s matches, retargeted at the fragment's exit, in front
  of the pending stack. The counted repetition is where the two number
  systems meet: the machine reads a `UInt32` count out of the register
  file where the enumeration carries a `Nat`, and the fuel bound is what
  keeps the two the same number and keeps a bounded high apart from the
  `none32` sentinel. `compileNode_facts` proves the compiler establishes
  the relation, under the append-only `Grows` discipline on all three
  tables.

* **The trail discipline and the metered bridge.** With register writes in
  play a backtrack entry decodes to the register file at push time:
  `snapAt` replays the trail above the entry's mark. Three lemmas carry
  it — a mark at the top replays nothing, a write-plus-undo pair cancels,
  and replay factors through any intermediate mark — and the `Sync`
  invariant packages them. `btStep_mirror` then says the metered machine,
  whenever it completes, does what the mirror does on the same fuel.

Above the per-attempt theorem (`attempt_refines`) the rest is
bookkeeping the two layers do in the same order: `btLoop_refines` walks
the attempt loop against `Spec.scan` — same starting positions, the same
bumpalong skips (`crFirst_agrees` closes that one), the same stop rule —
and `btRun_refines_matches` adds delivery and the two guards.

`Covered` is the shape predicate the compiler side runs on; `WfAst.covered`
derives it from the parser facts. Its one refusal is the empty
alternation, which the compiler treats like `nul` while `searchAlt []`
matches nothing, and which the engine's parser never emits.
-/

open private emit patch openRegion closeRegion dropEmptyRegion from
  Pcrevera.Ref.Compile

namespace Pcrevera.Refine

open Pcrevera Pcrevera.Ref

/-- A parked alternative: where to resume, and the thread to resume with.
Reusing the spec's `Thread` for the (pos, regs) half is what lets the
fragment theorem talk to `Spec.search`'s result lists without adapters. -/
abbrev Entry := Nat × Spec.Thread

/-- How a completed search ended. A found answer carries the accepted
thread with the two ovector slots already written, exactly as `btStep`'s
accept writes them. -/
inductive Out where
  | found (t : Spec.Thread)
  | nomatch

/-- What one instruction does, seen from the mirror: continue somewhere
(possibly with a register write folded in), fork a pending alternative,
fail into the stack, deliver, or fall outside the covered opcodes. The
whole point of this factoring is that the stack-algebra lemmas below need
only these five shapes, never the opcode. -/
inductive Eff where
  | goto (pc pos : Nat) (regs : Spec.Regs)
  | fork (pc alt : Nat)
  | fail
  | give (t : Spec.Thread)
  | stuck

/-- The dispatch of `btStep`, charge-free, one instruction's worth. Every
test is copied from `btStep` verbatim — the metered bridge depends on the
conditions being syntactically the same expressions. -/
def eff (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (pc pos : Nat) (regs : Spec.Regs) : Eff :=
  let n := s.size
  let inst := re.code[pc]!
  let step := fun (test : Bool) (len : Nat) =>
    if pos < n && test then Eff.goto (pc + 1) (pos + len) regs else .fail
  let holds := fun (test : Bool) =>
    if test then Eff.goto (pc + 1) pos regs else .fail
  match inst.op with
  | .chr => step (byteAt s pos == UInt8.ofNat inst.arg) 1
  | .chrCI => step (lowerByte (byteAt s pos) == UInt8.ofNat inst.arg) 1
  | .cls => step (pos < n && re.classHas inst.arg (byteAt s pos)) 1
  | .any => step true 1
  | .anyNoNL => step (newlineAt s pos re.nltype == 0) 1
  | .bsr =>
      let eaten := bsrAt s pos re.bsrtype
      if eaten != 0 then .goto (pc + 1) (pos + eaten) regs else .fail
  | .split => .fork inst.arg inst.alt
  | .jump => .goto inst.arg pos regs
  | .save => .goto (pc + 1) pos (regs.set! inst.arg pos.toUInt32)
  | .circ => holds (pos == 0 && !mo.notbol)
  | .circM =>
      holds (if pos == 0 then !mo.notbol
             else pos != n && newlineBefore s pos re.nltype != 0)
  | .doll => holds (!mo.noteol && atLineEnd s pos re.nltype)
  | .dollE => holds (!mo.noteol && pos == n)
  | .dollM =>
      holds (if pos < n then newlineAt s pos re.nltype != 0 else !mo.noteol)
  | .sod => holds (pos == 0)
  | .eod => holds (pos == n)
  | .eodn => holds (atLineEnd s pos re.nltype)
  | .wordB => holds (wordEdge s pos)
  | .notWordB => holds (!wordEdge s pos)
  | .repZero => .goto (pc + 1) pos (regs.set! (re.novec + inst.arg * 2) 0)
  | .repEnter =>
      .goto (pc + 1) pos
        (regs.set! (re.novec + inst.arg * 2 + 1) pos.toUInt32)
  | .repLoop =>
      let rep := re.reps[inst.arg]!
      let cnt := (regs[re.novec + inst.arg * 2]!).toNat
      if cnt < rep.lo then .goto rep.body pos regs
      else if cnt ≥ rep.hi then .goto rep.after pos regs
      else if rep.greedy then .fork rep.body rep.after
      else .fork rep.after rep.body
  | .repNext =>
      let rep := re.reps[inst.arg]!
      let slot := re.novec + inst.arg * 2
      let cnt := regs[slot]! + 1
      let entered := regs[slot + 1]!
      if rep.hi == none32 && pos.toUInt32 == entered && cnt.toNat ≥ rep.lo then
        .goto rep.after pos (regs.set! slot cnt)
      else .goto rep.head pos (regs.set! slot cnt)
  | .accept =>
      let empty := pos == attempt
      let refuse := empty &&
        (mo.notempty || (mo.notemptyAtStart && attempt == start))
      if refuse then .fail
      else .give ⟨pos, (regs.set! 0 attempt.toUInt32).set! 1 pos.toUInt32⟩

mutual

/-- The unmetered mirror of `btStep`, fuel-indexed: one `eff` per unit of
fuel, a fail popping the pending stack through `dispatch` on the same
fuel — the exact fuel hand-off of `btStep`/`btFail`. `none` is fuel
running out or an uncovered opcode. -/
def run (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat) :
    Nat → Nat → Nat → Spec.Regs → List Entry → Option Out
  | 0, _, _, _, _ => none
  | fuel + 1, pc, pos, regs, stk =>
      match eff re s mo start attempt pc pos regs with
      | .goto pc' pos' regs' => run re s mo start attempt fuel pc' pos' regs' stk
      | .fork pc' alt =>
          run re s mo start attempt fuel pc' pos regs ((alt, ⟨pos, regs⟩) :: stk)
      | .fail => dispatch re s mo start attempt fuel stk
      | .give t => some (.found t)
      | .stuck => none
termination_by fuel _ _ _ _ => (fuel, 0)

/-- Hand the next pending thread to `run`, or report the search over. -/
def dispatch (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (fuel : Nat) : List Entry → Option Out
  | [] => some .nomatch
  | (pc, t) :: stk => run re s mo start attempt fuel pc t.pos t.regs stk
termination_by _ => (fuel, 1)

end

/-- The mirror completes from this configuration with this answer. -/
def Runs (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (pc pos : Nat) (regs : Spec.Regs) (stk : List Entry) (r : Out) : Prop :=
  ∃ fuel, run re s mo start attempt fuel pc pos regs stk = some r

/-- Dispatching this pending list completes with this answer. -/
def Resumes (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (stk : List Entry) (r : Out) : Prop :=
  ∃ fuel, dispatch re s mo start attempt fuel stk = some r

section Mirror

variable {re : Re} {s : ByteArray} {mo : MOpts} {start attempt : Nat}

theorem run_mono :
    ∀ {fuel fuel' pc pos regs stk r}, fuel ≤ fuel' →
      run re s mo start attempt fuel pc pos regs stk = some r →
      run re s mo start attempt fuel' pc pos regs stk = some r := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; simp [run] at h
  | succ n ih =>
      intro fuel' pc pos regs stk r hle h
      obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
      rw [run] at h ⊢
      cases heff : eff re s mo start attempt pc pos regs <;>
        simp only [heff] at h ⊢
      case goto => exact ih (by omega) h
      case fork => exact ih (by omega) h
      case fail =>
          cases stk with
          | nil => simpa [dispatch] using h
          | cons top rest =>
              obtain ⟨q, t⟩ := top
              simp only [dispatch] at h ⊢
              exact ih (by omega) h
      all_goals exact h

theorem dispatch_mono {fuel fuel' : Nat} {stk : List Entry} {r : Out}
    (hle : fuel ≤ fuel')
    (h : dispatch re s mo start attempt fuel stk = some r) :
    dispatch re s mo start attempt fuel' stk = some r := by
  cases stk with
  | nil => simpa [dispatch] using h
  | cons top rest =>
      obtain ⟨q, t⟩ := top
      simp only [dispatch] at h ⊢
      exact run_mono hle h

theorem runs_det {pc pos : Nat} {regs : Spec.Regs} {stk : List Entry}
    {r r' : Out}
    (h : Runs re s mo start attempt pc pos regs stk r)
    (h' : Runs re s mo start attempt pc pos regs stk r') : r = r' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  have h1 := run_mono (Nat.le_max_left m m') hm
  have h2 := run_mono (Nat.le_max_right m m') hm'
  rw [h1] at h2
  exact Option.some.inj h2

theorem resumes_det {stk : List Entry} {r r' : Out}
    (h : Resumes re s mo start attempt stk r)
    (h' : Resumes re s mo start attempt stk r') : r = r' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  have h1 := dispatch_mono (Nat.le_max_left m m') hm
  have h2 := dispatch_mono (Nat.le_max_right m m') hm'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ### One step, read at the judgment level -/

theorem resumes_nil {r : Out} :
    Resumes re s mo start attempt [] r ↔ r = .nomatch := by
  constructor
  · rintro ⟨fuel, h⟩
    simpa [dispatch] using h.symm
  · rintro rfl
    exact ⟨0, by rw [dispatch]⟩

theorem resumes_cons {pc : Nat} {t : Spec.Thread} {stk : List Entry}
    {r : Out} :
    Resumes re s mo start attempt ((pc, t) :: stk) r ↔
      Runs re s mo start attempt pc t.pos t.regs stk r := by
  constructor
  · rintro ⟨fuel, h⟩
    rw [dispatch] at h
    exact ⟨fuel, h⟩
  · rintro ⟨fuel, h⟩
    refine ⟨fuel, ?_⟩
    rw [dispatch]
    exact h

/-- What each effect means as a judgment, given the configuration it fired
from. -/
def Eff.judg (re : Re) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (pos : Nat) (regs : Spec.Regs) (stk : List Entry) : Eff → Out → Prop
  | .goto pc' pos' regs', r => Runs re s mo start attempt pc' pos' regs' stk r
  | .fork pc' alt, r =>
      Runs re s mo start attempt pc' pos regs ((alt, ⟨pos, regs⟩) :: stk) r
  | .fail, r => Resumes re s mo start attempt stk r
  | .give t, r => r = .found t
  | .stuck, _ => False

/-- The single one-step lemma: a run means whatever its first effect
means. Every per-opcode fact downstream is this plus a computation of
`eff`. -/
theorem runs_eff {pc pos : Nat} {regs : Spec.Regs} {stk : List Entry}
    {r : Out} :
    Runs re s mo start attempt pc pos regs stk r ↔
      Eff.judg re s mo start attempt pos regs stk
        (eff re s mo start attempt pc pos regs) r := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
        rw [run] at h
        cases heff : eff re s mo start attempt pc pos regs <;>
          simp only [heff] at h <;> simp only [Eff.judg]
        case goto => exact ⟨n, h⟩
        case fork => exact ⟨n, h⟩
        case fail => exact ⟨n, h⟩
        case give => exact (Option.some.inj h).symm
        case stuck => cases h
  · intro h
    cases heff : eff re s mo start attempt pc pos regs <;>
      rw [heff] at h <;> simp only [Eff.judg] at h
    case goto pc' pos' regs' =>
        obtain ⟨fuel, h⟩ := h
        exact ⟨fuel + 1, by rw [run]; simp only [heff]; exact h⟩
    case fork pc' alt =>
        obtain ⟨fuel, h⟩ := h
        exact ⟨fuel + 1, by rw [run]; simp only [heff]; exact h⟩
    case fail =>
        obtain ⟨fuel, h⟩ := h
        exact ⟨fuel + 1, by rw [run]; simp only [heff]; exact h⟩
    case give t =>
        exact ⟨1, by rw [run]; simp only [heff]; rw [h]⟩

/-! ### The frame laws

The pending stack is the linearized search; what sits below a fragment's
own entries is only reachable once the fragment's search is over. These
two equivalences carry all of the spec's preference-order reasoning. -/

theorem run_extend_found :
    ∀ {fuel pc pos regs stk stk₂ t},
      run re s mo start attempt fuel pc pos regs stk = some (.found t) →
      run re s mo start attempt fuel pc pos regs (stk ++ stk₂) =
        some (.found t) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [run] at h
  | succ n ih =>
      intro pc pos regs stk stk₂ t h
      rw [run] at h ⊢
      cases heff : eff re s mo start attempt pc pos regs <;>
        simp only [heff] at h ⊢
      case goto => exact ih h
      case fork => exact ih (stk := _ :: stk) h
      case fail =>
          cases stk with
          | nil => simp [dispatch] at h
          | cons top rest =>
              obtain ⟨q, u⟩ := top
              simp only [dispatch, List.cons_append] at h ⊢
              exact ih h
      all_goals exact h

theorem run_extend_nomatch :
    ∀ {fuel₁ fuel₂ pc pos regs stk stk₂ r},
      run re s mo start attempt fuel₁ pc pos regs stk = some .nomatch →
      dispatch re s mo start attempt fuel₂ stk₂ = some r →
      run re s mo start attempt (fuel₁ + fuel₂) pc pos regs (stk ++ stk₂) =
        some r := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro _ _ _ _ _ _ _ h _; simp [run] at h
  | succ n ih =>
      intro fuel₂ pc pos regs stk stk₂ r h h₂
      have hsucc : n + 1 + fuel₂ = (n + fuel₂) + 1 := by omega
      rw [hsucc, run]
      rw [run] at h
      cases heff : eff re s mo start attempt pc pos regs <;>
        simp only [heff] at h ⊢
      case goto => exact ih h h₂
      case fork => exact ih (stk := _ :: stk) h h₂
      case fail =>
          cases stk with
          | nil =>
              simpa [List.nil_append] using
                dispatch_mono (Nat.le_add_left fuel₂ n) h₂
          | cons top rest =>
              obtain ⟨q, u⟩ := top
              simp only [dispatch, List.cons_append] at h ⊢
              exact ih h h₂
      case give => simp at h
      case stuck => simp at h

theorem run_frame :
    ∀ {fuel pc pos regs stk stk₂ r},
      run re s mo start attempt fuel pc pos regs (stk ++ stk₂) = some r →
      (∃ t, r = .found t ∧ Runs re s mo start attempt pc pos regs stk r) ∨
      (Runs re s mo start attempt pc pos regs stk .nomatch ∧
        Resumes re s mo start attempt stk₂ r) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [run] at h
  | succ n ih =>
      intro pc pos regs stk stk₂ r h
      rw [run] at h
      cases heff : eff re s mo start attempt pc pos regs <;>
        simp only [heff] at h
      case goto pc' pos' regs' =>
          rcases ih h with ⟨t, rfl, hr⟩ | ⟨hn, hres⟩
          · refine .inl ⟨t, rfl, ?_⟩
            rw [runs_eff, heff]
            exact hr
          · refine .inr ⟨?_, hres⟩
            rw [runs_eff, heff]
            exact hn
      case fork pc' alt =>
          rw [show ((alt, (⟨pos, regs⟩ : Spec.Thread)) :: (stk ++ stk₂)) =
            ((alt, (⟨pos, regs⟩ : Spec.Thread)) :: stk) ++ stk₂ from rfl] at h
          rcases ih h with ⟨t, rfl, hr⟩ | ⟨hn, hres⟩
          · refine .inl ⟨t, rfl, ?_⟩
            rw [runs_eff, heff]
            exact hr
          · refine .inr ⟨?_, hres⟩
            rw [runs_eff, heff]
            exact hn
      case fail =>
          cases stk with
          | nil =>
              refine .inr ⟨?_, ⟨n, by simpa [List.nil_append] using h⟩⟩
              rw [runs_eff, heff]
              exact resumes_nil.mpr rfl
          | cons top rest =>
              obtain ⟨q, u⟩ := top
              simp only [dispatch, List.cons_append] at h
              rcases ih h with ⟨t, rfl, hr⟩ | ⟨hn, hres⟩
              · refine .inl ⟨t, rfl, ?_⟩
                rw [runs_eff, heff]
                exact resumes_cons.mpr hr
              · refine .inr ⟨?_, hres⟩
                rw [runs_eff, heff]
                exact resumes_cons.mpr hn
      case give t =>
          obtain rfl := (Option.some.inj h).symm
          refine .inl ⟨t, rfl, ?_⟩
          rw [runs_eff, heff]
          rfl
      case stuck => cases h

/-- The frame law: a run over a composed stack either matches on the near
half alone, or drains it and resumes the far half. -/
theorem runs_append {pc pos : Nat} {regs : Spec.Regs}
    {stk stk₂ : List Entry} {r : Out} :
    Runs re s mo start attempt pc pos regs (stk ++ stk₂) r ↔
      (∃ t, r = .found t ∧ Runs re s mo start attempt pc pos regs stk r) ∨
      (Runs re s mo start attempt pc pos regs stk .nomatch ∧
        Resumes re s mo start attempt stk₂ r) := by
  constructor
  · rintro ⟨fuel, h⟩
    exact run_frame h
  · rintro (⟨t, rfl, ⟨fuel, h⟩⟩ | ⟨⟨fuel₁, h₁⟩, ⟨fuel₂, h₂⟩⟩)
    · exact ⟨fuel, run_extend_found h⟩
    · exact ⟨fuel₁ + fuel₂, run_extend_nomatch h₁ h₂⟩

theorem resumes_append {L₁ L₂ : List Entry} {r : Out} :
    Resumes re s mo start attempt (L₁ ++ L₂) r ↔
      (∃ t, r = .found t ∧ Resumes re s mo start attempt L₁ r) ∨
      (Resumes re s mo start attempt L₁ .nomatch ∧
        Resumes re s mo start attempt L₂ r) := by
  cases L₁ with
  | nil =>
      simp only [List.nil_append]
      constructor
      · intro h
        exact .inr ⟨resumes_nil.mpr rfl, h⟩
      · rintro (⟨t, rfl, hr⟩ | ⟨_, hr⟩)
        · cases resumes_nil.mp hr
        · exact hr
  | cons top rest =>
      obtain ⟨q, t⟩ := top
      simp only [List.cons_append, resumes_cons]
      exact runs_append

/-- Rewriting the far half of a pending list under a common near half. -/
theorem resumes_congr_tail {A L₁ L₂ : List Entry}
    (h : ∀ r, Resumes re s mo start attempt L₁ r ↔
      Resumes re s mo start attempt L₂ r) {r : Out} :
    Resumes re s mo start attempt (A ++ L₁) r ↔
      Resumes re s mo start attempt (A ++ L₂) r := by
  rw [resumes_append, resumes_append]
  exact or_congr Iff.rfl (and_congr Iff.rfl (h _))

/-- Swapping a whole pending stack for an equivalent one under a run. -/
theorem runs_congr_stack {pc pos : Nat} {regs : Spec.Regs}
    {L₁ L₂ : List Entry}
    (h : ∀ r, Resumes re s mo start attempt L₁ r ↔
      Resumes re s mo start attempt L₂ r) {r : Out} :
    Runs re s mo start attempt pc pos regs L₁ r ↔
      Runs re s mo start attempt pc pos regs L₂ r := by
  rw [← List.nil_append L₁, ← List.nil_append L₂, runs_append, runs_append]
  exact or_congr Iff.rfl (and_congr Iff.rfl (h _))

end Mirror

/-- Which opcode a bare assertion compiles to: the ten anchor-family
leaves, handled uniformly everywhere below. -/
def assnOp : Ast → Option Op
  | .circ => some .circ
  | .circM => some .circM
  | .doll => some .doll
  | .dollE => some .dollE
  | .dollM => some .dollM
  | .sod => some .sod
  | .eod => some .eod
  | .eodn => some .eodn
  | .wordB => some .wordB
  | .notWordB => some .notWordB
  | _ => none

/-! ## Wf: the parser facts the rest of S-8 stands on

Two recursive predicates and their conjunction over a pattern. Every
clause is a fact about the engine's parser, not an extra assumption on
top of it: an alternation always has at least one arm; quantifier bounds
are capped at 65535, far below the `none32` sentinel the compiled
repetition table would confuse an unbounded repetition with; and capture
numbers never exceed `maxGroup`, which is how `ncap` is defined, so every
save slot lands inside the ovector. `CapsBelow` is spelled as a clause
rather than derived from `Ast.maxGroup` to keep this round self-contained
— deriving it is a small foldl induction that can land later without
changing any statement here. -/

/-- The shape clauses: non-empty alternations, bounded quantifier highs.
`h < none32` matters because the compiler encodes `hi = none` as the
`none32` sentinel in the repetition table — a bounded repetition at or
past it would compile to the unbounded semantics, empty-match rule
included. The parser caps quantifiers at 65535. -/
def WfAst : Ast → Prop
  | .cat kids => kids.attach.foldr (fun ⟨k, _⟩ acc => WfAst k ∧ acc) True
  | .alt arms =>
      arms ≠ [] ∧
        arms.attach.foldr (fun ⟨a, _⟩ acc => WfAst a ∧ acc) True
  | .grp _ body => WfAst body
  | .rep _ hi _ body =>
      (∀ h, hi = some h → h < none32) ∧ WfAst body
  | _ => True

/-- Every capturing group's save slots sit inside the first `novec`
registers. The parser numbers groups densely up to `ncap`, so with
`novec = 2 * (ncap + 1)` this is `Ast.maxGroup`'s defining property. -/
def CapsBelow (novec : Nat) : Ast → Prop
  | .cat kids =>
      kids.attach.foldr (fun ⟨k, _⟩ acc => CapsBelow novec k ∧ acc) True
  | .alt arms =>
      arms.attach.foldr (fun ⟨a, _⟩ acc => CapsBelow novec a ∧ acc) True
  | .grp cap body =>
      (cap ≠ 0 → 2 * cap + 1 < novec) ∧ CapsBelow novec body
  | .rep _ _ _ body => CapsBelow novec body
  | _ => True

/-- The whole-pattern well-formedness the full S-8 will assume. -/
def Wf (p : Pat) : Prop :=
  WfAst p.root ∧ CapsBelow (2 * (p.ncap + 1)) p.root

private theorem attach_foldr_forall {α : Type _} {P : α → Prop} :
    ∀ {l : List α},
      l.attach.foldr (fun x acc => P x.1 ∧ acc) True → ∀ x ∈ l, P x := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons y ys ih =>
      intro h x hx
      simp only [List.attach_cons, List.foldr_cons, List.foldr_map] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact ih h.2 x hx'

/-- `WfAst` implies the `NoEmptyAlt` shape `crFirst_agrees` asks for, so
the bumpalong analysis composes with `Wf` directly. -/
theorem WfAst.noEmptyAlt : ∀ {a : Ast}, WfAst a → CrFirst.NoEmptyAlt a
  | .cat kids, h => by
      rw [WfAst] at h
      rw [CrFirst.NoEmptyAlt]
      intro k hk
      have := List.sizeOf_lt_of_mem hk
      exact WfAst.noEmptyAlt (attach_foldr_forall h k hk)
  | .alt arms, h => by
      rw [WfAst] at h
      rw [CrFirst.NoEmptyAlt]
      refine ⟨h.1, ?_⟩
      intro a ha
      have := List.sizeOf_lt_of_mem ha
      exact WfAst.noEmptyAlt (attach_foldr_forall h.2 a ha)
  | .grp cap body, h => by
      rw [WfAst] at h
      rw [CrFirst.NoEmptyAlt]
      exact WfAst.noEmptyAlt h
  | .rep lo hi greedy body, h => by
      rw [WfAst] at h
      rw [CrFirst.NoEmptyAlt]
      exact WfAst.noEmptyAlt h.2
  | .nul, _ | .chr _, _ | .chrCI _, _ | .cls _, _ | .any, _ | .anyNoNL, _
  | .bsr, _ | .circ, _ | .circM, _ | .doll, _ | .dollE, _ | .dollM, _
  | .sod, _ | .eod, _ | .eodn, _ | .wordB, _ | .notWordB, _ => by
      rw [CrFirst.NoEmptyAlt] <;> simp
termination_by a _ => sizeOf a
decreasing_by
  all_goals simp
  all_goals omega

/-! ## The full-register reference enumeration

The spec's threads carry only the ovector; the machine's carry the
repetition counters above it. `denot` is `Spec.search` re-run on the full
register file: same branching — the search never reads a register, so
the two take the same branches on the same fuel — with the counter
writes added exactly where the VM makes them: count zeroed at loop
entry, entry position saved before each round, count bumped after each
round, all at `novec + 2r` and `novec + 2r + 1`. Repetition indices are
threaded structurally the way the compiler assigns them, left to right;
`repCount` is a node's share. The projection theorem `denot_search`
below ties `denot` back to `Spec.search`: same positions, agreeing
ovectors — the counter writes are invisible below `novec`. -/

/-- How many repetition-table entries a node compiles to: none for
`{0,0}`, the body's own for the split-compiled `hi = 1` forms, one plus
the body's for the general block. -/
def repCount : Ast → Nat
  | .cat kids => kids.attach.foldl (fun acc ⟨k, _⟩ => acc + repCount k) 0
  | .alt arms => arms.attach.foldl (fun acc ⟨a, _⟩ => acc + repCount a) 0
  | .grp _ body => repCount body
  | .rep _ hi _ body =>
      match hi with
      | some 0 => 0
      | some 1 => repCount body
      | _ => 1 + repCount body
  | _ => 0

/-- Peeling an accumulator off a left fold that only ever adds. -/
private theorem foldl_add_start {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (acc : Nat),
      l.foldl (fun a x => a + f x) acc =
        acc + l.foldl (fun a x => a + f x) 0 := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (acc + f x), ih (0 + f x)]
      omega

theorem repCount_cat_nil : repCount (.cat []) = 0 := by rw [repCount]; simp

theorem repCount_alt_nil : repCount (.alt []) = 0 := by rw [repCount]; simp

/-- A list's repetition rows, one child at a time — which is how both the
compiler and the fragment relation hand out indices. -/
theorem repCount_cat_cons (k : Ast) (kids : List Ast) :
    repCount (.cat (k :: kids)) = repCount k + repCount (.cat kids) := by
  rw [repCount, repCount]
  simp only [List.attach_cons, List.foldl_cons, List.foldl_map]
  rw [foldl_add_start (fun x : { y // y ∈ kids } => repCount x.1) _ (0 + repCount k),
    foldl_add_start (fun x : { y // y ∈ kids } => repCount x.1) _ 0]
  omega

theorem repCount_alt_cons (a : Ast) (arms : List Ast) :
    repCount (.alt (a :: arms)) = repCount a + repCount (.alt arms) := by
  rw [repCount, repCount]
  simp only [List.attach_cons, List.foldl_cons, List.foldl_map]
  rw [foldl_add_start (fun x : { y // y ∈ arms } => repCount x.1) _ (0 + repCount a),
    foldl_add_start (fun x : { y // y ∈ arms } => repCount x.1) _ 0]
  omega

mutual

/-- `Spec.search` on the full register file, counter writes included. -/
def denot (fuel : Nat) (c : Spec.SCtx) (novec r0 : Nat) (a : Ast)
    (pos : Nat) (regs : Spec.Regs) : Option (List Spec.Thread) :=
  let n := c.s.size
  match a with
  | .nul => some [⟨pos, regs⟩]
  | .chr b =>
      some (if pos < n && byteAt c.s pos == b then [⟨pos + 1, regs⟩] else [])
  | .chrCI folded =>
      some (if pos < n && lowerByte (byteAt c.s pos) == folded
            then [⟨pos + 1, regs⟩] else [])
  | .cls bits =>
      some (if pos < n && bits.has (byteAt c.s pos) then [⟨pos + 1, regs⟩]
            else [])
  | .any => some (if pos < n then [⟨pos + 1, regs⟩] else [])
  | .anyNoNL =>
      some (if pos < n && newlineAt c.s pos c.nl == 0 then [⟨pos + 1, regs⟩]
            else [])
  | .bsr =>
      let eaten := bsrAt c.s pos c.bsr
      some (if eaten != 0 then [⟨pos + eaten, regs⟩] else [])
  | .cat kids => denotCat fuel c novec r0 kids pos regs
  | .alt arms => denotAlt fuel c novec r0 arms pos regs
  | .grp cap body =>
      let opened := if cap != 0 then regs.set! (2 * cap) pos.toUInt32 else regs
      (denot fuel c novec r0 body pos opened).map
        (List.map fun t =>
          if cap != 0 then ⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩
          else t)
  | .rep lo hi greedy body =>
      match hi with
      | some 0 => some [⟨pos, regs⟩]
      | some 1 =>
          if lo == 1 then denot fuel c novec r0 body pos regs
          else
            (denot fuel c novec r0 body pos regs).map fun taken =>
              if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken
      | _ =>
          denotRep fuel c novec (novec + 2 * r0) (r0 + 1) body lo hi greedy
            0 pos (regs.set! (novec + 2 * r0) 0)
  | a => some (if Spec.assertionHolds c a pos then [⟨pos, regs⟩] else [])
termination_by (fuel, sizeOf a)

def denotCat (fuel : Nat) (c : Spec.SCtx) (novec r0 : Nat)
    (kids : List Ast) (pos : Nat) (regs : Spec.Regs) :
    Option (List Spec.Thread) :=
  match kids with
  | [] => some [⟨pos, regs⟩]
  | k :: rest => do
      let heads ← denot fuel c novec r0 k pos regs
      let tails ← heads.mapM fun t =>
        denotCat fuel c novec (r0 + repCount k) rest t.pos t.regs
      pure tails.flatten
termination_by (fuel, sizeOf kids)

def denotAlt (fuel : Nat) (c : Spec.SCtx) (novec r0 : Nat)
    (arms : List Ast) (pos : Nat) (regs : Spec.Regs) :
    Option (List Spec.Thread) :=
  match arms with
  | [] => some []
  | arm :: rest => do
      let mine ← denot fuel c novec r0 arm pos regs
      let theirs ← denotAlt fuel c novec (r0 + repCount arm) rest pos regs
      pure (mine ++ theirs)
termination_by (fuel, sizeOf arms)

/-- One counted round, `Spec.searchRep` with the counter writes: entry
position saved before the body, count bumped after it, both at the
loop's own slots. `r0` is where the body's inner repetitions start. -/
def denotRep (fuel : Nat) (c : Spec.SCtx) (novec slot r0 : Nat)
    (body : Ast) (lo : Nat) (hi : Option Nat) (greedy : Bool)
    (cnt pos : Nat) (regs : Spec.Regs) : Option (List Spec.Thread) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let enter : Option (List Spec.Thread) := do
        let taken ← denot fuel c novec r0 body pos
          (regs.set! (slot + 1) pos.toUInt32)
        let onward ← taken.mapM fun t =>
          let bumped := t.regs.set! slot (cnt + 1).toUInt32
          if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
            pure [(⟨t.pos, bumped⟩ : Spec.Thread)]
          else
            denotRep fuel c novec slot r0 body lo hi greedy (cnt + 1)
              t.pos bumped
        pure onward.flatten
      if cnt < lo then enter
      else if hi.any (cnt ≥ ·) then some [⟨pos, regs⟩]
      else do
        let taken ← enter
        pure (if greedy then taken ++ [⟨pos, regs⟩] else ⟨pos, regs⟩ :: taken)
termination_by (fuel, 1 + sizeOf body)

end

/-- The assertion family compiles to a single cell and claims no
repetition row. -/
theorem repCount_assn {a : Ast} {op : Op} (h : assnOp a = some op) :
    repCount a = 0 := by
  cases a <;> simp only [assnOp] at h <;> try cases h
  all_goals simp [repCount]

/-- A concatenation is its list, read at the node level. -/
theorem denot_cat {c : Spec.SCtx} (fuel novec r0 : Nat) (kids : List Ast)
    (pos : Nat) (regs : Spec.Regs) :
    denot fuel c novec r0 (.cat kids) pos regs =
      denotCat fuel c novec r0 kids pos regs := by
  rw [denot.eq_def]

/-- An alternation is its list, read at the node level. -/
theorem denot_alt {c : Spec.SCtx} (fuel novec r0 : Nat) (arms : List Ast)
    (pos : Nat) (regs : Spec.Regs) :
    denot fuel c novec r0 (.alt arms) pos regs =
      denotAlt fuel c novec r0 arms pos regs := by
  rw [denot.eq_def]

/-- The assertion family's enumeration, computed once for all ten. -/
theorem denot_assn {c : Spec.SCtx} {a : Ast} {op : Op}
    (h : assnOp a = some op) (fuel novec r0 pos : Nat) (regs : Spec.Regs) :
    denot fuel c novec r0 a pos regs =
      some (if Spec.assertionHolds c a pos then [⟨pos, regs⟩] else []) := by
  cases a <;> simp only [assnOp] at h <;> try cases h
  all_goals rw [denot] <;> simp

/-! ## The ovector projection

Agreement below `novec` is all the spec ever sees of a register file.
Two writes keep it: the same value to the same slot on both sides, and
anything at or above `novec` on the full side only — which is every
counter write. No well-formedness enters: a save slot at or past
`novec` would disagree only above the window the relation looks at. -/

/-- The two files agree on the ovector window. The size bounds make the
window in-bounds on both sides, so a same-slot write inside it lands on
both. -/
def Agree (novec : Nat) (u v : Spec.Regs) : Prop :=
  novec ≤ u.size ∧ novec ≤ v.size ∧ ∀ i, i < novec → u[i]! = v[i]!

/-- Threads with the same end and agreeing ovectors. -/
def TAgree (novec : Nat) (tF tO : Spec.Thread) : Prop :=
  tF.pos = tO.pos ∧ Agree novec tF.regs tO.regs

private theorem getBang_set_ne {α : Type _} [Inhabited α] (u : Array α)
    (s : Nat) {x : α} {i : Nat} (h : i ≠ s) :
    (u.setIfInBounds s x)[i]! = u[i]! := by
  by_cases hi : i < u.size
  · rw [getElem!_pos (u.setIfInBounds s x) i (by simpa using hi),
      getElem!_pos u i hi]
    exact Array.getElem_setIfInBounds_ne hi (Ne.symm h)
  · rw [getElem!_neg (u.setIfInBounds s x) i (by simpa using hi),
      getElem!_neg u i hi]

private theorem getBang_set_eq {α : Type _} [Inhabited α] (u : Array α)
    {s : Nat} (h : s < u.size) {x : α} :
    (u.setIfInBounds s x)[s]! = x := by
  rw [getElem!_pos (u.setIfInBounds s x) s (by simpa using h)]
  exact Array.getElem_setIfInBounds_self (by simpa using h)

theorem Agree.set_both {novec : Nat} {u v : Spec.Regs}
    (h : Agree novec u v) (s : Nat) (x : UInt32) :
    Agree novec (u.set! s x) (v.set! s x) := by
  obtain ⟨hu, hv, hag⟩ := h
  simp only [Array.set!_eq_setIfInBounds]
  refine ⟨by simpa using hu, by simpa using hv, ?_⟩
  intro i hi
  by_cases hs : i = s
  · subst hs
    rw [getBang_set_eq u (by omega), getBang_set_eq v (by omega)]
  · rw [getBang_set_ne u s hs, getBang_set_ne v s hs]
    exact hag i hi

theorem Agree.set_high {novec : Nat} {u v : Spec.Regs}
    (h : Agree novec u v) {s : Nat} (hs : novec ≤ s) (x : UInt32) :
    Agree novec (u.set! s x) v := by
  obtain ⟨hu, hv, hag⟩ := h
  simp only [Array.set!_eq_setIfInBounds]
  refine ⟨by simpa using hu, hv, ?_⟩
  intro i hi
  rw [getBang_set_ne u s (by omega)]
  exact hag i hi

/-- Related lists append to related lists. -/
theorem forall₂_append {β : Type} {S : β → β → Prop} :
    ∀ {l₁ l₂ l₁' l₂' : List β}, List.Forall₂ S l₁ l₁' →
    List.Forall₂ S l₂ l₂' → List.Forall₂ S (l₁ ++ l₂) (l₁' ++ l₂') := by
  intro l₁ l₂ l₁' l₂' h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | cons hx _ ih => exact .cons hx ih

/-- Related lists map to related lists, under a pointwise transformer. -/
theorem forall₂_map {β : Type} {S T : β → β → Prop} {f g : β → β}
    (hfg : ∀ x y, S x y → T (f x) (g y)) :
    ∀ {l l' : List β}, List.Forall₂ S l l' →
    List.Forall₂ T (l.map f) (l'.map g) := by
  intro l l' h
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hfg _ _ hx) ih

private theorem bind_some {α β : Type} {o : Option α} {f : α → Option β}
    {b : β} (h : o.bind f = some b) : ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- Pairing a `mapM` on related inputs with related element answers. -/
theorem mapM_rel {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    {f g : α → Option (List β)}
    (hfg : ∀ x y, R x y → ∀ zs, f x = some zs →
      ∃ zs', g y = some zs' ∧ List.Forall₂ S zs zs') :
    ∀ {l l' : List α}, List.Forall₂ R l l' →
    ∀ {os : List (List β)}, l.mapM f = some os →
    ∃ os', l'.mapM g = some os' ∧
      List.Forall₂ (List.Forall₂ S) os os' := by
  intro l l' hrel
  induction hrel with
  | nil =>
      intro os h
      cases h
      exact ⟨[], rfl, .nil⟩
  | @cons x y xs ys hxy hrest ih =>
      intro os h
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => rw [hx] at h; cases h
      | some zs =>
          rw [hx] at h
          cases hxs : xs.mapM f with
          | none => rw [hxs] at h; cases h
          | some oss =>
              rw [hxs] at h
              cases h
              obtain ⟨zs', hy, hzs⟩ := hfg x y hxy zs hx
              obtain ⟨os', hys, hoss⟩ := ih hxs
              refine ⟨zs' :: os', ?_, .cons hzs hoss⟩
              rw [List.mapM_cons, hy, hys]
              rfl

/-- Related lists of lists flatten to related lists. -/
theorem Forall₂.flatten {β : Type} {S : β → β → Prop} :
    ∀ {os os' : List (List β)}, List.Forall₂ (List.Forall₂ S) os os' →
    List.Forall₂ S os.flatten os'.flatten := by
  intro os os' h
  induction h with
  | nil => exact .nil
  | cons hzs _ ih =>
      rw [List.flatten_cons, List.flatten_cons]
      exact forall₂_append hzs ih

section Projection

variable {c : Spec.SCtx} {novec : Nat}

mutual

/-- The projection: whatever `denot` answers, `Spec.search` answers the
same skeleton from any ovector-agreeing file — same length, same
positions, agreeing ovectors, on the same fuel. The two never read a
register, so they take the same branches; only the write bookkeeping
differs, and the counter writes fall outside the window. -/
theorem denot_search : ∀ {fuel r0 : Nat} {a : Ast} {pos : Nat}
    {regsF regsO : Spec.Regs} {tsF : List Spec.Thread},
    denot fuel c novec r0 a pos regsF = some tsF →
    Agree novec regsF regsO →
    ∃ tsO, Spec.search fuel c a pos regsO = some tsO ∧
      List.Forall₂ (TAgree novec) tsF tsO := by
  intro fuel r0 a pos regsF regsO tsF h hag
  match a with
  | .cat kids =>
      rw [denot.eq_def] at h
      rw [Spec.search.eq_def]
      exact denotCat_search h hag
  | .alt arms =>
      rw [denot.eq_def] at h
      rw [Spec.search.eq_def]
      exact denotAlt_search h hag
  | .grp cap body =>
      rw [denot.eq_def] at h
      rw [Spec.search.eq_def]
      simp only [Option.map_eq_some_iff] at h ⊢
      by_cases hcap : (cap != 0) = true
      all_goals simp only [hcap, Bool.false_eq_true, if_true, if_false] at h ⊢
      · obtain ⟨taken, htaken, rfl⟩ := h
        obtain ⟨takenO, htakenO, hrel⟩ :=
          denot_search htaken (hag.set_both (2 * cap) pos.toUInt32)
        refine ⟨_, ⟨takenO, htakenO, rfl⟩, ?_⟩
        refine forall₂_map (fun x y hxy => ?_) hrel
        exact ⟨hxy.1, hxy.1 ▸ hxy.2.set_both (2 * cap + 1) x.pos.toUInt32⟩
      · obtain ⟨taken, htaken, rfl⟩ := h
        obtain ⟨takenO, htakenO, hrel⟩ := denot_search htaken hag
        refine ⟨_, ⟨takenO, htakenO, rfl⟩, ?_⟩
        simpa using hrel
  | .rep lo hi greedy body =>
      rw [denot.eq_def] at h
      rw [Spec.search.eq_def]
      match hi with
      | some 0 =>
          cases h
          exact ⟨_, rfl, .cons ⟨rfl, hag⟩ .nil⟩
      | some 1 =>
          simp only [] at h ⊢
          split at h <;> rename_i hlo
          · rw [if_pos hlo]
            exact denot_search h hag
          · rw [if_neg hlo]
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨taken, htaken, rfl⟩ := h
            obtain ⟨takenO, htakenO, hrel⟩ := denot_search htaken hag
            refine ⟨(if greedy then takenO ++ [⟨pos, regsO⟩]
              else ⟨pos, regsO⟩ :: takenO), ?_, ?_⟩
            · rw [htakenO]
              rfl
            · by_cases hg : greedy = true
              all_goals simp only [hg, Bool.false_eq_true, if_true, if_false]
              · exact forall₂_append hrel (.cons ⟨rfl, hag⟩ .nil)
              · exact .cons ⟨rfl, hag⟩ hrel
      | none =>
          exact denotRep_search (Nat.le_add_right _ _) h
            (hag.set_high (Nat.le_add_right _ _) 0)
      | some (_ + 2) =>
          exact denotRep_search (Nat.le_add_right _ _) h
            (hag.set_high (Nat.le_add_right _ _) 0)
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [denot.eq_def] at h
      rw [Spec.search.eq_def]
      cases h
      refine ⟨_, rfl, ?_⟩
      try split
      all_goals first
        | exact .cons ⟨rfl, hag⟩ .nil
        | exact .nil
termination_by fuel _ a => (fuel, sizeOf a)

theorem denotCat_search : ∀ {fuel r0 : Nat} {kids : List Ast} {pos : Nat}
    {regsF regsO : Spec.Regs} {tsF : List Spec.Thread},
    denotCat fuel c novec r0 kids pos regsF = some tsF →
    Agree novec regsF regsO →
    ∃ tsO, Spec.searchCat fuel c kids pos regsO = some tsO ∧
      List.Forall₂ (TAgree novec) tsF tsO := by
  intro fuel r0 kids pos regsF regsO tsF h hag
  match kids with
  | [] =>
      rw [denotCat.eq_def] at h
      rw [Spec.searchCat.eq_def]
      cases h
      exact ⟨_, rfl, .cons ⟨rfl, hag⟩ .nil⟩
  | k :: rest =>
      rw [denotCat.eq_def] at h
      rw [Spec.searchCat.eq_def]
      simp only [Option.pure_def, Option.bind_eq_bind] at h ⊢
      obtain ⟨heads, hheads, h⟩ := bind_some h
      obtain ⟨tails, htails, h⟩ := bind_some h
      cases h
      obtain ⟨headsO, hheadsO, hrelh⟩ := denot_search hheads hag
      obtain ⟨tailsO, htailsO, hrelt⟩ :=
        mapM_rel (S := TAgree novec)
          (fun x y hxy zs hzs => hxy.1 ▸ denotCat_search hzs hxy.2)
          hrelh htails
      refine ⟨tailsO.flatten, ?_, Forall₂.flatten hrelt⟩
      rw [hheadsO]
      simp only [Option.bind]
      rw [htailsO]
termination_by fuel _ kids => (fuel, sizeOf kids)

theorem denotAlt_search : ∀ {fuel r0 : Nat} {arms : List Ast} {pos : Nat}
    {regsF regsO : Spec.Regs} {tsF : List Spec.Thread},
    denotAlt fuel c novec r0 arms pos regsF = some tsF →
    Agree novec regsF regsO →
    ∃ tsO, Spec.searchAlt fuel c arms pos regsO = some tsO ∧
      List.Forall₂ (TAgree novec) tsF tsO := by
  intro fuel r0 arms pos regsF regsO tsF h hag
  match arms with
  | [] =>
      rw [denotAlt.eq_def] at h
      rw [Spec.searchAlt.eq_def]
      cases h
      exact ⟨_, rfl, .nil⟩
  | arm :: rest =>
      rw [denotAlt.eq_def] at h
      rw [Spec.searchAlt.eq_def]
      simp only [Option.pure_def, Option.bind_eq_bind] at h ⊢
      obtain ⟨mine, hmine, h⟩ := bind_some h
      obtain ⟨theirs, htheirs, h⟩ := bind_some h
      cases h
      obtain ⟨mineO, hmineO, hrelm⟩ := denot_search hmine hag
      obtain ⟨theirsO, htheirsO, hrelr⟩ := denotAlt_search htheirs hag
      refine ⟨mineO ++ theirsO, ?_, forall₂_append hrelm hrelr⟩
      rw [hmineO]
      simp only [Option.bind]
      rw [htheirsO]
termination_by fuel _ arms => (fuel, sizeOf arms)

theorem denotRep_search : ∀ {fuel slot r0 : Nat} {body : Ast} {lo : Nat}
    {hi : Option Nat} {greedy : Bool} {cnt pos : Nat}
    {regsF regsO : Spec.Regs} {tsF : List Spec.Thread},
    novec ≤ slot →
    denotRep fuel c novec slot r0 body lo hi greedy cnt pos regsF =
      some tsF →
    Agree novec regsF regsO →
    ∃ tsO, Spec.searchRep fuel c body lo hi greedy cnt pos regsO =
      some tsO ∧ List.Forall₂ (TAgree novec) tsF tsO := by
  intro fuel slot r0 body lo hi greedy cnt pos regsF regsO tsF hslot h hag
  match fuel with
  | 0 =>
      rw [denotRep.eq_def] at h
      cases h
  | fuel + 1 =>
      rw [denotRep.eq_def] at h
      rw [Spec.searchRep.eq_def]
      simp only [Option.pure_def, Option.bind_eq_bind] at h ⊢
      have henter : ∀ {taken : List Spec.Thread}
          {onward : List (List Spec.Thread)},
          denot fuel c novec r0 body pos
            (regsF.set! (slot + 1) pos.toUInt32) = some taken →
          taken.mapM (fun t =>
            if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
              some [(⟨t.pos, t.regs.set! slot (cnt + 1).toUInt32⟩ :
                Spec.Thread)]
            else
              denotRep fuel c novec slot r0 body lo hi greedy (cnt + 1)
                t.pos (t.regs.set! slot (cnt + 1).toUInt32)) = some onward →
          ∃ takenO onwardO,
            Spec.search fuel c body pos regsO = some takenO ∧
            takenO.mapM (fun t =>
              if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                some [t]
              else
                Spec.searchRep fuel c body lo hi greedy (cnt + 1)
                  t.pos t.regs) = some onwardO ∧
            List.Forall₂ (List.Forall₂ (TAgree novec)) onward onwardO := by
        intro taken onward htaken honward
        obtain ⟨takenO, htakenO, hrelt⟩ := denot_search htaken
          (hag.set_high (by omega) pos.toUInt32)
        obtain ⟨onwardO, honwardO, hrelo⟩ :=
          mapM_rel (S := TAgree novec)
            (g := fun t =>
              if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then some [t]
              else Spec.searchRep fuel c body lo hi greedy (cnt + 1)
                t.pos t.regs)
            (fun x y hxy zs hzs => by
              rw [← hxy.1]
              split at hzs <;> rename_i hcase
              · rw [if_pos hcase]
                cases hzs
                exact ⟨[y], rfl,
                  .cons ⟨hxy.1, hxy.2.set_high hslot _⟩ .nil⟩
              · rw [if_neg hcase]
                exact denotRep_search hslot hzs (hxy.2.set_high hslot _))
            hrelt honward
        exact ⟨takenO, onwardO, htakenO, honwardO, hrelo⟩
      by_cases hcl : cnt < lo
      · rw [if_pos hcl] at h ⊢
        obtain ⟨taken, htaken, h⟩ := bind_some h
        obtain ⟨onward, honward, h⟩ := bind_some h
        cases h
        obtain ⟨takenO, onwardO, htakenO, honwardO, hrelo⟩ :=
          henter htaken honward
        refine ⟨onwardO.flatten, ?_, Forall₂.flatten hrelo⟩
        rw [htakenO]
        simp only [Option.bind]
        rw [honwardO]
      · rw [if_neg hcl] at h ⊢
        by_cases hhi : hi.any (cnt ≥ ·) = true
        · rw [if_pos hhi] at h ⊢
          cases h
          exact ⟨_, rfl, .cons ⟨rfl, hag⟩ .nil⟩
        · rw [if_neg hhi] at h ⊢
          obtain ⟨takenAll, hAll, h⟩ := bind_some h
          cases h
          obtain ⟨taken, htaken, hAll⟩ := bind_some hAll
          obtain ⟨onward, honward, hAll⟩ := bind_some hAll
          cases hAll
          obtain ⟨takenO, onwardO, htakenO, honwardO, hrelo⟩ :=
            henter htaken honward
          refine ⟨(if greedy then onwardO.flatten ++ [⟨pos, regsO⟩]
            else ⟨pos, regsO⟩ :: onwardO.flatten), ?_, ?_⟩
          · rw [htakenO]
            simp only [Option.bind]
            rw [honwardO]
          · by_cases hg : greedy = true
            all_goals simp only [hg, Bool.false_eq_true, if_true, if_false]
            · exact forall₂_append (Forall₂.flatten hrelo)
                (.cons ⟨rfl, hag⟩ .nil)
            · exact .cons ⟨rfl, hag⟩ (Forall₂.flatten hrelo)
termination_by fuel _ _ body => (fuel, 1 + sizeOf body)

end

end Projection

/-! ## Frame: the registers the enumeration leaves alone

`denot` writes in exactly three places: a group's two save slots, which
`CapsBelow` puts below `novec`; the count it zeroes when it enters a
repetition; and, inside `denotRep`, the entry position and the bumped
count. The first is invisible to anyone reading counters, and the last
three all land inside the window the node's own repetition indices own.
So a thread that comes back from `denot` carries the register file it was
handed everywhere outside that window — and it carries a file of the same
size, since `Array.set!` on a stray index is a no-op rather than a grow.

That is what the fragment relation needs on the machine side: the
compiled block for a node touches no counter that belongs to a sibling,
so the pieces of a concatenation or an alternation can be reasoned about
one at a time. -/

/-- A concatenation's capture bound, one child at a time. -/
theorem capsBelow_cat_cons {novec : Nat} {k : Ast} {kids : List Ast} :
    CapsBelow novec (.cat (k :: kids)) ↔
      CapsBelow novec k ∧ CapsBelow novec (.cat kids) := by
  rw [CapsBelow, CapsBelow]
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map]

/-- An alternation's capture bound, one arm at a time. -/
theorem capsBelow_alt_cons {novec : Nat} {a : Ast} {arms : List Ast} :
    CapsBelow novec (.alt (a :: arms)) ↔
      CapsBelow novec a ∧ CapsBelow novec (.alt arms) := by
  rw [CapsBelow, CapsBelow]
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map]


mutual

/-- The frame: a thread `denot` hands back carries a register file of the
same size as the one it was given, and one that differs only inside the
window `novec + 2 * r0 .. novec + 2 * (r0 + repCount a)` — the node's own
repetition rows. Nothing is claimed below `novec`, which is where the
group writes go. -/
theorem denot_frame {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel r0 : Nat} {a : Ast} {pos : Nat} {regs : Spec.Regs}
      {ts : List Spec.Thread},
    denot fuel c novec r0 a pos regs = some ts → CapsBelow novec a →
    ∀ t ∈ ts, t.regs.size = regs.size ∧
      ∀ i, novec ≤ i →
        (i < novec + 2 * r0 ∨ novec + 2 * (r0 + repCount a) ≤ i) →
        t.regs[i]! = regs[i]! := by
  intro fuel r0 a pos regs ts h hcap
  match a with
  | .cat kids =>
      rw [denot.eq_def] at h
      exact denotCat_frame h hcap
  | .alt arms =>
      rw [denot.eq_def] at h
      exact denotAlt_frame h hcap
  | .grp cap body =>
      rw [denot.eq_def] at h
      rw [CapsBelow] at hcap
      simp only [Option.map_eq_some_iff] at h
      by_cases hc : (cap != 0) = true
      · simp only [hc, if_true] at h
        obtain ⟨taken, htaken, rfl⟩ := h
        have hlt : 2 * cap + 1 < novec := hcap.1 (by simpa using hc)
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        obtain ⟨hsz, hreg⟩ := denot_frame htaken hcap.2 u hu
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
          at hsz hreg ⊢
        refine ⟨hsz, ?_⟩
        intro i hi hw
        simp only [repCount] at hw
        rw [getBang_set_ne u.regs (2 * cap + 1) (by omega), hreg i hi hw,
          getBang_set_ne regs (2 * cap) (by omega)]
      · simp only [hc, Bool.false_eq_true, if_false] at h
        obtain ⟨taken, htaken, rfl⟩ := h
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        obtain ⟨hsz, hreg⟩ := denot_frame htaken hcap.2 u hu
        exact ⟨hsz, fun i hi hw => hreg i hi (by simpa only [repCount] using hw)⟩
  | .rep lo hi greedy body =>
      rw [denot.eq_def] at h
      rw [CapsBelow] at hcap
      match hi with
      | some 0 =>
          simp only [] at h
          cases h
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨rfl, fun _ _ _ => rfl⟩
      | some 1 =>
          simp only [] at h
          split at h <;> rename_i hlo
          · intro t ht
            obtain ⟨hsz, hreg⟩ := denot_frame h hcap t ht
            exact ⟨hsz, fun i hi hw =>
              hreg i hi (by simpa only [repCount] using hw)⟩
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨taken, htaken, rfl⟩ := h
            intro t ht
            have hmem : t ∈ taken ∨ t = ⟨pos, regs⟩ := by
              split at ht
              · simpa only [List.mem_append, List.mem_singleton] using ht
              · rcases List.mem_cons.mp ht with h' | h'
                · exact Or.inr h'
                · exact Or.inl h'
            rcases hmem with hm | rfl
            · obtain ⟨hsz, hreg⟩ := denot_frame htaken hcap t hm
              exact ⟨hsz, fun i hi hw =>
                hreg i hi (by simpa only [repCount] using hw)⟩
            · exact ⟨rfl, fun _ _ _ => rfl⟩
      | none =>
          intro t ht
          obtain ⟨hsz, hreg⟩ :=
            denotRep_frame h hcap (Nat.le_add_right _ _) t ht
          simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
            at hsz hreg
          refine ⟨hsz, ?_⟩
          intro i hi hw
          simp only [repCount] at hw
          rw [hreg i hi (by omega) (by omega) (by omega),
            getBang_set_ne regs (novec + 2 * r0) (by omega)]
      | some (n + 2) =>
          intro t ht
          obtain ⟨hsz, hreg⟩ :=
            denotRep_frame h hcap (Nat.le_add_right _ _) t ht
          simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
            at hsz hreg
          refine ⟨hsz, ?_⟩
          intro i hi hw
          simp only [repCount] at hw
          rw [hreg i hi (by omega) (by omega) (by omega),
            getBang_set_ne regs (novec + 2 * r0) (by omega)]
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [denot.eq_def] at h
      cases h
      intro t ht
      have hregs : t.regs = regs := by
        first
          | (simp only [List.mem_singleton] at ht; subst ht; rfl)
          | (split at ht
             · simp only [List.mem_singleton] at ht; subst ht; rfl
             · simp at ht)
      exact ⟨by rw [hregs], fun _ _ _ => by rw [hregs]⟩
termination_by fuel _ a => (fuel, sizeOf a)

/-- Threading the frame through a concatenation: the head owns the first
stretch of rows, the tail the rest, and a thread of the answer is the
tail's answer to some thread of the head's. -/
theorem denotCat_frame {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel r0 : Nat} {kids : List Ast} {pos : Nat} {regs : Spec.Regs}
      {ts : List Spec.Thread},
    denotCat fuel c novec r0 kids pos regs = some ts →
    CapsBelow novec (.cat kids) →
    ∀ t ∈ ts, t.regs.size = regs.size ∧
      ∀ i, novec ≤ i →
        (i < novec + 2 * r0 ∨ novec + 2 * (r0 + repCount (.cat kids)) ≤ i) →
        t.regs[i]! = regs[i]! := by
  intro fuel r0 kids pos regs ts h hcap
  match kids with
  | [] =>
      rw [denotCat.eq_def] at h
      cases h
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨rfl, fun _ _ _ => rfl⟩
  | k :: rest =>
      rw [denotCat.eq_def] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨heads, hheads, tails, htails, rfl⟩ := h
      obtain ⟨hck, hcr⟩ := capsBelow_cat_cons.mp hcap
      intro t ht
      simp only [List.mem_flatten] at ht
      obtain ⟨l, hl, htl⟩ := ht
      obtain ⟨u, hu, hul⟩ := Spec.mapM_mem htails hl
      obtain ⟨hsz1, hreg1⟩ := denot_frame hheads hck u hu
      obtain ⟨hsz2, hreg2⟩ := denotCat_frame hul hcr t htl
      refine ⟨hsz2.trans hsz1, ?_⟩
      intro i hi hw
      rw [repCount_cat_cons] at hw
      rw [hreg2 i hi (by omega), hreg1 i hi (by omega)]
termination_by fuel _ kids => (fuel, sizeOf kids)

/-- The same for an alternation, where the arms all start from the caller's
file and each owns its own stretch of rows. -/
theorem denotAlt_frame {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel r0 : Nat} {arms : List Ast} {pos : Nat} {regs : Spec.Regs}
      {ts : List Spec.Thread},
    denotAlt fuel c novec r0 arms pos regs = some ts →
    CapsBelow novec (.alt arms) →
    ∀ t ∈ ts, t.regs.size = regs.size ∧
      ∀ i, novec ≤ i →
        (i < novec + 2 * r0 ∨ novec + 2 * (r0 + repCount (.alt arms)) ≤ i) →
        t.regs[i]! = regs[i]! := by
  intro fuel r0 arms pos regs ts h hcap
  match arms with
  | [] =>
      rw [denotAlt.eq_def] at h
      cases h
      intro t ht
      simp at ht
  | arm :: rest =>
      rw [denotAlt.eq_def] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := h
      obtain ⟨hca, hcr⟩ := capsBelow_alt_cons.mp hcap
      intro t ht
      rw [repCount_alt_cons]
      rcases List.mem_append.mp ht with hm | hm
      · obtain ⟨hsz, hreg⟩ := denot_frame hmine hca t hm
        exact ⟨hsz, fun i hi hw => hreg i hi (by omega)⟩
      · obtain ⟨hsz, hreg⟩ := denotAlt_frame htheirs hcr t hm
        exact ⟨hsz, fun i hi hw => hreg i hi (by omega)⟩
termination_by fuel _ arms => (fuel, sizeOf arms)

/-- A counted loop's frame, with its own pair of slots excused: `slot`
holds the count and `slot + 1` the entry position, and those two are
exactly what a repetition is meant to disturb. Everything else outside
the body's window survives every round. -/
theorem denotRep_frame {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel slot r0 : Nat} {body : Ast} {lo : Nat} {hi : Option Nat}
      {greedy : Bool} {cnt pos : Nat} {regs : Spec.Regs}
      {ts : List Spec.Thread},
    denotRep fuel c novec slot r0 body lo hi greedy cnt pos regs = some ts →
    CapsBelow novec body → novec ≤ slot →
    ∀ t ∈ ts, t.regs.size = regs.size ∧
      ∀ i, novec ≤ i → i ≠ slot → i ≠ slot + 1 →
        (i < novec + 2 * r0 ∨ novec + 2 * (r0 + repCount body) ≤ i) →
        t.regs[i]! = regs[i]! := by
  intro fuel slot r0 body lo hi greedy cnt pos regs ts h hcap hslot
  match fuel with
  | 0 =>
      rw [denotRep.eq_def] at h
      cases h
  | fuel + 1 =>
      rw [denotRep.eq_def] at h
      simp only [Option.pure_def, Option.bind_eq_bind] at h
      have henter : ∀ {taken : List Spec.Thread}
          {onward : List (List Spec.Thread)},
          denot fuel c novec r0 body pos
            (regs.set! (slot + 1) pos.toUInt32) = some taken →
          taken.mapM (fun t =>
            if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
              some [(⟨t.pos, t.regs.set! slot (cnt + 1).toUInt32⟩ :
                Spec.Thread)]
            else
              denotRep fuel c novec slot r0 body lo hi greedy (cnt + 1)
                t.pos (t.regs.set! slot (cnt + 1).toUInt32)) = some onward →
          ∀ t ∈ onward.flatten, t.regs.size = regs.size ∧
            ∀ i, novec ≤ i → i ≠ slot → i ≠ slot + 1 →
              (i < novec + 2 * r0 ∨ novec + 2 * (r0 + repCount body) ≤ i) →
              t.regs[i]! = regs[i]! := by
        intro taken onward htaken honward t ht
        simp only [List.mem_flatten] at ht
        obtain ⟨l, hl, htl⟩ := ht
        obtain ⟨u, hu, hul⟩ := Spec.mapM_mem honward hl
        obtain ⟨hsz1, hreg1⟩ := denot_frame htaken hcap u hu
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
          at hsz1 hreg1
        have key : ∀ w : Spec.Thread,
            w.regs.size = (u.regs.setIfInBounds slot (cnt + 1).toUInt32).size →
            (∀ i, novec ≤ i → i ≠ slot → i ≠ slot + 1 →
              (i < novec + 2 * r0 ∨ novec + 2 * (r0 + repCount body) ≤ i) →
              w.regs[i]! =
                (u.regs.setIfInBounds slot (cnt + 1).toUInt32)[i]!) →
            w.regs.size = regs.size ∧
              ∀ i, novec ≤ i → i ≠ slot → i ≠ slot + 1 →
                (i < novec + 2 * r0 ∨
                  novec + 2 * (r0 + repCount body) ≤ i) →
                w.regs[i]! = regs[i]! := by
          intro w hwsz hwreg
          rw [Array.size_setIfInBounds] at hwsz
          refine ⟨hwsz.trans hsz1, ?_⟩
          intro i hi hns hns1 hw
          rw [hwreg i hi hns hns1 hw, getBang_set_ne u.regs slot hns,
            hreg1 i hi hw, getBang_set_ne regs (slot + 1) hns1]
        simp only [Array.set!_eq_setIfInBounds] at hul
        split at hul
        · cases hul
          simp only [List.mem_singleton] at htl
          subst htl
          exact key _ rfl (fun _ _ _ _ _ => rfl)
        · obtain ⟨hsz2, hreg2⟩ := denotRep_frame hul hcap hslot t htl
          exact key t hsz2 hreg2
      split at h
      · obtain ⟨taken, htaken, h⟩ := bind_some h
        obtain ⟨onward, honward, h⟩ := bind_some h
        cases h
        exact henter htaken honward
      · split at h
        · cases h
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
        · obtain ⟨takenAll, hAll, h⟩ := bind_some h
          cases h
          obtain ⟨taken, htaken, hAll⟩ := bind_some hAll
          obtain ⟨onward, honward, hAll⟩ := bind_some hAll
          cases hAll
          intro t ht
          have hmem : t ∈ onward.flatten ∨ t = ⟨pos, regs⟩ := by
            split at ht
            · simpa only [List.mem_append, List.mem_singleton] using ht
            · rcases List.mem_cons.mp ht with h' | h'
              · exact Or.inr h'
              · exact Or.inl h'
          rcases hmem with hm | rfl
          · exact henter htaken honward t hm
          · exact ⟨rfl, fun _ _ _ _ _ => rfl⟩
termination_by fuel _ _ body => (fuel, 1 + sizeOf body)

end



/-- Each element on the left of a `Forall₂` has a partner on the right. -/
private theorem forall₂_mem_left {β : Type} {S : β → β → Prop} :
    ∀ {l l' : List β}, List.Forall₂ S l l' → ∀ {x}, x ∈ l →
    ∃ y ∈ l', S x y := by
  intro l l' h
  induction h with
  | nil => intro x hx; cases hx
  | @cons a b as bs hab _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, by simp, hab⟩
      · obtain ⟨y, hy, hxy⟩ := ih hx'
        exact ⟨y, by simp [hy], hxy⟩

/-- `denot`'s threads stay inside the subject, like the spec's. Nothing new
has to be proved: the projection lines the two enumerations up thread by
thread with equal positions, so `Spec.search_pos_le` answers for both.
Running the projection against `regs` itself is what makes the agreement
hypothesis free. -/
theorem denot_pos_le {c : Spec.SCtx} {novec fuel r0 : Nat} {a : Ast}
    {pos : Nat} {regs : Spec.Regs} {ts : List Spec.Thread}
    (h : denot fuel c novec r0 a pos regs = some ts)
    (hpos : pos ≤ c.s.size) (hn : novec ≤ regs.size) :
    ∀ t ∈ ts, pos ≤ t.pos ∧ t.pos ≤ c.s.size := by
  obtain ⟨tsO, hO, hrel⟩ := denot_search h ⟨hn, hn, fun _ _ => rfl⟩
  intro t ht
  obtain ⟨u, hu, hrelu⟩ := forall₂_mem_left hrel ht
  have hb := Spec.search_pos_le hO hpos u hu
  rw [hrelu.1]
  exact hb



/-! ## Totality of the reference enumeration

`Spec.search_some` one level up: at the sufficient fuel `denot` always
answers. The register writes are the only new bookkeeping and none of
them changes a file's length, so the `novec` bound travels along with
the position bound through every recursive call. -/

/-- A thread's file is at least as long as the one the search started
from. That is the only part of `denot_frame` the totality argument
needs, and like `denot_pos_le` it comes straight off the projection. -/
theorem denot_novec_le {c : Spec.SCtx} {novec fuel r0 : Nat} {a : Ast}
    {pos : Nat} {regs : Spec.Regs} {ts : List Spec.Thread}
    (h : denot fuel c novec r0 a pos regs = some ts)
    (hn : novec ≤ regs.size) :
    ∀ t ∈ ts, novec ≤ t.regs.size := by
  obtain ⟨tsO, _, hrel⟩ := denot_search h ⟨hn, hn, fun _ _ => rfl⟩
  intro t ht
  obtain ⟨u, _, hrelu⟩ := forall₂_mem_left hrel ht
  exact hrelu.2.1

mutual

/-- The reference enumeration answers whenever the spec's does, on the
same fuel and for the same reason. -/
theorem denot_some {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel r0 : Nat} {a : Ast} {pos : Nat} {regs : Spec.Regs},
    pos ≤ c.s.size → novec ≤ regs.size →
    Spec.suffFuel c.s.size a ≤ fuel →
    (denot fuel c novec r0 a pos regs).isSome := by
  intro fuel r0 a pos regs hpos hn hfuel
  match a with
  | .cat kids =>
      rw [denot.eq_def]
      exact denotCat_some hpos hn fun k hk =>
        Nat.le_trans (Spec.suffFuel_le_cat hk) hfuel
  | .alt arms =>
      rw [denot.eq_def]
      exact denotAlt_some hpos hn fun x hx =>
        Nat.le_trans (Spec.suffFuel_le_alt hx) hfuel
  | .grp cap body =>
      rw [denot.eq_def]
      simp only [Option.isSome_map]
      refine denot_some hpos ?_ (by rw [Spec.suffFuel] at hfuel; exact hfuel)
      split
      · simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
          using hn
      · exact hn
  | .rep lo hi greedy body =>
      match hi with
      | some 0 =>
          rw [denot.eq_def]
          simp
      | some 1 =>
          rw [denot.eq_def]
          simp only [Spec.suffFuel] at hfuel
          simp only []
          split
          · exact denot_some hpos hn (by omega)
          · simp only [Option.isSome_map]
            exact denot_some hpos hn (by omega)
      | none =>
          rw [denot.eq_def]
          simp only [Spec.suffFuel] at hfuel
          refine denotRep_some hpos ?_ (by simp only [Spec.repRemaining]; omega)
          simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
            using hn
      | some (_ + 2) =>
          rw [denot.eq_def]
          simp only [Spec.suffFuel] at hfuel
          refine denotRep_some hpos ?_ (by simp only [Spec.repRemaining]; omega)
          simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
            using hn
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [denot.eq_def]
      simp
termination_by fuel _ a => (fuel, sizeOf a)

theorem denotCat_some {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel r0 : Nat} {kids : List Ast} {pos : Nat} {regs : Spec.Regs},
    pos ≤ c.s.size → novec ≤ regs.size →
    (∀ k ∈ kids, Spec.suffFuel c.s.size k ≤ fuel) →
    (denotCat fuel c novec r0 kids pos regs).isSome := by
  intro fuel r0 kids pos regs hpos hn hfuel
  match kids with
  | [] =>
      rw [denotCat.eq_def]
      simp
  | k :: rest =>
      rw [denotCat.eq_def]
      obtain ⟨heads, hheads⟩ := Option.isSome_iff_exists.mp
        (denot_some (a := k) (r0 := r0) (regs := regs) hpos hn
          (hfuel k (by simp)))
      have hb := denot_pos_le hheads hpos hn
      have hsz := denot_novec_le hheads hn
      have htails : (heads.mapM fun t =>
          denotCat fuel c novec (r0 + repCount k) rest t.pos t.regs).isSome :=
        Spec.mapM_isSome fun t ht =>
          denotCat_some (hb t ht).2 (hsz t ht)
            fun k' hk' => hfuel k' (by simp [hk'])
      obtain ⟨tails, htails⟩ := Option.isSome_iff_exists.mp htails
      simp [hheads, htails]
termination_by fuel _ kids => (fuel, sizeOf kids)

theorem denotAlt_some {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel r0 : Nat} {arms : List Ast} {pos : Nat} {regs : Spec.Regs},
    pos ≤ c.s.size → novec ≤ regs.size →
    (∀ x ∈ arms, Spec.suffFuel c.s.size x ≤ fuel) →
    (denotAlt fuel c novec r0 arms pos regs).isSome := by
  intro fuel r0 arms pos regs hpos hn hfuel
  match arms with
  | [] =>
      rw [denotAlt.eq_def]
      simp
  | arm :: rest =>
      rw [denotAlt.eq_def]
      obtain ⟨mine, hmine⟩ := Option.isSome_iff_exists.mp
        (denot_some (a := arm) (r0 := r0) (regs := regs) hpos hn
          (hfuel arm (by simp)))
      obtain ⟨theirs, htheirs⟩ := Option.isSome_iff_exists.mp
        (denotAlt_some (arms := rest) (r0 := r0 + repCount arm) (regs := regs)
          hpos hn fun x hx => hfuel x (by simp [hx]))
      simp [hmine, htheirs]
termination_by fuel _ arms => (fuel, sizeOf arms)

/-- The budget argument of `Spec.searchRep_some`, unchanged: a round that
reaches its tail hands the next one a strictly smaller `repRemaining`,
because below the minimum the count rises, a bounded round rises toward
the bound, and an unbounded round past the minimum either consumed a
byte or was ended on the spot by the empty-match rule. The counter and
entry-position writes only have to be carried through the `novec`
bound. -/
theorem denotRep_some {c : Spec.SCtx} {novec : Nat} :
    ∀ {fuel slot r0 : Nat} {body : Ast} {lo : Nat} {hi : Option Nat}
      {greedy : Bool} {cnt pos : Nat} {regs : Spec.Regs},
    pos ≤ c.s.size → novec ≤ regs.size →
    Spec.repRemaining c.s.size lo hi cnt pos + Spec.suffFuel c.s.size body + 2
      ≤ fuel →
    (denotRep fuel c novec slot r0 body lo hi greedy cnt pos regs).isSome := by
  intro fuel slot r0 body lo hi greedy cnt pos regs hpos hn hfuel
  match fuel with
  | 0 => exact absurd hfuel (by omega)
  | fuel + 1 =>
      rw [denotRep.eq_def]
      simp only []
      have hbody : Spec.suffFuel c.s.size body ≤ fuel := by omega
      have hentry : novec ≤ (regs.set! (slot + 1) pos.toUInt32).size := by
        simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
          using hn
      have henter : (∀ h', hi = some h' → cnt < max lo h') →
          ∃ v, (do
            let taken ← denot fuel c novec r0 body pos
              (regs.set! (slot + 1) pos.toUInt32)
            let onward ← taken.mapM fun t =>
              if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                pure [(⟨t.pos, t.regs.set! slot (cnt + 1).toUInt32⟩ :
                  Spec.Thread)]
              else
                denotRep fuel c novec slot r0 body lo hi greedy (cnt + 1)
                  t.pos (t.regs.set! slot (cnt + 1).toUInt32)
            pure onward.flatten : Option (List Spec.Thread)) = some v := by
        intro hcommon
        obtain ⟨taken, htaken⟩ := Option.isSome_iff_exists.mp
          (denot_some (a := body) (r0 := r0)
            (regs := regs.set! (slot + 1) pos.toUInt32) hpos hentry hbody)
        have hb := denot_pos_le htaken hpos hentry
        have hsz := denot_novec_le htaken hentry
        have honward : (taken.mapM fun t =>
            if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
              some [(⟨t.pos, t.regs.set! slot (cnt + 1).toUInt32⟩ :
                Spec.Thread)]
            else
              denotRep fuel c novec slot r0 body lo hi greedy (cnt + 1)
                t.pos (t.regs.set! slot (cnt + 1).toUInt32)).isSome := by
          refine Spec.mapM_isSome fun t ht => ?_
          split
          · simp
          · rename_i hguard
            refine denotRep_some (hb t ht).2
              (by simpa only [Array.set!_eq_setIfInBounds,
                    Array.size_setIfInBounds] using hsz t ht) ?_
            cases hi with
            | some h' =>
                have hcnt := hcommon h' rfl
                simp only [Spec.repRemaining] at hfuel ⊢
                omega
            | none =>
                have h1 := (hb t ht).1
                have h2 := (hb t ht).2
                simp only [Option.isNone_none, Bool.true_and, Bool.and_eq_true,
                  beq_iff_eq, decide_eq_true_eq, not_and] at hguard
                simp only [Spec.repRemaining] at hfuel ⊢
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
termination_by fuel _ _ body => (fuel, 1 + sizeOf body)

end

/-! ## The shapes the compiler covers

`Covered` is the fragment relation's well-formedness predicate: every
wave 1 construct, with one deliberate exclusion — the empty alternation.
The compiler emits nothing for `alt []`, which behaves like `nul`, while
`searchAlt []` matches nothing; the engine's parser never emits an
alternation without arms, so `Covered` refuses the shape, and `WfAst`
discharges the same clause. The general counted repetition carries the
sentinel bound with it: the compiled repetition table spells an
unbounded high as `none32`, so a bounded one at or past that number would
compile to the unbounded semantics, empty-match rule included. -/

inductive Covered : Ast → Prop where
  | nul : Covered .nul
  | chr (b : UInt8) : Covered (.chr b)
  | chrCI (folded : UInt8) : Covered (.chrCI folded)
  | cls (bits : ClassBits) : Covered (.cls bits)
  | any : Covered .any
  | anyNoNL : Covered .anyNoNL
  | bsr : Covered .bsr
  | assn {a : Ast} {op : Op} : assnOp a = some op → Covered a
  | catNil : Covered (.cat [])
  | catCons {k : Ast} {kids : List Ast} :
      Covered k → Covered (.cat kids) → Covered (.cat (k :: kids))
  | altOne {a : Ast} : Covered a → Covered (.alt [a])
  | altCons {a b : Ast} {rest : List Ast} :
      Covered a → Covered (.alt (b :: rest)) → Covered (.alt (a :: b :: rest))
  | grp {cap : Nat} {body : Ast} : Covered body → Covered (.grp cap body)
  | repNone {lo : Nat} {greedy : Bool} {body : Ast} :
      Covered (.rep lo (some 0) greedy body)
  | repOne {greedy : Bool} {body : Ast} :
      Covered body → Covered (.rep 1 (some 1) greedy body)
  | repOpt {lo : Nat} {greedy : Bool} {body : Ast} :
      lo ≠ 1 → Covered body → Covered (.rep lo (some 1) greedy body)
  | repGen {lo : Nat} {hi : Option Nat} {greedy : Bool} {body : Ast} :
      hi ≠ some 0 → hi ≠ some 1 → (∀ h, hi = some h → h < none32) →
      Covered body → Covered (.rep lo hi greedy body)

/-- The conventions the mirror reads, packed the way the spec wants them.
Every leaf-test alignment below is a projection of this record. -/
def mctx (re : Re) (s : ByteArray) (mo : MOpts) : Spec.SCtx :=
  ⟨s, re.nltype, re.bsrtype, mo.notbol, mo.noteol⟩

/-- How the compiler spells a repetition's high bound: the number itself,
or the `none32` sentinel for an unbounded one. -/
def hiCode : Option Nat → Nat
  | some h => h
  | none => none32

/-! ## The fragment relation

Where a covered node's compiled form sits: one cell per leaf, juxtaposed
cat pieces, the split/branch/jump chain, and a group's optional save
brackets. A class leaf also pins its slice of the class table — not cell
by cell but semantically, as the membership test the VM will actually
run, which is the only thing the fragment theorem needs and the only
thing that survives table growth. -/

inductive FragAt (code : Array Inst) (classes : Array UInt8)
    (reps : Array RepInfo) : Nat → Ast → Nat → Nat → Prop where
  | nul {r0 lo : Nat} : FragAt code classes reps r0 .nul lo lo
  | chr {b : UInt8} {r0 lo : Nat}
      (hcell : code[lo]! = ⟨.chr, b.toNat, 0⟩) :
      FragAt code classes reps r0 (.chr b) lo (lo + 1)
  | chrCI {folded : UInt8} {r0 lo : Nat}
      (hcell : code[lo]! = ⟨.chrCI, folded.toNat, 0⟩) :
      FragAt code classes reps r0 (.chrCI folded) lo (lo + 1)
  | cls {bits : ClassBits} {r0 idx lo : Nat}
      (hcell : code[lo]! = ⟨.cls, idx, 0⟩)
      (hblob : idx * 32 + 32 ≤ classes.size)
      (hsem : ∀ b : UInt8,
        (classes[idx * 32 + (b >>> 3).toNat]! &&& (1 <<< (b &&& 7)) != 0) =
          bits.has b) :
      FragAt code classes reps r0 (.cls bits) lo (lo + 1)
  | any {r0 lo : Nat} (hcell : code[lo]! = ⟨.any, 0, 0⟩) :
      FragAt code classes reps r0 .any lo (lo + 1)
  | anyNoNL {r0 lo : Nat} (hcell : code[lo]! = ⟨.anyNoNL, 0, 0⟩) :
      FragAt code classes reps r0 .anyNoNL lo (lo + 1)
  | bsr {r0 lo : Nat} (hcell : code[lo]! = ⟨.bsr, 0, 0⟩) :
      FragAt code classes reps r0 .bsr lo (lo + 1)
  | assn {a : Ast} {op : Op} {r0 lo : Nat}
      (ha : assnOp a = some op) (hcell : code[lo]! = ⟨op, 0, 0⟩) :
      FragAt code classes reps r0 a lo (lo + 1)
  | catNil {r0 lo : Nat} : FragAt code classes reps r0 (.cat []) lo lo
  | catCons {k : Ast} {kids : List Ast} {r0 lo mid hi : Nat}
      (hk : FragAt code classes reps r0 k lo mid)
      (hkids : FragAt code classes reps (r0 + repCount k) (.cat kids) mid hi) :
      FragAt code classes reps r0 (.cat (k :: kids)) lo hi
  | altOne {a : Ast} {r0 lo hi : Nat}
      (ha : FragAt code classes reps r0 a lo hi) :
      FragAt code classes reps r0 (.alt [a]) lo hi
  | altCons {a b : Ast} {rest : List Ast} {r0 lo j hi : Nat}
      (hsplit : code[lo]! = ⟨.split, lo + 1, j + 1⟩)
      (ha : FragAt code classes reps r0 a (lo + 1) j)
      (hjump : code[j]! = ⟨.jump, hi, 0⟩)
      (hrest : FragAt code classes reps (r0 + repCount a)
        (.alt (b :: rest)) (j + 1) hi) :
      FragAt code classes reps r0 (.alt (a :: b :: rest)) lo hi
  | grpZero {body : Ast} {r0 lo hi : Nat}
      (hbody : FragAt code classes reps r0 body lo hi) :
      FragAt code classes reps r0 (.grp 0 body) lo hi
  | grpCap {cap : Nat} {body : Ast} {r0 lo j : Nat}
      (hcap : cap ≠ 0)
      (hopen : code[lo]! = ⟨.save, 2 * cap, 0⟩)
      (hbody : FragAt code classes reps r0 body (lo + 1) j)
      (hclose : code[j]! = ⟨.save, 2 * cap + 1, 0⟩) :
      FragAt code classes reps r0 (.grp cap body) lo (j + 1)
  | repNone {lo' : Nat} {greedy : Bool} {body : Ast} {r0 lo : Nat} :
      FragAt code classes reps r0 (.rep lo' (some 0) greedy body) lo lo
  | repOne {greedy : Bool} {body : Ast} {r0 lo hi : Nat}
      (hbody : FragAt code classes reps r0 body lo hi) :
      FragAt code classes reps r0 (.rep 1 (some 1) greedy body) lo hi
  | repOpt {lo' : Nat} {greedy : Bool} {body : Ast} {r0 sp j : Nat}
      (hlo : lo' ≠ 1)
      (hsplit : code[sp]! =
        (if greedy then ⟨.split, sp + 1, j⟩ else ⟨.split, j, sp + 1⟩))
      (hbody : FragAt code classes reps r0 body (sp + 1) j) :
      FragAt code classes reps r0 (.rep lo' (some 1) greedy body) sp j
  | repGen {lo' : Nat} {hi : Option Nat} {greedy : Bool} {body : Ast}
      {r0 lo j : Nat}
      (hzero : code[lo]! = ⟨.repZero, r0, 0⟩)
      (hloop : code[lo + 1]! = ⟨.repLoop, r0, 0⟩)
      (henter : code[lo + 2]! = ⟨.repEnter, r0, 0⟩)
      (hnext : code[j]! = ⟨.repNext, r0, 0⟩)
      (hrow : r0 < reps.size)
      (hinfo : reps[r0]! = ⟨lo', hiCode hi, greedy, lo + 1, lo + 2, j + 1⟩)
      (hbound : ∀ h, hi = some h → h < none32)
      (hnot0 : hi ≠ some 0) (hnot1 : hi ≠ some 1)
      (hbody : FragAt code classes reps (r0 + 1) body (lo + 3) j) :
      FragAt code classes reps r0 (.rep lo' hi greedy body) lo (j + 1)

/-- The byte's high-bit index stays inside a 32-byte class row. -/
private theorem shr3_lt (b : UInt8) : (b >>> 3).toNat < 32 := by
  have hb : b.toNat < 256 := b.toNat_lt
  have : (b >>> 3).toNat = b.toNat / 8 := by
    rw [UInt8.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  omega

theorem FragAt.le {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast}
    {lo hi : Nat} (h : FragAt code classes reps r0 a lo hi) : lo ≤ hi := by
  induction h <;> omega

/-- A fragment only pins code cells inside its range, class cells below
the table's size and repetition rows below the repetition table's, so any
code that agrees there — and any larger table that preserves the prefix —
carries the same fragment. -/
theorem FragAt.mono {code code' : Array Inst} {classes classes' : Array UInt8}
    {reps reps' : Array RepInfo} {r0 : Nat}
    {a : Ast} {lo hi : Nat} (h : FragAt code classes reps r0 a lo hi)
    (hag : ∀ pc, lo ≤ pc → pc < hi → code'[pc]! = code[pc]!)
    (hcsz : classes.size ≤ classes'.size)
    (hcag : ∀ j, j < classes.size → classes'[j]! = classes[j]!)
    (hrsz : reps.size ≤ reps'.size)
    (hrag : ∀ i, i < reps.size → reps'[i]! = reps[i]!) :
    FragAt code' classes' reps' r0 a lo hi := by
  induction h with
  | nul => exact .nul
  | chr hcell =>
      exact .chr ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | chrCI hcell =>
      exact .chrCI ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | @cls bits r0 idx lo hcell hblob hsem =>
      refine .cls ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
        (by omega) ?_
      intro b
      rw [hcag _ (by have := shr3_lt b; omega)]
      exact hsem b
  | any hcell =>
      exact .any ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | anyNoNL hcell =>
      exact .anyNoNL ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | bsr hcell =>
      exact .bsr ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | assn ha hcell =>
      exact .assn ha ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
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
  | grpZero hbody ihbody => exact .grpZero (ihbody hag)
  | grpCap hcap hopen hbody hclose ihbody =>
      have h1 := hbody.le
      exact .grpCap hcap
        ((hag _ (by omega) (by omega)).trans hopen)
        (ihbody fun pc h1' h2' => hag pc (by omega) (by omega))
        ((hag _ (by omega) (by omega)).trans hclose)
  | repNone => exact .repNone
  | repOne hbody ihbody => exact .repOne (ihbody hag)
  | repOpt hlo hsplit hbody ihbody =>
      have h1 := hbody.le
      exact .repOpt hlo
        ((hag _ (by omega) (by omega)).trans hsplit)
        (ihbody fun pc h1' h2' => hag pc (by omega) h2')
  | @repGen lo' hi greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      have h1 := hbody.le
      exact .repGen
        ((hag _ (by omega) (by omega)).trans hzero)
        ((hag _ (by omega) (by omega)).trans hloop)
        ((hag _ (by omega) (by omega)).trans henter)
        ((hag _ (by omega) (by omega)).trans hnext)
        (by omega)
        ((hrag r0 hrow).trans hinfo) hbound hnot0 hnot1
        (ihbody fun pc h1' h2' => hag pc (by omega) (by omega))

/-- A fragment never looks below its own base row: every repetition it
pins sits at `r0` or above. So the rows underneath may still move — which
is exactly what an enclosing counted repetition does when it comes back
to write its exit in. -/
theorem FragAt.patchBelow {code : Array Inst} {classes : Array UInt8}
    {reps reps' : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi)
    (hrsz : reps.size ≤ reps'.size)
    (hrag : ∀ i, r0 ≤ i → i < reps.size → reps'[i]! = reps[i]!) :
    FragAt code classes reps' r0 a lo hi := by
  induction h with
  | nul => exact .nul
  | chr hcell => exact .chr hcell
  | chrCI hcell => exact .chrCI hcell
  | cls hcell hblob hsem => exact .cls hcell hblob hsem
  | any hcell => exact .any hcell
  | anyNoNL hcell => exact .anyNoNL hcell
  | bsr hcell => exact .bsr hcell
  | assn ha hcell => exact .assn ha hcell
  | catNil => exact .catNil
  | catCons hk hkids ihk ihkids =>
      exact .catCons (ihk fun i h1 h2 => hrag i (by omega) h2)
        (ihkids fun i h1 h2 => hrag i (by omega) h2)
  | altOne _ iha => exact .altOne (iha hrag)
  | altCons hsplit _ hjump _ iha ihrest =>
      exact .altCons hsplit (iha hrag) hjump
        (ihrest fun i h1 h2 => hrag i (by omega) h2)
  | grpZero _ ihbody => exact .grpZero (ihbody hrag)
  | grpCap hcap hopen _ hclose ihbody =>
      exact .grpCap hcap hopen (ihbody hrag) hclose
  | repNone => exact .repNone
  | repOne _ ihbody => exact .repOne (ihbody hrag)
  | repOpt hlo hsplit _ ihbody => exact .repOpt hlo hsplit (ihbody hrag)
  | @repGen lo' hi greedy body r0 lo j hzero hloop henter hnext hrow hinfo
      hbound hnot0 hnot1 _ ihbody =>
      exact .repGen hzero hloop henter hnext (by omega)
        ((hrag r0 (Nat.le_refl _) hrow).trans hinfo) hbound hnot0 hnot1
        (ihbody fun i h1 h2 => hrag i (by omega) h2)

/-- A fragment derivation is a subset witness. -/
theorem FragAt.covered {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast}
    {lo hi : Nat} (h : FragAt code classes reps r0 a lo hi) : Covered a := by
  induction h with
  | nul => exact .nul
  | chr _ => exact .chr _
  | chrCI _ => exact .chrCI _
  | cls _ _ _ => exact .cls _
  | any _ => exact .any
  | anyNoNL _ => exact .anyNoNL
  | bsr _ => exact .bsr
  | assn ha _ => exact .assn ha
  | catNil => exact .catNil
  | catCons _ _ ihk ihkids => exact .catCons ihk ihkids
  | altOne _ iha => exact .altOne iha
  | altCons _ _ _ _ iha ihrest => exact .altCons iha ihrest
  | grpZero _ ihbody => exact .grp ihbody
  | grpCap _ _ _ _ ihbody => exact .grp ihbody
  | repNone => exact .repNone
  | repOne _ ihbody => exact .repOne ihbody
  | repOpt hlo _ _ ihbody => exact .repOpt hlo ihbody
  | repGen _ _ _ _ _ _ hbound hnot0 hnot1 _ ihbody =>
      exact .repGen hnot0 hnot1 hbound ihbody

/-! ## The fragment theorem -/

section Frag

variable {re : Re} {s : ByteArray} {mo : MOpts} {start attempt : Nat}

/-- The assertion family's effect: the spec's `assertionHolds`, verbatim,
because `mctx`'s projections are the very conventions `btStep` reads. -/
theorem eff_assn {a : Ast} {op : Op} {pc pos : Nat} {regs : Spec.Regs}
    (ha : assnOp a = some op) (hcell : re.code[pc]! = ⟨op, 0, 0⟩) :
    eff re s mo start attempt pc pos regs =
      if Spec.assertionHolds (mctx re s mo) a pos then
        .goto (pc + 1) pos regs
      else .fail := by
  cases a <;> simp only [assnOp] at ha <;> try cases ha
  all_goals simp [eff, hcell, Spec.assertionHolds, mctx]

/-- Retargeting every pending thread through an equivalent continuation,
a per-thread transform folded in: covers a jump (identity transform) and
a group's closing save. -/
theorem resumes_retarget {pcA pcB : Nat} {f : Spec.Thread → Spec.Thread}
    (h : ∀ (t : Spec.Thread) (stk : List Entry) (r : Out),
      Runs re s mo start attempt pcA t.pos t.regs stk r ↔
      Runs re s mo start attempt pcB (f t).pos (f t).regs stk r) :
    ∀ (ts : List Spec.Thread) (T : List Entry) (r : Out),
      Resumes re s mo start attempt ((ts.map fun t => (pcA, t)) ++ T) r ↔
      Resumes re s mo start attempt ((ts.map fun t => (pcB, f t)) ++ T) r := by
  intro ts
  induction ts with
  | nil => intro T r; exact Iff.rfl
  | cons t ts ihp =>
      intro T r
      simp only [List.map_cons, List.cons_append, resumes_cons]
      rw [h]
      exact runs_congr_stack fun r' => ihp T r'

/-- Below the wrap a count survives the round trip through the register
file, which is what lets the machine's `UInt32` counter stand for the
enumeration's `Nat` one. -/
private theorem toNat_toUInt32 {n : Nat} (h : n < 2 ^ 32) :
    (n.toUInt32).toNat = n := by
  simp [Nat.toUInt32, Nat.mod_eq_of_lt h]

private theorem toUInt32_succ (n : Nat) :
    (n + 1).toUInt32 = n.toUInt32 + 1 := by
  simp [Nat.toUInt32]

/-- Positions stay far below the wrap, so the machine's copy of one
identifies it. -/
private theorem toUInt32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : a.toUInt32 = b.toUInt32) : a = b := by
  have h' := congrArg UInt32.toNat h
  simpa [Nat.toUInt32, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h'

/-- A consuming or asserting leaf, generically: given the effect is a
test between one continuation and a fail, the run means the test's
one-or-zero-thread enumeration. -/
private theorem frag_leaf {lo : Nat} {pos : Nat} {regs : Spec.Regs}
    {cond : Bool} {t : Spec.Thread}
    (heff : eff re s mo start attempt lo pos regs =
      if cond then .goto (lo + 1) t.pos t.regs else .fail)
    (stk : List Entry) (r : Out) :
    Runs re s mo start attempt lo pos regs stk r ↔
      Resumes re s mo start attempt
        (((if cond then [t] else []).map fun u => (lo + 1, u)) ++ stk) r := by
  rw [runs_eff, heff]
  by_cases hc : cond = true
  · simp only [if_pos hc, Eff.judg, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, resumes_cons]
  · simp only [if_neg hc, Eff.judg, List.map_nil, List.nil_append]

/-- Continuing every pending thread of a fragment into its continuation:
the list-level engine of the cat case, over an enumeration that answers
one head thread at a time. -/
theorem resumes_bindM {mid hi : Nat}
    {f : Spec.Thread → Option (List Spec.Thread)} :
    ∀ (ts : List Spec.Thread) (oss : List (List Spec.Thread)),
      ts.mapM f = some oss →
      (∀ t ∈ ts, ∀ us, f t = some us → ∀ (stk : List Entry) (r : Out),
        Runs re s mo start attempt mid t.pos t.regs stk r ↔
        Resumes re s mo start attempt ((us.map fun u => (hi, u)) ++ stk) r) →
      ∀ (stk : List Entry) (r : Out),
        Resumes re s mo start attempt ((ts.map fun t => (mid, t)) ++ stk) r ↔
        Resumes re s mo start attempt
          ((oss.flatten.map fun u => (hi, u)) ++ stk) r := by
  intro ts
  induction ts with
  | nil =>
      intro oss hm _ stk r
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
      subst hm
      simp
  | cons t ts ihp =>
      intro oss hm hpt stk r
      rw [List.mapM_cons] at hm
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hm
      obtain ⟨us, hus, oss', hoss', rfl⟩ := hm
      simp only [List.map_cons, List.cons_append, resumes_cons]
      rw [hpt t (List.mem_cons_self ..) us hus]
      rw [resumes_congr_tail
        (fun r' => ihp oss' hoss'
          (fun t' ht' => hpt t' (List.mem_cons_of_mem t ht')) stk r')]
      simp [List.map_append, List.append_assoc]

/-- The fragment theorem: running the mirror from a fragment's entry with
any pending stack behaves exactly like queuing the reference
enumeration's matches — retargeted at the fragment's exit — in front of
that stack.

The three side conditions are what the counted repetition needs and every
other construct only passes on: the position is inside the subject, so the
entry position a round records survives the trip through `UInt32`; the
fuel is below the sentinel, so a count can never reach it; and the
register file is long enough to hold the rows this node's repetitions
claim, so the counter writes land instead of falling off the end. -/
theorem frag_runs {a : Ast} {r0 lo hi : Nat} (hs : s.size ≤ ceiling)
    (h : FragAt re.code re.classes re.reps r0 a lo hi) :
    ∀ (fuel pos : Nat) (regs : Spec.Regs) (ts : List Spec.Thread),
      denot fuel (mctx re s mo) re.novec r0 a pos regs = some ts →
      pos ≤ s.size → fuel < none32 → CapsBelow re.novec a →
      re.novec + 2 * (r0 + repCount a) ≤ regs.size →
      ∀ (stk : List Entry) (r : Out),
        Runs re s mo start attempt lo pos regs stk r ↔
        Resumes re s mo start attempt
          ((ts.map fun t => (hi, t)) ++ stk) r := by
  induction h with
  | nul =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      simp only [List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | @chr b r0 lo hcell =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && byteAt s pos == b then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell, UInt8.ofNat_toNat]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      rfl
  | @chrCI folded r0 lo hcell =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && lowerByte (byteAt s pos) == folded then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell, UInt8.ofNat_toNat]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      rfl
  | @cls bits r0 idx lo hcell hblob hsem =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      have hch : re.classHas idx (byteAt s pos) =
          bits.has (byteAt s pos) := hsem (byteAt s pos)
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && bits.has (byteAt s pos) then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp only [eff, hcell]
        rw [hch]
        by_cases hp : (decide (pos < s.size)) = true <;> simp [hp]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      rfl
  | @any r0 lo hcell =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      -- Read the enumeration's answer on the subject itself: the context
      -- the mirror builds projects to it, and the `if` is over the same
      -- test either way.
      have hd' : (some (if pos < s.size then [(⟨pos + 1, regs⟩ : Spec.Thread)]
          else []) : Option (List Spec.Thread)) = some ts := hd
      cases hd'
      have heff : eff re s mo start attempt lo pos regs =
          if decide (pos < s.size) then .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      simp
  | @anyNoNL r0 lo hcell =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && newlineAt s pos re.nltype == 0 then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      rfl
  | @bsr r0 lo hcell =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      have heff : eff re s mo start attempt lo pos regs =
          if bsrAt s pos re.bsrtype != 0 then
            .goto (lo + 1) (pos + bsrAt s pos re.bsrtype) regs
          else .fail := by
        simp [eff, hcell]
      rw [frag_leaf (t := ⟨pos + bsrAt s pos re.bsrtype, regs⟩) heff]
      rfl
  | @assn a op r0 lo ha hcell =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot_assn ha] at hd
      cases hd
      exact frag_leaf (t := ⟨pos, regs⟩) (eff_assn ha hcell) stk r
  | catNil =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot_cat, denotCat.eq_def] at hd
      cases hd
      simp only [List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | @catCons k kids r0 lo mid hi hk hkids ihk ihkids =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      obtain ⟨hck, hcr⟩ := capsBelow_cat_cons.mp hcaps
      rw [repCount_cat_cons] at hsize
      rw [denot_cat, denotCat.eq_def] at hd
      simp only [Option.pure_def, Option.bind_eq_bind] at hd
      obtain ⟨heads, hheads, hd⟩ := bind_some hd
      obtain ⟨tails, htails, hd⟩ := bind_some hd
      cases hd
      rw [ihk fuel pos regs heads hheads hpos hfuel hck (by omega) stk r]
      refine resumes_bindM heads tails htails ?_ stk r
      intro t ht us hus stk' r'
      obtain ⟨hsz, _⟩ := denot_frame hheads hck t ht
      obtain ⟨_, hp2⟩ := denot_pos_le hheads hpos (by omega) t ht
      exact ihkids fuel t.pos t.regs us (by rw [denot_cat]; exact hus) hp2 hfuel
        hcr (by rw [hsz]; omega) stk' r'
  | @altOne a r0 lo hi ha iha =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      rw [repCount_alt_cons, repCount_alt_nil] at hsize
      rw [denot_alt, denotAlt.eq_def] at hd
      simp only [Option.pure_def, Option.bind_eq_bind] at hd
      obtain ⟨mine, hmine, hd⟩ := bind_some hd
      obtain ⟨theirs, htheirs, hd⟩ := bind_some hd
      cases hd
      rw [denotAlt.eq_def] at htheirs
      cases htheirs
      simp only [List.append_nil]
      exact iha fuel pos regs mine hmine hpos hfuel
        (capsBelow_alt_cons.mp hcaps).1 (by omega) stk r
  | @altCons a b rest r0 lo j hi hsplit ha hjump hrest iha ihrest =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      obtain ⟨hca, hcr⟩ := capsBelow_alt_cons.mp hcaps
      rw [repCount_alt_cons] at hsize
      rw [denot_alt, denotAlt.eq_def] at hd
      simp only [Option.pure_def, Option.bind_eq_bind] at hd
      obtain ⟨mine, hmine, hd⟩ := bind_some hd
      obtain ⟨theirs, htheirs, hd⟩ := bind_some hd
      cases hd
      have heff : eff re s mo start attempt lo pos regs =
          .fork (lo + 1) (j + 1) := by
        simp [eff, hsplit]
      rw [runs_eff, heff]
      simp only [Eff.judg]
      rw [iha fuel pos regs mine hmine hpos hfuel hca (by omega)
        ((j + 1, (⟨pos, regs⟩ : Spec.Thread)) :: stk) r]
      have hjt : ∀ (t : Spec.Thread) (stk' : List Entry) (r' : Out),
          Runs re s mo start attempt j t.pos t.regs stk' r' ↔
          Runs re s mo start attempt hi (id t).pos (id t).regs stk' r' := by
        intro t stk' r'
        have heffj : eff re s mo start attempt j t.pos t.regs =
            .goto hi t.pos t.regs := by
          simp [eff, hjump]
        rw [runs_eff, heffj]
        exact Iff.rfl
      rw [resumes_retarget hjt mine _ r]
      have hstep : ∀ r', Resumes re s mo start attempt
          ((j + 1, (⟨pos, regs⟩ : Spec.Thread)) :: stk) r' ↔
          Resumes re s mo start attempt
            ((theirs.map fun t => (hi, t)) ++ stk) r' := by
        intro r'
        rw [resumes_cons]
        exact ihrest fuel pos regs theirs (by rw [denot_alt]; exact htheirs)
          hpos hfuel hcr (by omega) stk r'
      refine Iff.trans (resumes_congr_tail hstep) ?_
      simp [List.map_append, List.append_assoc]
  | @grpZero body r0 lo hi hbody ihbody =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      rw [CapsBelow] at hcaps
      rw [repCount] at hsize
      rw [denot.eq_def] at hd
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false,
        Option.map_eq_some_iff] at hd
      obtain ⟨taken, htaken, rfl⟩ := hd
      rw [ihbody fuel pos regs taken htaken hpos hfuel hcaps.2 hsize stk r]
      simp
  | @grpCap cap body r0 lo j hcap hopen hbody hclose ihbody =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      rw [CapsBelow] at hcaps
      rw [repCount] at hsize
      have hcap' : (cap != 0) = true := by simpa using hcap
      rw [denot.eq_def] at hd
      simp only [hcap', if_true, Option.map_eq_some_iff] at hd
      obtain ⟨taken, htaken, rfl⟩ := hd
      have heff : eff re s mo start attempt lo pos regs =
          .goto (lo + 1) pos (regs.set! (2 * cap) pos.toUInt32) := by
        simp [eff, hopen]
      rw [runs_eff, heff]
      simp only [Eff.judg]
      rw [ihbody fuel pos (regs.set! (2 * cap) pos.toUInt32) taken htaken hpos
        hfuel hcaps.2 (by simpa [Array.set!_eq_setIfInBounds] using hsize) stk r]
      have hstep : ∀ (t : Spec.Thread) (stk' : List Entry) (r' : Out),
          Runs re s mo start attempt j t.pos t.regs stk' r' ↔
          Runs re s mo start attempt (j + 1)
            ((fun t : Spec.Thread =>
              (⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩ :
                Spec.Thread)) t).pos
            ((fun t : Spec.Thread =>
              (⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩ :
                Spec.Thread)) t).regs stk' r' := by
        intro t stk' r'
        have heffj : eff re s mo start attempt j t.pos t.regs =
            .goto (j + 1) t.pos (t.regs.set! (2 * cap + 1) t.pos.toUInt32) := by
          simp [eff, hclose]
        rw [runs_eff, heffj]
        exact Iff.rfl
      rw [resumes_retarget hstep taken stk r]
      simp [List.map_map, Function.comp_def]
  | repNone =>
      intro fuel pos regs ts hd _ _ _ _ stk r
      rw [denot.eq_def] at hd
      cases hd
      simp only [List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | @repOne greedy body r0 lo hi hbody ihbody =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      rw [CapsBelow] at hcaps
      rw [repCount] at hsize
      rw [denot.eq_def] at hd
      simp only [beq_self_eq_true, if_true] at hd
      exact ihbody fuel pos regs ts hd hpos hfuel hcaps hsize stk r
  | @repGen lo' hi greedy body r0 lo j hzero hloop hentr hnext hrow hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      rw [CapsBelow] at hcaps
      have hrc : repCount (Ast.rep lo' hi greedy body) = 1 + repCount body := by
        cases hi with
        | none => simp [repCount]
        | some k =>
            match k with
            | 0 => exact absurd rfl hnot0
            | 1 => exact absurd rfl hnot1
            | _ + 2 => simp [repCount]
      rw [hrc] at hsize
      have hslot : re.novec + r0 * 2 = re.novec + 2 * r0 := by omega
      -- The row the compiler pinned, read back through the three targets it
      -- fixed: the loop head, the body entry and the exit.
      have hrep : re.reps[r0]! =
          (⟨lo', hiCode hi, greedy, lo + 1, lo + 2, j + 1⟩ : RepInfo) := hinfo
      have hnone : (hiCode hi == none32) = hi.isNone := by
        cases hi with
        | none => simp [hiCode]
        | some h =>
            have hh := hbound h rfl
            simp only [hiCode, Option.isNone_some, beq_eq_false_iff_ne]
            omega
      have hge : ∀ n : Nat, n < none32 →
          (n ≥ hiCode hi ↔ hi.any (fun x => decide (n ≥ x)) = true) := by
        intro n hn
        cases hi with
        | none =>
            simp only [hiCode, Option.any_none, Bool.false_eq_true, iff_false,
              Nat.not_le]
            omega
        | some h => simp [hiCode]
      -- One round of the counted loop, from the deciding head.
      have key : ∀ (f cnt pos' : Nat) (regs' : Spec.Regs)
          (ts' : List Spec.Thread),
          denotRep f (mctx re s mo) re.novec (re.novec + 2 * r0) (r0 + 1) body
            lo' hi greedy cnt pos' regs' = some ts' →
          regs'[re.novec + 2 * r0]! = cnt.toUInt32 →
          pos' ≤ s.size → cnt + f < none32 →
          re.novec + 2 * (r0 + 1 + repCount body) ≤ regs'.size →
          ∀ (stk' : List Entry) (r' : Out),
            Runs re s mo start attempt (lo + 1) pos' regs' stk' r' ↔
            Resumes re s mo start attempt
              ((ts'.map fun t => (j + 1, t)) ++ stk') r' := by
        intro f
        induction f with
        | zero =>
            intro cnt pos' regs' ts' hdr _ _ _ _ stk' r'
            rw [denotRep.eq_def] at hdr
            exact absurd hdr (by simp)
        | succ f ihf =>
            intro cnt pos' regs' ts' hdr hcnt hpos' hwrap hsz' stk' r'
            have hcntlt : cnt < 2 ^ 32 := by
              simp only [none32] at hwrap
              omega
            have hcntv : (regs'[re.novec + 2 * r0]!).toNat = cnt := by
              rw [hcnt, toNat_toUInt32 hcntlt]
            have heffloop : eff re s mo start attempt (lo + 1) pos' regs' =
                (if cnt < lo' then Eff.goto (lo + 2) pos' regs'
                 else if cnt ≥ hiCode hi then
                   Eff.goto (j + 1) pos' regs'
                 else if greedy then Eff.fork (lo + 2) (j + 1)
                 else Eff.fork (j + 1) (lo + 2)) := by
              simp only [eff, hloop, hslot, hrep, hcntv]
            -- The body, entered through the round's own entry-position write.
            have henter : ∀ (taken : List Spec.Thread)
                (onward : List (List Spec.Thread)),
                denot f (mctx re s mo) re.novec (r0 + 1) body pos'
                  (regs'.set! (re.novec + 2 * r0 + 1) pos'.toUInt32) =
                  some taken →
                taken.mapM (fun t =>
                  if hi.isNone && t.pos == pos' && cnt + 1 ≥ lo' then
                    some [(⟨t.pos, t.regs.set! (re.novec + 2 * r0)
                      (cnt + 1).toUInt32⟩ : Spec.Thread)]
                  else
                    denotRep f (mctx re s mo) re.novec (re.novec + 2 * r0)
                      (r0 + 1) body lo' hi greedy (cnt + 1) t.pos
                      (t.regs.set! (re.novec + 2 * r0) (cnt + 1).toUInt32)) =
                  some onward →
                ∀ (stk'' : List Entry) (r'' : Out),
                  Runs re s mo start attempt (lo + 2) pos' regs' stk'' r'' ↔
                  Resumes re s mo start attempt
                    ((onward.flatten.map fun t => (j + 1, t)) ++ stk'') r'' := by
              intro taken onward htaken honward stk'' r''
              have heffe : eff re s mo start attempt (lo + 2) pos' regs' =
                  Eff.goto (lo + 3) pos'
                    (regs'.set! (re.novec + 2 * r0 + 1) pos'.toUInt32) := by
                simp only [eff, hentr, hslot]
              rw [runs_eff, heffe]
              simp only [Eff.judg]
              rw [ihbody f pos' _ taken htaken hpos' (by omega) hcaps
                (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                    omega) stk'' r'']
              refine resumes_bindM taken onward honward ?_ stk'' r''
              intro t ht us hus stk₃ r₃
              obtain ⟨hszt, hfrt⟩ := denot_frame htaken hcaps t ht
              obtain ⟨_, hpost⟩ := denot_pos_le htaken hpos' (by
                rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                omega) t ht
              rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hszt
              simp only [Array.set!_eq_setIfInBounds] at hfrt
              -- Neither counter slot is the body's to touch.
              have hkeep0 : t.regs[re.novec + 2 * r0]! = cnt.toUInt32 := by
                rw [hfrt _ (by omega) (by omega),
                  getBang_set_ne regs' (re.novec + 2 * r0 + 1) (by omega), hcnt]
              have hkeep1 :
                  t.regs[re.novec + 2 * r0 + 1]! = pos'.toUInt32 := by
                rw [hfrt _ (by omega) (by omega),
                  getBang_set_eq regs' (by omega)]
              have hpost' : t.pos ≤ s.size := hpost
              have hposlt : t.pos < 2 ^ 32 := by
                simp only [ceiling] at hs
                omega
              have hpos'lt : pos' < 2 ^ 32 := by
                simp only [ceiling] at hs
                omega
              have hsame : (t.pos.toUInt32 == pos'.toUInt32) =
                  (t.pos == pos') := by
                by_cases hpe : t.pos = pos'
                · subst hpe
                  simp
                · have hne : UInt32.ofNat t.pos ≠ UInt32.ofNat pos' :=
                    fun heq => hpe (toUInt32_inj hposlt hpos'lt heq)
                  rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hpe]
              have hcnt1 : ((cnt + 1).toUInt32).toNat = cnt + 1 :=
                toNat_toUInt32 (by simp only [none32] at hwrap; omega)
              have heffn : eff re s mo start attempt j t.pos t.regs =
                  (if hi.isNone && t.pos == pos' && cnt + 1 ≥ lo' then
                     Eff.goto (j + 1) t.pos
                       (t.regs.set! (re.novec + 2 * r0) (cnt + 1).toUInt32)
                   else Eff.goto (lo + 1) t.pos
                       (t.regs.set! (re.novec + 2 * r0) (cnt + 1).toUInt32)) := by
                simp only [eff, hnext, hslot, hrep, hkeep0, hkeep1, hsame,
                  hnone, ← toUInt32_succ, hcnt1]
              rw [runs_eff, heffn]
              by_cases htst : (hi.isNone && t.pos == pos' &&
                  decide (cnt + 1 ≥ lo')) = true
              · rw [if_pos htst] at hus ⊢
                cases hus
                simp only [Eff.judg, List.map_cons, List.map_nil,
                  List.cons_append, List.nil_append]
                exact (resumes_cons (t := ⟨t.pos, t.regs.set!
                  (re.novec + 2 * r0) (cnt + 1).toUInt32⟩)).symm
              · rw [if_neg htst] at hus ⊢
                simp only [Eff.judg]
                exact ihf (cnt + 1) t.pos _ us hus
                  (by rw [Array.set!_eq_setIfInBounds,
                        getBang_set_eq _ (by omega)])
                  hpost (by omega)
                  (by rw [Array.set!_eq_setIfInBounds,
                        Array.size_setIfInBounds]
                      omega) stk₃ r₃
            rw [denotRep.eq_def] at hdr
            simp only [Option.pure_def, Option.bind_eq_bind] at hdr
            rw [runs_eff, heffloop]
            by_cases hlt : cnt < lo'
            · rw [if_pos hlt] at hdr ⊢
              simp only [Eff.judg]
              obtain ⟨taken, htaken, hdr⟩ := bind_some hdr
              obtain ⟨onward, honward, hdr⟩ := bind_some hdr
              cases hdr
              exact henter taken onward htaken honward stk' r'
            · rw [if_neg hlt] at hdr ⊢
              have hcw : cnt < none32 := by
                simp only [none32] at hwrap ⊢
                omega
              by_cases hhi : hi.any (fun x => decide (cnt ≥ x)) = true
              · rw [if_pos hhi] at hdr
                rw [if_pos ((hge cnt hcw).mpr hhi)]
                cases hdr
                simp only [Eff.judg, List.map_cons, List.map_nil,
                  List.cons_append, List.nil_append]
                exact (resumes_cons (t := ⟨pos', regs'⟩)).symm
              · rw [if_neg hhi] at hdr
                rw [if_neg (fun hc => hhi ((hge cnt hcw).mp hc))]
                obtain ⟨takenAll, hAll, hdr⟩ := bind_some hdr
                cases hdr
                obtain ⟨taken, htaken, hAll⟩ := bind_some hAll
                obtain ⟨onward, honward, hAll⟩ := bind_some hAll
                cases hAll
                cases greedy with
                | true =>
                    simp only [if_true, Eff.judg]
                    rw [henter taken onward htaken honward
                      ((j + 1, (⟨pos', regs'⟩ : Spec.Thread)) :: stk') r']
                    simp [List.map_append, List.append_assoc]
                | false =>
                    simp only [Bool.false_eq_true, if_false, Eff.judg]
                    rw [show Runs re s mo start attempt (j + 1) pos' regs'
                        ((lo + 2, (⟨pos', regs'⟩ : Spec.Thread)) :: stk') r' ↔
                        Resumes re s mo start attempt
                          ((j + 1, (⟨pos', regs'⟩ : Spec.Thread)) ::
                            (lo + 2, (⟨pos', regs'⟩ : Spec.Thread)) :: stk') r'
                        from (resumes_cons (t := ⟨pos', regs'⟩)).symm]
                    simp only [List.map_cons, List.cons_append]
                    exact resumes_congr_tail
                      (A := [(j + 1, (⟨pos', regs'⟩ : Spec.Thread))])
                      (fun r'' => by
                        rw [resumes_cons]
                        exact henter taken onward htaken honward stk' r'')
      -- The block starts by zeroing the count.
      have hd' : denotRep fuel (mctx re s mo) re.novec (re.novec + 2 * r0)
          (r0 + 1) body lo' hi greedy 0 pos
          (regs.set! (re.novec + 2 * r0) 0) = some ts := by
        rw [denot.eq_def] at hd
        cases hi with
        | none => exact hd
        | some k =>
            match k with
            | 0 => exact absurd rfl hnot0
            | 1 => exact absurd rfl hnot1
            | _ + 2 => exact hd
      have heff0 : eff re s mo start attempt lo pos regs =
          Eff.goto (lo + 1) pos (regs.set! (re.novec + 2 * r0) 0) := by
        simp only [eff, hzero, hslot]
      rw [runs_eff, heff0]
      simp only [Eff.judg]
      exact key fuel 0 pos (regs.set! (re.novec + 2 * r0) 0) ts hd'
        (by rw [Array.set!_eq_setIfInBounds, getBang_set_eq _ (by omega)]
            rfl)
        hpos (by omega)
        (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
            omega) stk r
  | @repOpt lo' greedy body r0 sp j hlo hsplit hbody ihbody =>
      intro fuel pos regs ts hd hpos hfuel hcaps hsize stk r
      rw [CapsBelow] at hcaps
      rw [repCount] at hsize
      have hlo' : (lo' == 1) = false := by simp [hlo]
      rw [denot.eq_def] at hd
      simp only [hlo', Bool.false_eq_true, if_false,
        Option.map_eq_some_iff] at hd
      obtain ⟨taken, htaken, rfl⟩ := hd
      have ihb := ihbody fuel pos regs taken htaken hpos hfuel hcaps hsize
      cases greedy with
      | true =>
          rw [if_pos rfl] at hsplit
          have heff : eff re s mo start attempt sp pos regs =
              .fork (sp + 1) j := by
            simp [eff, hsplit]
          rw [runs_eff, heff]
          simp only [Eff.judg]
          rw [ihb ((j, (⟨pos, regs⟩ : Spec.Thread)) :: stk) r]
          simp [List.map_append, List.append_assoc]
      | false =>
          rw [if_neg (by simp)] at hsplit
          have heff : eff re s mo start attempt sp pos regs =
              .fork j (sp + 1) := by
            simp [eff, hsplit]
          rw [runs_eff, heff]
          simp only [Eff.judg]
          rw [runs_congr_stack (L₂ :=
            ((taken.map fun t => (j, t)) ++ stk))
            (fun r' => by
              rw [resumes_cons]
              exact ihb stk r')]
          simp only [Bool.false_eq_true, if_false, List.map_cons,
            List.cons_append]
          exact (resumes_cons (t := ⟨pos, regs⟩)).symm

end Frag

/-! ## The compiler establishes the fragment relation

The discipline is the proto's, extended to the second table: `compileNode`
only appends code and patches cells it laid down itself, and it only ever
appends to the class table, 32 bytes at a time. `Grows` records exactly
that; the alternation chain keeps its strengthened jump-accumulator
statement. -/

private theorem getBang_push_lt {α : Type _} [Inhabited α] (a : Array α)
    (x : α) {i : Nat} (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h]
  exact Array.getElem_push_lt h

private theorem getBang_push_eq {α : Type _} [Inhabited α] (a : Array α)
    (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  exact Array.getElem_push_eq

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

private theorem getBang_append_left {α : Type _} [Inhabited α]
    (as bs : Array α) {j : Nat} (h : j < as.size) :
    (as ++ bs)[j]! = as[j]! := by
  rw [getElem!_pos (as ++ bs) j (by simp; omega), getElem!_pos as j h]
  exact Array.getElem_append_left h

private theorem getBang_append_right {α : Type _} [Inhabited α]
    (as bs : Array α) {j : Nat} (h : j < bs.size) :
    (as ++ bs)[as.size + j]! = bs[j]! := by
  rw [getElem!_pos (as ++ bs) _ (by simp; omega), getElem!_pos bs j h]
  rw [Array.getElem_append_right (by omega)]
  congr 1
  omega

/-- What compiling any construct does to the tables: code grows and keeps
its prefix, the class table grows by whole 32-byte rows and keeps its
prefix, and the repetition table follows the same append-only prefix
discipline — a counted repetition claims its row on the way in and only
ever patches that row's exit afterwards. -/
structure Grows (st st' : CState) : Prop where
  code_le : st.code.size ≤ st'.code.size
  code_pre : ∀ pc, pc < st.code.size → st'.code[pc]! = st.code[pc]!
  cls_le : st.classes.size ≤ st'.classes.size
  cls_pre : ∀ j, j < st.classes.size → st'.classes[j]! = st.classes[j]!
  cls_mod : st.classes.size % 32 = 0 → st'.classes.size % 32 = 0
  reps_le : st.reps.size ≤ st'.reps.size
  reps_pre : ∀ i, i < st.reps.size → st'.reps[i]! = st.reps[i]!

theorem Grows.refl (st : CState) : Grows st st :=
  ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, id,
   Nat.le_refl _, fun _ _ => rfl⟩

theorem Grows.comp {st₁ st₂ st₃ : CState}
    (h₁ : Grows st₁ st₂) (h₂ : Grows st₂ st₃) : Grows st₁ st₃ :=
  ⟨Nat.le_trans h₁.code_le h₂.code_le,
   fun pc hpc => (h₂.code_pre pc (by have := h₁.code_le; omega)).trans
     (h₁.code_pre pc hpc),
   Nat.le_trans h₁.cls_le h₂.cls_le,
   fun j hj => (h₂.cls_pre j (by have := h₁.cls_le; omega)).trans
     (h₁.cls_pre j hj),
   fun h => h₂.cls_mod (h₁.cls_mod h),
   Nat.le_trans h₁.reps_le h₂.reps_le,
   fun i hi => (h₂.reps_pre i (by have := h₁.reps_le; omega)).trans
     (h₁.reps_pre i hi)⟩

/-- A finished fragment survives the rest of the compilation. -/
theorem FragAt.grow {st st' : CState} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt st.code st.classes st.reps r0 a lo hi) (hg : Grows st st')
    (hhi : hi ≤ st.code.size) :
    FragAt st'.code st'.classes st'.reps r0 a lo hi :=
  h.mono (fun pc _ h2 => hg.code_pre pc (by omega)) hg.cls_le hg.cls_pre
    hg.reps_le hg.reps_pre

/-- A single emitted instruction: the cell lands at the old end. -/
private theorem emit_facts (st : CState) (i : Inst) :
    Grows st (emit st i).1 ∧
    (emit st i).1.code[st.code.size]! = i ∧
    (emit st i).1.code.size = st.code.size + 1 := by
  refine ⟨⟨?_, ?_, Nat.le_refl _, fun _ _ => rfl, id, Nat.le_refl _,
    fun _ _ => rfl⟩, ?_, ?_⟩
  · show st.code.size ≤ (st.code.push i).size
    simp
  · intro pc hpc
    exact getBang_push_lt st.code i hpc
  · exact getBang_push_eq st.code i
  · show (st.code.push i).size = st.code.size + 1
    simp

/-- The assertion family's emission, computed once for all ten. -/
private theorem compileNode_assn {a : Ast} {op : Op}
    (h : assnOp a = some op) (here : Nat) (st : CState) :
    compileNode a here st = (emit st ⟨op, 0, 0⟩).1 := by
  cases a <;> simp only [assnOp] at h <;> try cases h
  all_goals rw [compileNode]

/-- The state after an alternation's split is laid down and patched to
enter its branch. -/
private def altSplitSt (st : CState) : CState :=
  { st with code := ((st.code.push ⟨.split, 0, 0⟩).modify st.code.size
      (fun i => { i with arg := st.code.size + 1 })) }

/-- The branch region opened on top of it. -/
private def altBranchSt (inside : Nat) (st : CState) : CState :=
  { st with regions := (st.regions.push
      ⟨.branch, inside, st.code.size, st.code.size⟩) }

/-- The state right after a non-final branch's body. -/
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

/-- Patching a batch of collected jumps: only the named code cells move,
and every one of them gets the new target — idempotence makes duplicate
pcs harmless. -/
private theorem patchAll_facts (stop : Nat) :
    ∀ (js : List Nat) (st : CState),
      (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
        st).code.size = st.code.size ∧
      (∀ pc, pc ∉ js →
        (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
          st).code[pc]! = st.code[pc]!) ∧
      (∀ pc ∈ js, pc < st.code.size →
        (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
          st).code[pc]! = { st.code[pc]! with arg := stop }) ∧
      (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
        st).classes = st.classes ∧
      (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
        st).reps = st.reps
  | [], st => by simp
  | j :: js', st => by
      obtain ⟨hsz, hpre, hhit, hcls, hreps⟩ := patchAll_facts stop js'
        (patch st j fun i => { i with arg := stop })
      have hpsz : (patch st j fun i => { i with arg := stop }).code.size =
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
      · rw [List.foldl_cons, hcls]
        rfl
      · rw [List.foldl_cons, hreps]
        rfl

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
      | assn ha => simp [assnOp] at ha

/-- The alternation chain, with the jump-accumulator postcondition: every
collected jump cell ends pointing at the final stop, everything else
below the input size survives, and the new range is the chain's
fragment. -/
private theorem compileAlt_facts {n : Nat}
    (ih : ∀ {a : Ast}, sizeOf a ≤ n → Covered a →
      ∀ (here : Nat) (st : CState),
        Grows st (compileNode a here st) ∧
        (compileNode a here st).reps.size = st.reps.size + repCount a ∧
        (st.classes.size % 32 = 0 →
          FragAt (compileNode a here st).code (compileNode a here st).classes
            (compileNode a here st).reps st.reps.size
            a st.code.size (compileNode a here st).code.size)) :
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
        st.classes.size ≤ (compileAlt arm rest inside jumps st).classes.size ∧
        (∀ j, j < st.classes.size →
          (compileAlt arm rest inside jumps st).classes[j]! =
            st.classes[j]!) ∧
        (st.classes.size % 32 = 0 →
          (compileAlt arm rest inside jumps st).classes.size % 32 = 0) ∧
        st.reps.size ≤ (compileAlt arm rest inside jumps st).reps.size ∧
        (∀ i, i < st.reps.size →
          (compileAlt arm rest inside jumps st).reps[i]! = st.reps[i]!) ∧
        (compileAlt arm rest inside jumps st).reps.size =
          st.reps.size + repCount (.alt (arm :: rest)) ∧
        (st.classes.size % 32 = 0 →
          FragAt (compileAlt arm rest inside jumps st).code
            (compileAlt arm rest inside jumps st).classes
            (compileAlt arm rest inside jumps st).reps st.reps.size
            (.alt (arm :: rest)) st.code.size
            (compileAlt arm rest inside jumps st).code.size) := by
  intro rest
  induction rest with
  | nil =>
      intro arm hszarm hcarm _ inside jumps st hj
      obtain ⟨hg, hgrsz, hfrag⟩ :=
        ih hszarm hcarm st.regions.size (altBranchSt inside st)
      -- Restated on `st`'s own tables: `altBranchSt` only touches regions,
      -- so these are the same facts read through definitional equalities.
      have hgle : st.code.size ≤
          (compileNode arm st.regions.size
            (altBranchSt inside st)).code.size := hg.code_le
      have hgpre : ∀ pc, pc < st.code.size →
          (compileNode arm st.regions.size
            (altBranchSt inside st)).code[pc]! = st.code[pc]! := hg.code_pre
      have hgcle : st.classes.size ≤
          (compileNode arm st.regions.size
            (altBranchSt inside st)).classes.size := hg.cls_le
      have hgcpre : ∀ j, j < st.classes.size →
          (compileNode arm st.regions.size
            (altBranchSt inside st)).classes[j]! = st.classes[j]! :=
        hg.cls_pre
      have hgcmod : st.classes.size % 32 = 0 →
          (compileNode arm st.regions.size
            (altBranchSt inside st)).classes.size % 32 = 0 := hg.cls_mod
      have hgrle : st.reps.size ≤ (compileNode arm st.regions.size
          (altBranchSt inside st)).reps.size := hg.reps_le
      have hgrpre : ∀ i, i < st.reps.size →
          (compileNode arm st.regions.size
            (altBranchSt inside st)).reps[i]! = st.reps[i]! := hg.reps_pre
      have hgrsz' : (compileNode arm st.regions.size
          (altBranchSt inside st)).reps.size =
          st.reps.size + repCount arm := hgrsz
      have hfrag' : st.classes.size % 32 = 0 →
          FragAt (compileNode arm st.regions.size (altBranchSt inside st)).code
            (compileNode arm st.regions.size (altBranchSt inside st)).classes
            (compileNode arm st.regions.size (altBranchSt inside st)).reps
            st.reps.size arm st.code.size
            (compileNode arm st.regions.size
              (altBranchSt inside st)).code.size := hfrag
      obtain ⟨hfsz, hfpre, hfhit, hfcls, hfreps⟩ :=
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
      have hclasses : (compileAlt arm [] inside jumps st).classes =
          (compileNode arm st.regions.size (altBranchSt inside st)).classes := by
        rw [compileAlt_nil_eq, ← Array.foldl_toList]
        exact hfcls
      have hreps : (compileAlt arm [] inside jumps st).reps =
          (compileNode arm st.regions.size (altBranchSt inside st)).reps := by
        rw [compileAlt_nil_eq, ← Array.foldl_toList]
        exact hfreps
      have hsize : (compileAlt arm [] inside jumps st).code.size =
          (compileNode arm st.regions.size
            (altBranchSt inside st)).code.size := by
        rw [hcode, hfsz]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsize]; exact hgle
      · intro pc hpc hnotin
        rw [hcode, hfpre pc hnotin]
        exact hgpre pc hpc
      · intro p hp
        have hplt := hj p hp
        rw [hcode, hfhit p hp (by omega), hgpre p hplt, hfsz]
      · rw [hclasses]; exact hgcle
      · intro j hjlt
        rw [hclasses]
        exact hgcpre j hjlt
      · intro hmod
        rw [hclasses]
        exact hgcmod hmod
      · rw [hreps]; exact hgrle
      · intro i hi
        rw [hreps]
        exact hgrpre i hi
      · rw [hreps, hgrsz', repCount_alt_cons arm [], repCount_alt_nil]
        omega
      · intro hmod
        rw [hsize, hclasses, hreps]
        refine .altOne ((hfrag' hmod).mono ?_ (Nat.le_refl _) (fun _ _ => rfl)
          (Nat.le_refl _) fun _ _ => rfl)
        intro pc h1 h2
        rw [hcode]
        exact hfpre pc fun hin => absurd (hj pc hin) (by omega)
  | cons bb rest' ihrest =>
      intro arm hszarm hcarm helems inside jumps st hj
      rw [compileAlt_cons_eq]
      have hsplitsz : (altSplitSt st).code.size = st.code.size + 1 := by
        simp [altSplitSt]
      obtain ⟨hg, hgrsz, hfrag⟩ :=
        ih hszarm hcarm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st))
      have hmid : compileNode arm (altSplitSt st).regions.size
            (altBranchSt inside (altSplitSt st)) = altMid arm inside st := rfl
      rw [hmid] at hg hgrsz hfrag
      -- Restated on `st`'s own tables, the split's one-cell growth folded
      -- into the bounds.
      have hgle : (altSplitSt st).code.size ≤
          (altMid arm inside st).code.size := hg.code_le
      have hgpre : ∀ pc, pc < (altSplitSt st).code.size →
          (altMid arm inside st).code[pc]! = (altSplitSt st).code[pc]! :=
        hg.code_pre
      rw [hsplitsz] at hgle hgpre
      have hgcle : st.classes.size ≤ (altMid arm inside st).classes.size :=
        hg.cls_le
      have hgcpre : ∀ j, j < st.classes.size →
          (altMid arm inside st).classes[j]! = st.classes[j]! := hg.cls_pre
      have hgcmod : st.classes.size % 32 = 0 →
          (altMid arm inside st).classes.size % 32 = 0 := hg.cls_mod
      have hgrle : st.reps.size ≤ (altMid arm inside st).reps.size := hg.reps_le
      have hgrpre : ∀ i, i < st.reps.size →
          (altMid arm inside st).reps[i]! = st.reps[i]! := hg.reps_pre
      have hgrsz' : (altMid arm inside st).reps.size =
          st.reps.size + repCount arm := hgrsz
      have hfrag' : st.classes.size % 32 = 0 →
          FragAt (altMid arm inside st).code (altMid arm inside st).classes
            (altMid arm inside st).reps st.reps.size
            arm (altSplitSt st).code.size (altMid arm inside st).code.size :=
        hfrag
      rw [hsplitsz] at hfrag'
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
      have houtc : (altOut arm inside st).code =
          ((altMid arm inside st).code.push ⟨.jump, 0, 0⟩).modify st.code.size
            (fun i => { i with
              alt := ((altMid arm inside st).code.push ⟨.jump, 0, 0⟩).size }) :=
        rfl
      have houtcl : (altOut arm inside st).classes =
          (altMid arm inside st).classes := rfl
      have houtr : (altOut arm inside st).reps =
          (altMid arm inside st).reps := rfl
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
          getBang_push_lt _ _ (by omega),
          hgpre st.code.size (by omega), hsplit_cell]
        simp
      have hout_pre : ∀ pc, pc < (altMid arm inside st).code.size →
          pc ≠ st.code.size →
          (altOut arm inside st).code[pc]! =
            (altMid arm inside st).code[pc]! := by
        intro pc hpc hne
        rw [houtc, getBang_modify_ne _ st.code.size hne,
          getBang_push_lt _ _ hpc]
      obtain ⟨hszbb, hcbb⟩ := helems bb (List.mem_cons_self ..)
      obtain ⟨cle, cpre, chit, ccle, ccpre, ccmod, crle, crpre, crsz, cfrag⟩ :=
        ihrest bb hszbb hcbb
          (fun x hx => helems x (List.mem_cons_of_mem bb hx))
          inside (jumps.push (altMid arm inside st).code.size)
          (altOut arm inside st)
          (by
            intro p hp
            rw [Array.toList_push] at hp
            rcases List.mem_append.mp hp with hp' | hp'
            · have := hj p hp'
              rw [houtsz]
              omega
            · rw [List.mem_singleton] at hp'
              rw [houtsz]
              omega)
      rw [houtsz] at cle cpre cfrag
      rw [houtcl] at ccle ccpre ccmod cfrag
      rw [houtr] at crle crpre crsz cfrag
      rw [hgrsz'] at cfrag
      have hmem_push : ∀ p,
          p ∈ (jumps.push (altMid arm inside st).code.size).toList ↔
          (p ∈ jumps.toList ∨ p = (altMid arm inside st).code.size) := by
        intro p
        rw [Array.toList_push, List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · intro pc hpc hnotin
        rw [cpre pc (by omega) (by
              rw [hmem_push]
              rintro (h' | rfl)
              · exact hnotin h'
              · omega),
          hout_pre pc (by omega) (by omega), hgpre pc (by omega),
          hsplit_pre pc hpc]
      · intro p hp
        have hplt := hj p hp
        have hcell := chit p ((hmem_push p).mpr (.inl hp))
        rw [hcell, hout_pre p (by omega) (by omega),
          hgpre p (by omega), hsplit_pre p hplt]
      · exact Nat.le_trans hgcle ccle
      · intro j hjlt
        rw [ccpre j (by omega), hgcpre j hjlt]
      · intro hmod
        exact ccmod (hgcmod hmod)
      · exact Nat.le_trans hgrle crle
      · intro i hi
        rw [crpre i (by omega), hgrpre i hi]
      · rw [crsz, hgrsz', repCount_alt_cons arm (bb :: rest')]
        omega
      · intro hmod
        refine .altCons (j := (altMid arm inside st).code.size) ?_ ?_ ?_ ?_
        · rw [cpre st.code.size (by omega) (by
              rw [hmem_push]
              rintro (h' | h')
              · have := hj st.code.size h'; omega
              · omega)]
          exact hout_split
        · refine ((hfrag' hmod).mono ?_ ?_ ?_ ?_ ?_)
          · intro pc h1 h2
            rw [cpre pc (by omega) (by
                  rw [hmem_push]
                  rintro (h' | h')
                  · have := hj pc h'; omega
                  · omega),
              hout_pre pc (by omega) (by omega)]
          · exact ccle
          · exact ccpre
          · exact crle
          · exact crpre
        · have hcell := chit (altMid arm inside st).code.size
            ((hmem_push (altMid arm inside st).code.size).mpr (.inr rfl))
          rw [hcell, hout_jump]
        · exact cfrag (hgcmod hmod)

/-- Growth by table equality: a step that only touches regions. -/
private theorem grows_of_eq {st st' : CState} (hc : st'.code = st.code)
    (hcl : st'.classes = st.classes) (hr : st'.reps = st.reps) :
    Grows st st' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    exact Nat.le_refl _
  · intro pc _
    rw [hc]
  · rw [hcl]
    exact Nat.le_refl _
  · intro j _
    rw [hcl]
  · intro hmod
    rw [hcl]
    exact hmod
  · rw [hr]
    exact Nat.le_refl _
  · intro i _
    rw [hr]

/-- The state after a group's region opens. -/
private def grpSt (here : Nat) (st : CState) : CState :=
  { st with regions := (st.regions.push
      ⟨.group, here, st.code.size, st.code.size⟩) }

private theorem dropEmptyRegion_tables (st : CState) (at_ : Nat) :
    (dropEmptyRegion st at_).code = st.code ∧
    (dropEmptyRegion st at_).classes = st.classes ∧
    (dropEmptyRegion st at_).reps = st.reps := by
  rw [dropEmptyRegion]
  split
  · split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- Closing a region leaves every table alone. -/
private theorem closeRegion_tables (st : CState) (at_ : Nat) :
    (closeRegion st at_).code = st.code ∧
    (closeRegion st at_).classes = st.classes ∧
    (closeRegion st at_).reps = st.reps :=
  ⟨rfl, rfl, rfl⟩

/-- Closing and possibly dropping a region leaves every table alone. -/
private theorem finish_tables (st4 : CState) (at_ : Nat) :
    (dropEmptyRegion (closeRegion st4 at_) at_).code = st4.code ∧
    (dropEmptyRegion (closeRegion st4 at_) at_).classes = st4.classes ∧
    (dropEmptyRegion (closeRegion st4 at_) at_).reps = st4.reps :=
  dropEmptyRegion_tables (closeRegion st4 at_) at_

private theorem compileNode_grp_pos {cap : Nat} (body : Ast) (here : Nat)
    (st : CState) (hcap : (cap != 0) = true) :
    compileNode (.grp cap body) here st =
      dropEmptyRegion (closeRegion
        ((emit (compileNode body st.regions.size
          ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1))
          ⟨.save, 2 * cap + 1, 0⟩).1) st.regions.size) st.regions.size := by
  rw [compileNode]
  simp only [hcap, if_true]
  rfl

private theorem compileNode_grp_zero (body : Ast) (here : Nat)
    (st : CState) :
    compileNode (.grp 0 body) here st =
      dropEmptyRegion (closeRegion
        (compileNode body st.regions.size (grpSt here st))
        st.regions.size) st.regions.size := by
  rw [compileNode]
  rfl

/-- The state after an optional item's region opens and its split is laid
down, still blank. -/
private def repOptSt (here : Nat) (st : CState) : CState :=
  { st with
    regions := (st.regions.push
      ⟨.«repeat», here, st.code.size, st.code.size⟩)
    code := (st.code.push ⟨.split, 0, 0⟩) }

private theorem compileNode_repOpt_eq {lo : Nat} (greedy : Bool)
    (body : Ast) (here : Nat) (st : CState) (hlo : (lo == 1) = false) :
    compileNode (.rep lo (some 1) greedy body) here st =
      closeRegion
        (patch (compileNode body st.regions.size (repOptSt here st))
          st.code.size
          (fun i => if greedy then
            { i with
              arg := st.code.size + 1
              alt := (compileNode body st.regions.size
                (repOptSt here st)).code.size }
          else
            { i with
              arg := (compileNode body st.regions.size
                (repOptSt here st)).code.size
              alt := st.code.size + 1 }))
        st.regions.size := by
  rw [compileNode]
  simp only [hlo, Bool.false_eq_true, if_false]
  rfl

/-- The state a counted repetition reaches on the way in: its region is
open, the three control cells are down and the row it will run on is
claimed — with the exit still blank, since nobody knows yet where the
block ends. -/
private def repGenSt (lo' : Nat) (hi : Option Nat) (greedy : Bool)
    (here : Nat) (st : CState) : CState :=
  { st with
    regions := (st.regions.push
      ⟨.«repeat», here, st.code.size, st.code.size⟩)
    code := (((st.code.push ⟨.repZero, st.reps.size, 0⟩).push
      ⟨.repLoop, st.reps.size, 0⟩).push ⟨.repEnter, st.reps.size, 0⟩)
    reps := (st.reps.push ⟨lo', hiCode hi, greedy,
      st.code.size + 1, st.code.size + 2, 0⟩) }

/-- What the way in costs: three cells and one row. -/
private theorem repGenSt_facts (lo' : Nat) (hi : Option Nat) (greedy : Bool)
    (here : Nat) (st : CState) :
    Grows st (repGenSt lo' hi greedy here st) ∧
    (repGenSt lo' hi greedy here st).code.size = st.code.size + 3 ∧
    (repGenSt lo' hi greedy here st).code[st.code.size]! =
      ⟨.repZero, st.reps.size, 0⟩ ∧
    (repGenSt lo' hi greedy here st).code[st.code.size + 1]! =
      ⟨.repLoop, st.reps.size, 0⟩ ∧
    (repGenSt lo' hi greedy here st).code[st.code.size + 2]! =
      ⟨.repEnter, st.reps.size, 0⟩ ∧
    (repGenSt lo' hi greedy here st).reps.size = st.reps.size + 1 ∧
    (repGenSt lo' hi greedy here st).reps[st.reps.size]! =
      ⟨lo', hiCode hi, greedy, st.code.size + 1, st.code.size + 2, 0⟩ := by
  have hsz1 : (st.code.push ⟨.repZero, st.reps.size, 0⟩).size =
      st.code.size + 1 := by simp
  have hsz2 : ((st.code.push ⟨.repZero, st.reps.size, 0⟩).push
      ⟨.repLoop, st.reps.size, 0⟩).size = st.code.size + 2 := by simp
  have hcode : (repGenSt lo' hi greedy here st).code =
      ((st.code.push ⟨.repZero, st.reps.size, 0⟩).push
        ⟨.repLoop, st.reps.size, 0⟩).push
        ⟨.repEnter, st.reps.size, 0⟩ := rfl
  have hcls : (repGenSt lo' hi greedy here st).classes = st.classes := rfl
  have hrsz : (repGenSt lo' hi greedy here st).reps.size =
      st.reps.size + 1 := by
    simp [repGenSt]
  have hpre : ∀ pc, pc < st.code.size →
      (repGenSt lo' hi greedy here st).code[pc]! = st.code[pc]! := by
    intro pc hpc
    rw [hcode, getBang_push_lt _ _ (by rw [hsz2]; omega),
      getBang_push_lt _ _ (by rw [hsz1]; omega), getBang_push_lt _ _ hpc]
  refine ⟨⟨?_, hpre, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hrsz, ?_⟩
  · rw [hcode]
    simp only [Array.size_push]
    omega
  · rw [hcls]
    exact Nat.le_refl _
  · intro j _
    rw [hcls]
  · intro hmod
    rw [hcls]
    exact hmod
  · omega
  · intro i hi'
    exact getBang_push_lt _ _ hi'
  · rw [hcode]
    simp only [Array.size_push]
  · rw [hcode, getBang_push_lt _ _ (by rw [hsz2]; omega),
      getBang_push_lt _ _ (by rw [hsz1]; omega)]
    exact getBang_push_eq _ _
  · rw [hcode, getBang_push_lt _ _ (by rw [hsz2]; omega), ← hsz1]
    exact getBang_push_eq _ _
  · rw [hcode, ← hsz2]
    exact getBang_push_eq _ _
  · exact getBang_push_eq _ _

/-- The state a counted repetition leaves: the RepNext cell goes down and
the claimed row learns where the block ends. -/
private def repGenOut (r : Nat) (st : CState) : CState :=
  let out := (emit st ⟨.repNext, r, 0⟩).1
  { out with
    reps := (out.reps.modify r (fun rr => { rr with after := out.code.size })) }

/-- What the way out costs: one cell, and one row rewritten. -/
private theorem repGenOut_facts (r : Nat) (st : CState)
    (hr : r < st.reps.size) :
    (repGenOut r st).code.size = st.code.size + 1 ∧
    (∀ pc, pc < st.code.size →
      (repGenOut r st).code[pc]! = st.code[pc]!) ∧
    (repGenOut r st).code[st.code.size]! = ⟨.repNext, r, 0⟩ ∧
    (repGenOut r st).classes = st.classes ∧
    (repGenOut r st).reps.size = st.reps.size ∧
    (∀ i, i ≠ r → (repGenOut r st).reps[i]! = st.reps[i]!) ∧
    (repGenOut r st).reps[r]! =
      { st.reps[r]! with after := st.code.size + 1 } := by
  have hcode : (repGenOut r st).code = st.code.push ⟨.repNext, r, 0⟩ := rfl
  have hreps : (repGenOut r st).reps =
      st.reps.modify r (fun rr => { rr with after := st.code.size + 1 }) := by
    show (st.reps.modify r (fun rr =>
      { rr with after := (st.code.push ⟨.repNext, r, 0⟩).size })) = _
    simp
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hcode]
    simp
  · intro pc hpc
    rw [hcode]
    exact getBang_push_lt _ _ hpc
  · rw [hcode]
    exact getBang_push_eq _ _
  · rw [hreps]
    simp
  · intro i hi
    rw [hreps]
    exact getBang_modify_ne _ _ hi
  · rw [hreps]
    exact getBang_modify_eq _ _ hr

private theorem compileNode_repGen_eq {lo' : Nat} {hi : Option Nat}
    (greedy : Bool) (body : Ast) (here : Nat) (st : CState)
    (hnot0 : hi ≠ some 0) (hnot1 : hi ≠ some 1) :
    compileNode (.rep lo' hi greedy body) here st =
      closeRegion
        (repGenOut st.reps.size
          (compileNode body st.regions.size (repGenSt lo' hi greedy here st)))
        st.regions.size := by
  rw [compileNode.eq_def]
  match hi, hnot0, hnot1 with
  | none, _, _ => simp [repGenSt, repGenOut, emit, openRegion, hiCode]
  | some 0, h, _ => exact absurd rfl h
  | some 1, _, h => exact absurd rfl h
  | some (k + 2), _, _ => simp [repGenSt, repGenOut, emit, openRegion, hiCode]

/-- Compiling a covered node: the tables grow by the `Grows` discipline,
and — as long as the class table arrived row-aligned — the new code range
is a fragment of the node. -/
theorem compileNode_facts :
    ∀ (n : Nat) {a : Ast}, sizeOf a ≤ n → Covered a →
    ∀ (here : Nat) (st : CState),
      Grows st (compileNode a here st) ∧
      (compileNode a here st).reps.size = st.reps.size + repCount a ∧
      (st.classes.size % 32 = 0 →
        FragAt (compileNode a here st).code (compileNode a here st).classes
          (compileNode a here st).reps st.reps.size a
          st.code.size (compileNode a here st).code.size) := by
  intro n
  induction n with
  | zero =>
      intro a hsz hc
      exfalso
      cases hc with
      | assn ha => cases a <;> simp [assnOp] at ha ⊢ <;> simp_all
      | _ => simp_all
  | succ n ih =>
      intro a hsz hc here st
      -- One shared script for every single-emit leaf.
      have leaf : ∀ (i : Inst),
          Grows st (emit st i).1 ∧
          (emit st i).1.code[st.code.size]! = i ∧
          (emit st i).1.code.size = st.code.size + 1 := emit_facts st
      cases hc with
      | nul =>
          have hstep : compileNode .nul here st = st := by rw [compileNode]
          rw [hstep]
          exact ⟨Grows.refl st, by simp [repCount], fun _ => .nul⟩
      | chr b =>
          have hstep : compileNode (.chr b) here st =
              (emit st ⟨.chr, b.toNat, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.chr, b.toNat, 0⟩
          rw [hstep]
          exact ⟨hg, by simp [repCount, emit], fun _ => hsz' ▸ .chr hcell⟩
      | chrCI folded =>
          have hstep : compileNode (.chrCI folded) here st =
              (emit st ⟨.chrCI, folded.toNat, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.chrCI, folded.toNat, 0⟩
          rw [hstep]
          exact ⟨hg, by simp [repCount, emit], fun _ => hsz' ▸ .chrCI hcell⟩
      | any =>
          have hstep : compileNode .any here st =
              (emit st ⟨.any, 0, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.any, 0, 0⟩
          rw [hstep]
          exact ⟨hg, by simp [repCount, emit], fun _ => hsz' ▸ .any hcell⟩
      | anyNoNL =>
          have hstep : compileNode .anyNoNL here st =
              (emit st ⟨.anyNoNL, 0, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.anyNoNL, 0, 0⟩
          rw [hstep]
          exact ⟨hg, by simp [repCount, emit],
            fun _ => hsz' ▸ .anyNoNL hcell⟩
      | bsr =>
          have hstep : compileNode .bsr here st =
              (emit st ⟨.bsr, 0, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.bsr, 0, 0⟩
          rw [hstep]
          exact ⟨hg, by simp [repCount, emit], fun _ => hsz' ▸ .bsr hcell⟩
      | @assn a' op ha =>
          have hstep := compileNode_assn ha here st
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨op, 0, 0⟩
          rw [hstep]
          exact ⟨hg, by simp [repCount_assn ha, emit],
            fun _ => hsz' ▸ .assn ha hcell⟩
      | cls bits =>
          have hstep : compileNode (.cls bits) here st =
              (emit { st with classes := st.classes ++ bits.toArray }
                ⟨.cls, st.classes.size / 32, 0⟩).1 := by
            rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ :=
            emit_facts { st with classes := st.classes ++ bits.toArray }
              ⟨.cls, st.classes.size / 32, 0⟩
          rw [hstep]
          refine ⟨?_, by simp [repCount, emit], ?_⟩
          · refine Grows.comp
              (st₂ := { st with classes := st.classes ++ bits.toArray })
              ⟨Nat.le_refl _, fun _ _ => rfl, ?_, ?_, ?_, Nat.le_refl _,
                fun _ _ => rfl⟩ hg
            · show st.classes.size ≤ (st.classes ++ bits.toArray).size
              simp
            · intro j hj
              exact getBang_append_left st.classes bits.toArray hj
            · intro hmod
              show (st.classes ++ bits.toArray).size % 32 = 0
              simp
              omega
          · intro hmod
            rw [hsz']
            have hdvd : st.classes.size / 32 * 32 = st.classes.size := by
              omega
            refine .cls hcell ?_ ?_
            · have : (emit { st with classes := st.classes ++ bits.toArray }
                  ⟨.cls, st.classes.size / 32, 0⟩).1.classes =
                  st.classes ++ bits.toArray := rfl
              rw [this]
              simp
              omega
            · intro b
              have hclasses : (emit { st with
                  classes := st.classes ++ bits.toArray }
                  ⟨.cls, st.classes.size / 32, 0⟩).1.classes =
                  st.classes ++ bits.toArray := rfl
              rw [hclasses, hdvd, getBang_append_right st.classes bits.toArray
                (by simp; exact shr3_lt b)]
              show (bits.toArray[(b >>> 3).toNat]! &&& (1 <<< (b &&& 7)) != 0) =
                bits.has b
              rw [ClassBits.has]
              congr 1
              rw [getElem!_pos bits.toArray _ (by simp; exact shr3_lt b),
                getElem!_pos bits _ (shr3_lt b), Vector.getElem_toArray]
      | catNil =>
          have hstep : compileNode (.cat []) here st = st := by
            rw [compileNode, compileCat]
          rw [hstep]
          exact ⟨Grows.refl st, by rw [repCount_cat_nil]; omega,
            fun _ => .catNil⟩
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
          obtain ⟨hg1, hr1, hfrag1⟩ := ih hszk.1 hck here st
          obtain ⟨hg2, hr2, hfrag2⟩ :=
            ih hszk.2 hckids here (compileNode k here st)
          rw [hstep]
          refine ⟨Grows.comp hg1 hg2, ?_, ?_⟩
          · rw [hr2, hr1, repCount_cat_cons]
            omega
          · intro hmod
            refine .catCons ((hfrag1 hmod).grow hg2 (Nat.le_refl _)) ?_
            rw [← hr1]
            exact hfrag2 (hg1.cls_mod hmod)
      | @altOne a1 hca =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have hstep : compileNode (.alt [a1]) here st =
              compileNode a1 here st := by
            rw [compileNode]
          obtain ⟨hg, hr, hfrag⟩ := ih hsza hca here st
          rw [hstep]
          refine ⟨hg, ?_, fun hmod => .altOne (hfrag hmod)⟩
          rw [hr, repCount_alt_cons, repCount_alt_nil]
          omega
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
          obtain ⟨h1, h2, _, h4, h5, h6, h7, h7', h7'', h8⟩ :=
            compileAlt_facts (fun h hc => ih h hc) (b :: rest) a1 hsza hca
              helems st.regions.size #[]
              { st with regions := (st.regions.push
                  ⟨.alt, here, st.code.size, st.code.size⟩) }
              (by simp)
          rw [hstep]
          refine ⟨⟨h1, fun pc hpc => h2 pc hpc (by simp), h4, h5, h6, h7, h7'⟩,
            h7'', ?_⟩
          intro hmod
          exact h8 hmod
      | @grp cap body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          by_cases hcap : (cap != 0) = true
          · rw [compileNode_grp_pos body here st hcap]
            obtain ⟨hgo, hocell, hosz⟩ :=
              emit_facts (grpSt here st) ⟨.save, 2 * cap, 0⟩
            obtain ⟨hgb, hrb, hfragb⟩ := ih hszb hcbody st.regions.size
              ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1)
            obtain ⟨hgc, hccell, hcsz⟩ :=
              emit_facts (compileNode body st.regions.size
                ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1))
                ⟨.save, 2 * cap + 1, 0⟩
            obtain ⟨hdc, hdcl, hdr⟩ := finish_tables
              ((emit (compileNode body st.regions.size
                ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1))
                ⟨.save, 2 * cap + 1, 0⟩).1) st.regions.size
            -- Read through the region-only steps.
            have hosz' : (emit (grpSt here st)
                ⟨.save, 2 * cap, 0⟩).1.code.size = st.code.size + 1 := hosz
            have hocell' : (emit (grpSt here st)
                ⟨.save, 2 * cap, 0⟩).1.code[st.code.size]! =
                ⟨.save, 2 * cap, 0⟩ := hocell
            rw [hosz'] at hfragb
            have hfragb' : st.classes.size % 32 = 0 →
                FragAt (compileNode body st.regions.size
                    ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1)).code
                  (compileNode body st.regions.size
                    ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1)).classes
                  (compileNode body st.regions.size
                    ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1)).reps
                  st.reps.size body (st.code.size + 1)
                  (compileNode body st.regions.size
                    ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1)).code.size :=
              hfragb
            have hgo' : Grows st (emit (grpSt here st)
                ⟨.save, 2 * cap, 0⟩).1 :=
              Grows.comp
                (grows_of_eq (st := st) (st' := grpSt here st) rfl rfl rfl)
                hgo
            have hbodyle := hgb.code_le
            rw [hosz'] at hbodyle
            refine ⟨?_, ?_, ?_⟩
            · exact Grows.comp hgo'
                (Grows.comp hgb (Grows.comp hgc
                  (grows_of_eq hdc hdcl hdr)))
            · rw [hdr, repCount]
              exact hrb
            · intro hmod
              rw [hdc, hdcl, hdr, hcsz]
              refine .grpCap (by simpa using hcap) ?_ ?_ ?_
              · have h1 : (emit (compileNode body st.regions.size
                    ((emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1))
                    ⟨.save, 2 * cap + 1, 0⟩).1.code[st.code.size]! =
                    (compileNode body st.regions.size
                      ((emit (grpSt here st)
                        ⟨.save, 2 * cap, 0⟩).1)).code[st.code.size]! :=
                  getBang_push_lt _ _ (by omega)
                rw [h1, hgb.code_pre st.code.size (by rw [hosz']; omega),
                  hocell']
              · exact (hfragb' hmod).grow hgc (Nat.le_refl _)
              · exact hccell
          · have hcap0 : cap = 0 := by simpa using hcap
            subst hcap0
            rw [compileNode_grp_zero body here st]
            obtain ⟨hgb, hrb, hfragb⟩ :=
              ih hszb hcbody st.regions.size (grpSt here st)
            obtain ⟨hdc, hdcl, hdr⟩ := finish_tables
              (compileNode body st.regions.size (grpSt here st))
              st.regions.size
            have hfragb' : st.classes.size % 32 = 0 →
                FragAt (compileNode body st.regions.size (grpSt here st)).code
                  (compileNode body st.regions.size (grpSt here st)).classes
                  (compileNode body st.regions.size (grpSt here st)).reps
                  st.reps.size body st.code.size
                  (compileNode body st.regions.size
                    (grpSt here st)).code.size := hfragb
            refine ⟨?_, ?_, ?_⟩
            · exact Grows.comp
                (grows_of_eq (st := st) (st' := grpSt here st) rfl rfl rfl)
                (Grows.comp hgb (grows_of_eq hdc hdcl hdr))
            · rw [hdr, repCount]
              exact hrb
            · intro hmod
              rw [hdc, hdcl, hdr]
              exact .grpZero (hfragb' hmod)
      | @repNone lo greedy body =>
          have hstep : compileNode (.rep lo (some 0) greedy body) here st =
              st := by
            rw [compileNode]
          rw [hstep]
          exact ⟨Grows.refl st, by rw [repCount]; omega, fun _ => .repNone⟩
      | @repOne greedy body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hstep : compileNode (.rep 1 (some 1) greedy body) here st =
              compileNode body here st := by
            rw [compileNode]
            simp
          obtain ⟨hg, hr, hfrag⟩ := ih hszb hcbody here st
          rw [hstep]
          refine ⟨hg, ?_, fun hmod => .repOne (hfrag hmod)⟩
          rw [hr, repCount]
      | @repGen lo hi greedy body hnot0 hnot1 hbound hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          -- The two side conditions are what picks `repCount`'s last arm.
          have hcnt :
              repCount (.rep lo hi greedy body) = 1 + repCount body := by
            rw [repCount]
            · exact hnot0
            · exact hnot1
          obtain ⟨hgs, hscode, hszero, hsloop, hsenter, hsreps, hsrow⟩ :=
            repGenSt_facts lo hi greedy here st
          obtain ⟨hgb, hrb, hfragb⟩ :=
            ih hszb hcbody st.regions.size (repGenSt lo hi greedy here st)
          obtain ⟨hocode, hopre, honext, hocls, horeps, horest, horow⟩ :=
            repGenOut_facts st.reps.size
              (compileNode body st.regions.size (repGenSt lo hi greedy here st))
              (by have := hgb.reps_le; omega)
          obtain ⟨hfc, hfcl, hfr⟩ :=
            closeRegion_tables (repGenOut st.reps.size
              (compileNode body st.regions.size
                (repGenSt lo hi greedy here st))) st.regions.size
          -- The body sits above the three control cells and its own row.
          have hble : st.code.size + 3 ≤ (compileNode body st.regions.size
              (repGenSt lo hi greedy here st)).code.size := by
            have := hgb.code_le
            omega
          have hbrle : st.reps.size + 1 ≤ (compileNode body st.regions.size
              (repGenSt lo hi greedy here st)).reps.size := by
            have := hgb.reps_le
            omega
          have hgf : Grows st (repGenOut st.reps.size
              (compileNode body st.regions.size
                (repGenSt lo hi greedy here st))) := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hocode]
              omega
            · intro pc hpc
              rw [hopre pc (by omega), hgb.code_pre pc (by omega)]
              exact hgs.code_pre pc hpc
            · rw [hocls]
              exact Nat.le_trans hgs.cls_le hgb.cls_le
            · intro j hj
              rw [hocls, hgb.cls_pre j (by have := hgs.cls_le; omega)]
              exact hgs.cls_pre j hj
            · intro hmod
              rw [hocls]
              exact hgb.cls_mod (hgs.cls_mod hmod)
            · rw [horeps]
              exact Nat.le_trans hgs.reps_le hgb.reps_le
            · intro i hi'
              rw [horest i (by omega), hgb.reps_pre i (by omega)]
              exact hgs.reps_pre i hi'
          rw [compileNode_repGen_eq greedy body here st hnot0 hnot1]
          refine ⟨Grows.comp hgf (grows_of_eq hfc hfcl hfr), ?_, ?_⟩
          · rw [hfr, horeps, hrb, hsreps, hcnt]
            omega
          · intro hmod
            rw [hfc, hfcl, hfr, hocode]
            refine .repGen ?_ ?_ ?_ honext ?_ ?_ hbound hnot0 hnot1 ?_
            · rw [hopre st.code.size (by omega),
                hgb.code_pre st.code.size (by omega)]
              exact hszero
            · rw [hopre (st.code.size + 1) (by omega),
                hgb.code_pre (st.code.size + 1) (by omega)]
              exact hsloop
            · rw [hopre (st.code.size + 2) (by omega),
                hgb.code_pre (st.code.size + 2) (by omega)]
              exact hsenter
            · rw [horeps]
              omega
            · rw [horow, (hgb.reps_pre st.reps.size (by omega)).trans hsrow]
            · have hfragb' := hfragb (hgs.cls_mod hmod)
              rw [hsreps, hscode] at hfragb'
              refine (hfragb'.mono (fun pc _ h2 => hopre pc h2) ?_ ?_
                  (Nat.le_refl _) (fun _ _ => rfl)).patchBelow
                (Nat.le_of_eq horeps.symm) (fun i h1 _ => horest i (by omega))
              · rw [hocls]
                exact Nat.le_refl _
              · intro j _
                rw [hocls]
      | @repOpt lo greedy body hlo hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hlo' : (lo == 1) = false := by simp [hlo]
          rw [compileNode_repOpt_eq greedy body here st hlo']
          have hrsz : (repOptSt here st).code.size = st.code.size + 1 := by
            simp [repOptSt]
          obtain ⟨hg, hr, hfrag⟩ :=
            ih hszb hcbody st.regions.size (repOptSt here st)
          have hgle : st.code.size + 1 ≤
              (compileNode body st.regions.size
                (repOptSt here st)).code.size := by
            have h1 := hg.code_le
            rw [hrsz] at h1
            exact h1
          have hgpre : ∀ pc, pc < st.code.size + 1 →
              (compileNode body st.regions.size
                (repOptSt here st)).code[pc]! =
                (repOptSt here st).code[pc]! := by
            have h1 := hg.code_pre
            rw [hrsz] at h1
            exact h1
          have hgcle : st.classes.size ≤
              (compileNode body st.regions.size
                (repOptSt here st)).classes.size := hg.cls_le
          have hgcpre : ∀ j, j < st.classes.size →
              (compileNode body st.regions.size
                (repOptSt here st)).classes[j]! = st.classes[j]! := hg.cls_pre
          have hgcmod : st.classes.size % 32 = 0 →
              (compileNode body st.regions.size
                (repOptSt here st)).classes.size % 32 = 0 := hg.cls_mod
          have hgrle : st.reps.size ≤ (compileNode body st.regions.size
              (repOptSt here st)).reps.size := hg.reps_le
          have hgrpre : ∀ i, i < st.reps.size →
              (compileNode body st.regions.size
                (repOptSt here st)).reps[i]! = st.reps[i]! := hg.reps_pre
          have hfrag' : st.classes.size % 32 = 0 →
              FragAt (compileNode body st.regions.size
                  (repOptSt here st)).code
                (compileNode body st.regions.size (repOptSt here st)).classes
                (compileNode body st.regions.size (repOptSt here st)).reps
                st.reps.size body (st.code.size + 1)
                (compileNode body st.regions.size
                  (repOptSt here st)).code.size := by
            intro hmod
            have h1 := hfrag hmod
            rwa [hrsz] at h1
          have hsp0 : (repOptSt here st).code[st.code.size]! =
              ⟨.split, 0, 0⟩ := getBang_push_eq st.code _
          have hfc : (closeRegion
              (patch (compileNode body st.regions.size (repOptSt here st))
                st.code.size
                (fun i => if greedy then
                  { i with
                    arg := st.code.size + 1
                    alt := (compileNode body st.regions.size
                      (repOptSt here st)).code.size }
                else
                  { i with
                    arg := (compileNode body st.regions.size
                      (repOptSt here st)).code.size
                    alt := st.code.size + 1 }))
              st.regions.size).code =
              (compileNode body st.regions.size
                (repOptSt here st)).code.modify st.code.size
                (fun i => if greedy then
                  { i with
                    arg := st.code.size + 1
                    alt := (compileNode body st.regions.size
                      (repOptSt here st)).code.size }
                else
                  { i with
                    arg := (compileNode body st.regions.size
                      (repOptSt here st)).code.size
                    alt := st.code.size + 1 }) := rfl
          refine ⟨?_, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hfc]
              simp
              omega
            · intro pc hpc
              rw [hfc, getBang_modify_ne _ st.code.size (by omega),
                hgpre pc (by omega)]
              show (st.code.push ⟨.split, 0, 0⟩)[pc]! = st.code[pc]!
              exact getBang_push_lt st.code _ hpc
            · exact hgcle
            · exact hgcpre
            · exact hgcmod
            · exact hgrle
            · exact hgrpre
          · rw [repCount]
            exact hr
          · intro hmod
            rw [hfc]
            have hhisz :
                ((compileNode body st.regions.size
                  (repOptSt here st)).code.modify st.code.size
                  (fun i => if greedy then
                    { i with
                      arg := st.code.size + 1
                      alt := (compileNode body st.regions.size
                        (repOptSt here st)).code.size }
                  else
                    { i with
                      arg := (compileNode body st.regions.size
                        (repOptSt here st)).code.size
                      alt := st.code.size + 1 })).size =
                (compileNode body st.regions.size
                  (repOptSt here st)).code.size := by
              simp
            rw [hhisz]
            refine .repOpt hlo ?_ ?_
            · rw [getBang_modify_eq _ st.code.size (by omega),
                hgpre st.code.size (by omega), hsp0]
            · refine ((hfrag' hmod).mono ?_ (Nat.le_refl _) (fun _ _ => rfl)
                (Nat.le_refl _) fun _ _ => rfl)
              intro pc h1 h2
              exact getBang_modify_ne _ st.code.size (by omega)

/-! ## The trail discipline

On this round's opcodes the register file changes — `save` writes a slot
and pushes an undo entry whenever anything is on the stack — so a
backtrack entry no longer stands alone: what it means is the register
file *at push time*, recovered by replaying the trail above its mark.
The three facts below are the whole discipline: a mark at the top means
no replay, a write-plus-undo pair cancels, and replaying down to `m` can
go through any intermediate mark `k`. -/

private theorem set!_cancel (u : Spec.Regs) (i : Nat) (x : UInt32) :
    (u.set! i x).set! i u[i]! = u := by
  by_cases h : i < u.size
  · rw [getElem!_pos u i h]
    show (u.setIfInBounds i x).setIfInBounds i u[i] = u
    rw [Array.setIfInBounds_setIfInBounds]
    apply Array.ext
    · simp
    · intro j h1 h2
      by_cases hj : i = j
      · subst hj
        simp
      · rw [Array.getElem_setIfInBounds_ne h2 hj]
  · show (u.setIfInBounds i x).setIfInBounds i u[i]! = u
    rw [Array.setIfInBounds_eq_of_size_le (by simp; omega),
      Array.setIfInBounds_eq_of_size_le (by omega)]

/-- The register file a stack entry saw at push time. -/
def snapAt (trail : Array Undo) (regs : Spec.Regs) (mark : Nat) :
    Spec.Regs :=
  (replayTrail trail regs mark).2

theorem replayTrail_of_le {trail : Array Undo} {regs : Spec.Regs}
    {mark : Nat} (h : trail.size ≤ mark) :
    replayTrail trail regs mark = (trail, regs) := by
  rw [replayTrail, if_pos h]

theorem snapAt_full (trail : Array Undo) (regs : Spec.Regs) :
    snapAt trail regs trail.size = regs := by
  rw [snapAt, replayTrail_of_le (Nat.le_refl _)]

/-- One write, one undo: replaying past the pair restores the file. -/
theorem replay_push_cancel (trail : Array Undo) (regs : Spec.Regs)
    (slot : Nat) (v : UInt32) {mark : Nat} (h : mark ≤ trail.size) :
    replayTrail (trail.push ⟨slot, regs[slot]!⟩) (regs.set! slot v) mark =
      replayTrail trail regs mark := by
  rw [replayTrail, if_neg (by simp; omega)]
  simp only [Array.back!_push, Array.pop_push]
  rw [set!_cancel]

/-- Replaying to `m` factors through any intermediate mark `k`. -/
theorem replay_stage :
    ∀ (n : Nat) (trail : Array Undo) (regs : Spec.Regs) (m k : Nat),
      trail.size ≤ n → m ≤ k → k ≤ trail.size →
      replayTrail trail regs m =
        replayTrail (replayTrail trail regs k).1
          (replayTrail trail regs k).2 m := by
  intro n
  induction n with
  | zero =>
      intro trail regs m k hn hm hk
      rw [replayTrail_of_le (show trail.size ≤ k by omega)]
  | succ n ih =>
      intro trail regs m k hn hm hk
      by_cases hks : trail.size ≤ k
      · rw [replayTrail_of_le hks]
      · rw [show replayTrail trail regs m =
            replayTrail trail.pop
              (regs.set! trail.back!.slot trail.back!.old) m from by
          rw [replayTrail, if_neg (by omega)]]
        rw [show replayTrail trail regs k =
            replayTrail trail.pop
              (regs.set! trail.back!.slot trail.back!.old) k from by
          rw [replayTrail, if_neg (by omega)]]
        exact ih trail.pop _ m k (by simp; omega) hm (by simp; omega)

/-- Replaying to a mark leaves exactly that much trail. -/
theorem replay_size :
    ∀ (n : Nat) (trail : Array Undo) (regs : Spec.Regs) (mark : Nat),
      trail.size ≤ n → mark ≤ trail.size →
      (replayTrail trail regs mark).1.size = mark := by
  intro n
  induction n with
  | zero =>
      intro trail regs mark hn hk
      rw [replayTrail_of_le (by omega)]
      simp
      omega
  | succ n ih =>
      intro trail regs mark hn hk
      by_cases hks : trail.size ≤ mark
      · rw [replayTrail_of_le hks]
        simp
        omega
      · rw [show replayTrail trail regs mark =
            replayTrail trail.pop
              (regs.set! trail.back!.slot trail.back!.old) mark from by
          rw [replayTrail, if_neg (by omega)]]
        exact ih trail.pop _ mark (by simp; omega) (by simp; omega)

/-- The mirror's reading of the backtrack stack: resume points paired
with their push-time threads, newest first. -/
def stackOf (trail : Array Undo) (regs : Spec.Regs) (bt : Array BtEntry) :
    List Entry :=
  (bt.toList.map fun e => (e.pc, ⟨e.pos, snapAt trail regs e.mark⟩)).reverse

theorem stackOf_push (trail : Array Undo) (regs : Spec.Regs)
    (bt : Array BtEntry) (pc pos : Nat) :
    stackOf trail regs (bt.push ⟨pc, pos, trail.size⟩) =
      (pc, ⟨pos, regs⟩) :: stackOf trail regs bt := by
  simp [stackOf, Array.toList_push, snapAt_full]

/-- A guarded write leaves every decoded snapshot alone: the undo entry
pushed with it cancels it below every live mark. -/
theorem stackOf_write (trail : Array Undo) (regs : Spec.Regs)
    (bt : Array BtEntry) (slot : Nat) (v : UInt32)
    (hmarks : ∀ e ∈ bt.toList, e.mark ≤ trail.size) :
    stackOf (trail.push ⟨slot, regs[slot]!⟩) (regs.set! slot v) bt =
      stackOf trail regs bt := by
  unfold stackOf
  congr 1
  apply List.map_congr_left
  intro e he
  have : snapAt (trail.push ⟨slot, regs[slot]!⟩) (regs.set! slot v) e.mark =
      snapAt trail regs e.mark := by
    unfold snapAt
    rw [replay_push_cancel trail regs slot v (hmarks e he)]
  rw [this]

/-- Replaying to a mark at or above every decoded mark leaves the decoded
stack alone: the two-stage replay law, per entry. -/
theorem stackOf_replay (trail : Array Undo) (regs : Spec.Regs)
    (bt : Array BtEntry) (k : Nat) (hk : k ≤ trail.size)
    (hmarks : ∀ e ∈ bt.toList, e.mark ≤ k) :
    stackOf (replayTrail trail regs k).1 (replayTrail trail regs k).2 bt =
      stackOf trail regs bt := by
  unfold stackOf
  congr 1
  apply List.map_congr_left
  intro e he
  have : snapAt (replayTrail trail regs k).1 (replayTrail trail regs k).2
      e.mark = snapAt trail regs e.mark := by
    unfold snapAt
    rw [← replay_stage trail.size trail regs e.mark k (Nat.le_refl _)
      (hmarks e he) hk]
  rw [this]

/-- A nonempty stack splits into its earlier entries and its top. -/
theorem toList_pop_back (bt : Array BtEntry) (h : bt.size ≠ 0) :
    bt.toList = bt.pop.toList ++ [bt.back!] := by
  have hne : bt.toList ≠ [] := by
    intro he
    exact h (by simpa using congrArg List.length he)
  have hback : bt.toList.getLast hne = bt.back! := by
    rw [List.getLast_eq_getElem]
    show _ = bt[bt.size - 1]!
    rw [getElem!_pos bt (bt.size - 1) (by omega)]
    simp
  rw [Array.toList_pop, ← hback]
  exact (List.dropLast_concat_getLast hne).symm

theorem stackOf_pop (trail : Array Undo) (regs : Spec.Regs)
    (bt : Array BtEntry) (h : bt.size ≠ 0) :
    stackOf trail regs bt =
      (bt.back!.pc, ⟨bt.back!.pos, snapAt trail regs bt.back!.mark⟩) ::
        stackOf trail regs bt.pop := by
  unfold stackOf
  conv => lhs; rw [toList_pop_back bt h]
  rw [List.map_append, List.reverse_append]
  simp

/-- What a successful `fork` did to the state: one entry pushed at the
current trail mark, everything else untouched. -/
theorem fork_shape {st st' : BtSt} {lim : Limits} {target pos : Nat}
    (h : fork st lim target pos = some st') :
    st'.bt = st.bt.push ⟨target, pos, st.trail.size⟩ ∧
    st'.trail = st.trail ∧ st'.regs = st.regs := by
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
            exact ⟨rfl, rfl, rfl⟩

/-- What a successful `writeReg` did: the slot written, an undo entry
pushed exactly when something is on the stack. -/
theorem writeReg_shape {st st' : BtSt} {lim : Limits} {slot : Nat}
    {v : UInt32}
    (h : writeReg st lim slot v = some st') :
    st'.regs = st.regs.set! slot v ∧ st'.bt = st.bt ∧
    ((0 < st.bt.size ∧
        st'.trail = st.trail.push ⟨slot, st.regs[slot]!⟩) ∨
      (st.bt.size = 0 ∧ st'.trail = st.trail)) := by
  rw [writeReg] at h
  split at h
  next hpos =>
    cases hg : chargeGrow st.trailCap st.trail.size undoSize maxTrail
        st.m lim with
    | none => rw [hg] at h; cases h
    | some pr =>
        obtain ⟨m2, cap2⟩ := pr
        rw [hg] at h
        cases h
        exact ⟨rfl, rfl, .inl ⟨hpos, rfl⟩⟩
  next hpos =>
    cases h
    exact ⟨rfl, rfl, .inr ⟨by omega, rfl⟩⟩

/-! ## The metered bridge -/

/-- The bridge invariant: the mirror's configuration is the machine's,
decoded. The register files agree, the decoded stack is the pending list,
and the marks obey the trail discipline — at or below the trail's size
and nondecreasing bottom to top, which is what pop-and-replay
preserves. -/
structure Sync (st : BtSt) (regs : Spec.Regs) (stk : List Entry) : Prop where
  regs_eq : st.regs = regs
  stack_eq : stackOf st.trail st.regs st.bt = stk
  marks_le : ∀ e ∈ st.bt.toList, e.mark ≤ st.trail.size
  marks_mono : st.bt.toList.Pairwise fun a b => a.mark ≤ b.mark

/-- Forget the machine state, keep the verdict; `none` is a budget stop. -/
def verdict : AttemptOut → Option Out
  | .found e st' => some (.found ⟨e, st'.regs⟩)
  | .exhausted _ => some .nomatch
  | .exceeded _ => none

/-- A guarded register write keeps the bridge invariant: the mirror makes
the same write, and the undo entry that rides along cancels it under every
live mark, so no decoded thread moves. -/
theorem sync_write {st st' : BtSt} {lim : Limits} {slot : Nat} {v : UInt32}
    {regs : Spec.Regs} {stk : List Entry} (hs : Sync st regs stk)
    (h : writeReg st lim slot v = some st') :
    Sync st' (regs.set! slot v) stk := by
  obtain ⟨hregs, hstack, hmle, hmmono⟩ := hs
  obtain ⟨hrg2, hbt2, htr2⟩ := writeReg_shape h
  refine ⟨by rw [hrg2, hregs], ?_, ?_, ?_⟩
  · rcases htr2 with ⟨_, htr⟩ | ⟨hzero, htr⟩
    · rw [htr, hbt2, hrg2, stackOf_write st.trail st.regs st.bt _ _ hmle,
        hstack]
    · have hbt0 : st.bt = #[] := Array.size_eq_zero_iff.mp hzero
      rw [htr, hbt2, hrg2, hbt0]
      rw [hbt0] at hstack
      rw [← hstack]
      rfl
  · intro e he
    rw [hbt2] at he
    rcases htr2 with ⟨_, htr⟩ | ⟨_, htr⟩
    · rw [htr]
      have := hmle e he
      simp
      omega
    · rw [htr]
      exact hmle e he
  · rw [hbt2]
    exact hmmono

/-- A fork keeps the bridge invariant: the entry pushed at the current
trail mark decodes to exactly the thread the mirror parks. -/
theorem sync_fork {st st' : BtSt} {lim : Limits} {target pos : Nat}
    {regs : Spec.Regs} {stk : List Entry} (hs : Sync st regs stk)
    (h : fork st lim target pos = some st') :
    Sync st' regs ((target, ⟨pos, regs⟩) :: stk) := by
  obtain ⟨hregs, hstack, hmle, hmmono⟩ := hs
  obtain ⟨hbt2, htr2, hrg2⟩ := fork_shape h
  refine ⟨by rw [hrg2, hregs], ?_, ?_, ?_⟩
  · rw [htr2, hrg2, hbt2, stackOf_push, hstack, hregs]
  · intro e he
    rw [htr2]
    rw [hbt2, Array.toList_push] at he
    rcases List.mem_append.mp he with he' | he'
    · exact hmle e he'
    · rw [List.mem_singleton] at he'
      subst he'
      exact Nat.le_refl _
  · rw [hbt2, Array.toList_push, List.pairwise_append]
    refine ⟨hmmono, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact hmle a ha

/-- `btFail` on a nonempty stack, spelled without its lets so the ite can
be split: pop the top entry, then either the replay budget refuses, or
the trail replays down to the entry's mark and the run resumes there. -/
private theorem btFail_eq {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt fuel : Nat} (st : BtSt)
    (hsz : st.bt.size ≠ 0) :
    btFail re s mo lim start attempt fuel st =
      (if (st.trail.size - st.bt.back!.mark) * regSize >
          lim.cost - st.m.cost then
        AttemptOut.exceeded { st with bt := st.bt.pop }
      else
        btStep re s mo lim start attempt fuel st.bt.back!.pc st.bt.back!.pos
          (if st.bt.pop.size == 0 then
            { st with
              bt := st.bt.pop
              m := ({ st.m with cost := (st.m.cost +
                (st.trail.size - st.bt.back!.mark) * regSize) })
              trail := #[]
              regs := ((replayTrail st.trail st.regs st.bt.back!.mark).2) }
          else
            { st with
              bt := st.bt.pop
              m := ({ st.m with cost := (st.m.cost +
                (st.trail.size - st.bt.back!.mark) * regSize) })
              trail := ((replayTrail st.trail st.regs st.bt.back!.mark).1)
              regs := ((replayTrail st.trail st.regs st.bt.back!.mark).2) })) := by
  rw [btFail, dif_neg hsz]

/-- The bridge: whenever the metered `btStep` completes — found or
exhausted, never exceeded — the mirror completes with the same verdict
from the decoded configuration, on the very same fuel. -/
theorem btStep_mirror {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt : Nat} :
    ∀ (fuel : Nat) (pc pos : Nat) (st : BtSt) (regs : Spec.Regs)
      (stk : List Entry), Sync st regs stk →
      ∀ r, verdict (btStep re s mo lim start attempt fuel pc pos st) =
        some r →
      run re s mo start attempt fuel pc pos regs stk = some r := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc pos st regs stk _ r h
      rw [btStep] at h
      simp [verdict] at h
  | succ n ih =>
      intro pc pos st regs stk hsync r h
      obtain ⟨hregs, hstack, hmle, hmmono⟩ := hsync
      have hfail : ∀ (st1 : BtSt) (regs1 : Spec.Regs) (stk1 : List Entry),
          Sync st1 regs1 stk1 → ∀ r',
          verdict (btFail re s mo lim start attempt n st1) = some r' →
          dispatch re s mo start attempt n stk1 = some r' := by
        intro st1 regs1 stk1 hsync1 r' h'
        obtain ⟨hregs1, hstack1, hmle1, hmmono1⟩ := hsync1
        by_cases hsz : st1.bt.size = 0
        · rw [btFail, dif_pos hsz] at h'
          simp only [verdict, Option.some.injEq] at h'
          have hbt : st1.bt = #[] := Array.size_eq_zero_iff.mp hsz
          rw [← hstack1, hbt, ← h']
          rw [show stackOf st1.trail st1.regs #[] = [] from rfl, dispatch]
        · rw [btFail_eq st1 hsz] at h'
          have hbackmem : st1.bt.back! ∈ st1.bt.toList := by
            rw [toList_pop_back st1.bt hsz]
            exact List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl))
          have hmarkle : st1.bt.back!.mark ≤ st1.trail.size :=
            hmle1 _ hbackmem
          have hcross : ∀ e ∈ st1.bt.pop.toList,
              e.mark ≤ st1.bt.back!.mark := by
            intro e he
            have hp := hmmono1
            rw [toList_pop_back st1.bt hsz, List.pairwise_append] at hp
            exact hp.2.2 e he _ (List.mem_singleton.mpr rfl)
          rw [← hstack1, stackOf_pop st1.trail st1.regs st1.bt hsz, dispatch]
          split at h'
          · simp [verdict] at h'
          · split at h'
            next hzero =>
              have hbt0 : st1.bt.pop = #[] := by
                refine Array.size_eq_zero_iff.mp ?_
                simpa using hzero
              refine ih st1.bt.back!.pc st1.bt.back!.pos _
                (snapAt st1.trail st1.regs st1.bt.back!.mark)
                (stackOf st1.trail st1.regs st1.bt.pop) ⟨rfl, ?_, ?_, ?_⟩ r' h'
              · rw [hbt0]
                rfl
              · intro e he
                rw [hbt0] at he
                cases he
              · rw [hbt0]
                simp
            next hzero =>
              refine ih st1.bt.back!.pc st1.bt.back!.pos _
                (snapAt st1.trail st1.regs st1.bt.back!.mark)
                (stackOf st1.trail st1.regs st1.bt.pop) ⟨rfl, ?_, ?_, ?_⟩ r' h'
              · exact stackOf_replay st1.trail st1.regs st1.bt.pop
                  st1.bt.back!.mark hmarkle hcross
              · intro e he
                have h1 := hcross e he
                have h2 := replay_size st1.trail.size st1.trail st1.regs
                  st1.bt.back!.mark (Nat.le_refl _) hmarkle
                show e.mark ≤ (replayTrail st1.trail st1.regs
                  st1.bt.back!.mark).1.size
                omega
              · show (st1.bt.pop).toList.Pairwise fun a b => a.mark ≤ b.mark
                rw [Array.toList_pop]
                exact List.Pairwise.sublist (List.dropLast_sublist _) hmmono1
      rw [btStep] at h
      split at h
      · simp [verdict] at h
      · have branch : ∀ (cond : Bool) (pos' : Nat),
            eff re s mo start attempt pc pos regs =
              (if cond then .goto (pc + 1) pos' regs else .fail) →
            verdict (if cond then
                btStep re s mo lim start attempt n (pc + 1) pos'
                  { st with m := { st.m with cost := st.m.cost + 1 } }
              else btFail re s mo lim start attempt n
                  { st with m := { st.m with cost := st.m.cost + 1 } }) =
              some r →
            run re s mo start attempt (n + 1) pc pos regs stk = some r := by
          intro cond pos' heff h'
          rw [run, heff]
          cases cond
          · exact hfail { st with m := { st.m with cost := st.m.cost + 1 } }
              regs stk ⟨hregs, hstack, hmle, hmmono⟩ r h'
          · exact ih (pc + 1) pos'
              { st with m := { st.m with cost := st.m.cost + 1 } }
              regs stk ⟨hregs, hstack, hmle, hmmono⟩ r h'
        have hsync1 : Sync { st with m := { st.m with cost := st.m.cost + 1 } }
            regs stk := ⟨hregs, hstack, hmle, hmmono⟩
        cases hop : (re.code[pc]!).op
        case repZero =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          cases hw : writeReg { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.novec + (re.code[pc]!).arg * 2) 0 with
          | none => rw [hw] at h; simp [verdict] at h
          | some st2 =>
              rw [hw] at h
              exact ih (pc + 1) pos st2
                (regs.set! (re.novec + (re.code[pc]!).arg * 2) 0) stk
                (sync_write hsync1 hw) r h
        case repEnter =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          cases hw : writeReg { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32 with
          | none => rw [hw] at h; simp [verdict] at h
          | some st2 =>
              rw [hw] at h
              exact ih (pc + 1) pos st2
                (regs.set! (re.novec + (re.code[pc]!).arg * 2 + 1) pos.toUInt32)
                stk (sync_write hsync1 hw) r h
        case repLoop =>
          simp only [hop] at h
          subst hregs
          rw [run]
          simp only [eff, hop]
          split at h
          next hlo =>
            rw [if_pos hlo]
            exact ih _ pos _ _ stk hsync1 r h
          next hlo =>
            rw [if_neg hlo]
            split at h
            next hhi =>
              rw [if_pos hhi]
              exact ih _ pos _ _ stk hsync1 r h
            next hhi =>
              rw [if_neg hhi]
              cases hg : (re.reps[(re.code[pc]!).arg]!).greedy with
              | true =>
                  simp only [hg, if_true] at h ⊢
                  cases hf : fork
                      { st with m := { st.m with cost := st.m.cost + 1 } } lim
                      (re.reps[(re.code[pc]!).arg]!).after pos with
                  | none => rw [hf] at h; simp [verdict] at h
                  | some st2 =>
                      rw [hf] at h
                      exact ih _ pos st2 _ _ (sync_fork hsync1 hf) r h
              | false =>
                  simp only [hg, Bool.false_eq_true, if_false] at h ⊢
                  cases hf : fork
                      { st with m := { st.m with cost := st.m.cost + 1 } } lim
                      (re.reps[(re.code[pc]!).arg]!).body pos with
                  | none => rw [hf] at h; simp [verdict] at h
                  | some st2 =>
                      rw [hf] at h
                      exact ih _ pos st2 _ _ (sync_fork hsync1 hf) r h
        case repNext =>
          simp only [hop] at h
          subst hregs
          rw [run]
          simp only [eff, hop]
          cases hw : writeReg { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.novec + (re.code[pc]!).arg * 2)
              (st.regs[re.novec + (re.code[pc]!).arg * 2]! + 1) with
          | none => rw [hw] at h; simp [verdict] at h
          | some st2 =>
              rw [hw] at h
              simp only [] at h
              by_cases hc : ((re.reps[(re.code[pc]!).arg]!).hi == none32 &&
                  pos.toUInt32 ==
                    st.regs[re.novec + (re.code[pc]!).arg * 2 + 1]! &&
                  (st.regs[re.novec + (re.code[pc]!).arg * 2]! + 1).toNat ≥
                    (re.reps[(re.code[pc]!).arg]!).lo) = true
              · rw [if_pos hc] at h ⊢
                exact ih _ pos st2 _ stk (sync_write hsync1 hw) r h
              · rw [if_neg hc] at h ⊢
                exact ih _ pos st2 _ stk (sync_write hsync1 hw) r h
        case jump =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          exact ih (re.code[pc]!).arg pos
            { st with m := { st.m with cost := st.m.cost + 1 } }
            regs stk ⟨hregs, hstack, hmle, hmmono⟩ r h
        case split =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          cases hf : fork { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.code[pc]!).alt pos with
          | none => rw [hf] at h; simp [verdict] at h
          | some st2 =>
              rw [hf] at h
              exact ih (re.code[pc]!).arg pos st2 regs
                ((((re.code[pc]!).alt, ⟨pos, regs⟩) : Entry) :: stk)
                (sync_fork hsync1 hf) r h
        case save =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          cases hw : writeReg { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.code[pc]!).arg pos.toUInt32 with
          | none => rw [hw] at h; simp [verdict] at h
          | some st2 =>
              rw [hw] at h
              exact ih (pc + 1) pos st2
                (regs.set! (re.code[pc]!).arg pos.toUInt32) stk
                (sync_write hsync1 hw) r h
        case accept =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          split at h
          next hrefuse =>
            rw [if_pos hrefuse]
            exact hfail { st with m := { st.m with cost := st.m.cost + 1 } }
              regs stk ⟨hregs, hstack, hmle, hmmono⟩ r h
          next hrefuse =>
            rw [if_neg hrefuse]
            simp only [verdict, Option.some.injEq] at h
            rw [hregs] at h
            rw [← h]
        all_goals
          simp only [hop] at h
          exact branch _ _ (by simp [eff, hop]) h

/-! ## The compiled pattern as a whole -/

/-- The state `compile` hands the root node: empty tables, root region
open. -/
private def rootSt : CState :=
  { code := #[], classes := #[], reps := #[],
    regions := #[(⟨.root, none32, 0, 0⟩ : Region)] }

private theorem compile_code {p : Pat} :
    ((p.opts.endanchored = false →
      (compile p).code =
        (compileNode p.root 0 rootSt).code.push ⟨.accept, 0, 0⟩) ∧
     (p.opts.endanchored = true →
      (compile p).code =
        ((compileNode p.root 0 rootSt).code.push ⟨.eod, 0, 0⟩).push
          ⟨.accept, 0, 0⟩)) ∧
    (compile p).classes = (compileNode p.root 0 rootSt).classes ∧
    (compile p).reps = (compileNode p.root 0 rootSt).reps := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro hend
    simp only [compile, hend]
    rfl
  · intro hend
    simp only [compile, hend]
    rfl
  · by_cases hend : p.opts.endanchored = true
    · simp only [compile, hend]
      rfl
    · simp only [compile, eq_false_of_ne_true hend]
      rfl
  · by_cases hend : p.opts.endanchored = true
    · simp only [compile, hend]
      rfl
    · simp only [compile, eq_false_of_ne_true hend]
      rfl

/-- The compiled form of a well-formed pattern: the root's fragment from
0, then the optional ENDANCHORED `eod` assertion, then `accept`. The
repetition rows the root claimed are the whole table, which is what ties
the fragment's threaded index to the compiled program. -/
theorem compile_shape {p : Pat} (hc : Covered p.root) :
    FragAt (compile p).code (compile p).classes (compile p).reps 0 p.root 0
      (compileNode p.root 0 rootSt).code.size ∧
    (compile p).reps.size = repCount p.root ∧
    (p.opts.endanchored = false →
      (compile p).code[(compileNode p.root 0 rootSt).code.size]! =
        ⟨.accept, 0, 0⟩) ∧
    (p.opts.endanchored = true →
      (compile p).code[(compileNode p.root 0 rootSt).code.size]! =
        ⟨.eod, 0, 0⟩ ∧
      (compile p).code[(compileNode p.root 0 rootSt).code.size + 1]! =
        ⟨.accept, 0, 0⟩) := by
  obtain ⟨⟨hopen, hanch⟩, hclasses, hreps⟩ := compile_code (p := p)
  obtain ⟨hg, hrsz, hfrag⟩ :=
    compileNode_facts (sizeOf p.root) (Nat.le_refl _) hc 0 rootSt
  have hfrag' : FragAt (compileNode p.root 0 rootSt).code
      (compileNode p.root 0 rootSt).classes (compileNode p.root 0 rootSt).reps
      0 p.root 0 (compileNode p.root 0 rootSt).code.size := hfrag (by rfl)
  have hfragc : FragAt (compile p).code (compile p).classes (compile p).reps 0
      p.root 0 (compileNode p.root 0 rootSt).code.size := by
    refine hfrag'.mono ?_ ?_ ?_ ?_ ?_
    · intro pc _ h2
      by_cases hend : p.opts.endanchored = true
      · rw [hanch hend, getBang_push_lt _ _ (by simp; omega),
          getBang_push_lt _ _ h2]
      · rw [hopen (eq_false_of_ne_true hend), getBang_push_lt _ _ h2]
    · rw [hclasses]
      exact Nat.le_refl _
    · intro j _
      rw [hclasses]
    · rw [hreps]
      exact Nat.le_refl _
    · intro i _
      rw [hreps]
  refine ⟨hfragc, ?_, ?_, ?_⟩
  · rw [hreps, hrsz]
    show 0 + repCount p.root = repCount p.root
    omega
  · intro hend
    rw [hopen hend, getBang_push_eq]
  · intro hend
    rw [hanch hend]
    constructor
    · rw [getBang_push_lt _ _ (by simp), getBang_push_eq]
    · rw [show (compileNode p.root 0 rootSt).code.size + 1 =
        ((compileNode p.root 0 rootSt).code.push ⟨.eod, 0, 0⟩).size from by
          simp,
        getBang_push_eq]

/-! ## The gate: eod, accept, and the spec's two filters -/

/-- The spec's per-thread survival test at the gate, spelled as the spec
spells it. -/
def gateKeep (p : Pat) (s : ByteArray) (mo : MOpts) (start attempt : Nat)
    (t : Spec.Thread) : Bool :=
  Spec.acceptable mo start attempt t && Spec.endOk p s t

/-- What the gate hands back for a queue of surviving threads: the first
one, its two ovector slots written the way accept writes them. -/
def gateOut (attempt : Nat) : List Spec.Thread → Out
  | [] => .nomatch
  | t :: _ =>
      .found ⟨t.pos, (t.regs.set! 0 attempt.toUInt32).set! 1 t.pos.toUInt32⟩

section Gate

variable {re : Re} {s : ByteArray} {mo : MOpts} {start attempt : Nat}

/-- Threads parked on a bare accept: the empty-match refusal is the
spec's `acceptable`, and with ENDANCHORED off `endOk` never refuses. -/
theorem resumes_gate_open {p : Pat} {M : Nat}
    (hend : p.opts.endanchored = false)
    (hcell : re.code[M]! = ⟨.accept, 0, 0⟩) :
    ∀ ts : List Spec.Thread,
      Resumes re s mo start attempt (ts.map fun t => (M, t))
        (gateOut attempt (ts.filter (gateKeep p s mo start attempt))) := by
  intro ts
  induction ts with
  | nil => exact resumes_nil.mpr rfl
  | cons t ts iht =>
      rw [List.map_cons, List.filter_cons]
      by_cases hrefuse : (t.pos == attempt &&
          (mo.notempty || (mo.notemptyAtStart && attempt == start))) = true
      · have hkeep : gateKeep p s mo start attempt t = false := by
          simp [gateKeep, Spec.acceptable, hrefuse]
        rw [hkeep]
        simp only [Bool.false_eq_true, if_false]
        refine resumes_cons.mpr (runs_eff.mpr ?_)
        rw [show eff re s mo start attempt M t.pos t.regs = .fail from by
          simp [eff, hcell, hrefuse]]
        exact iht
      · have hkeep : gateKeep p s mo start attempt t = true := by
          simp [gateKeep, Spec.acceptable, Spec.endOk, hend,
            eq_false_of_ne_true hrefuse]
        rw [hkeep]
        simp only [if_true]
        refine resumes_cons.mpr (runs_eff.mpr ?_)
        rw [show eff re s mo start attempt M t.pos t.regs =
            .give ⟨t.pos, (t.regs.set! 0 attempt.toUInt32).set! 1
              t.pos.toUInt32⟩ from by
          simp [eff, hcell, hrefuse]]
        rfl

/-- Threads parked on the ENDANCHORED gate: the eod assertion is exactly
`endOk`'s test, and the accept behind it is `acceptable`. -/
theorem resumes_gate_anchored {p : Pat} {M : Nat}
    (hend : p.opts.endanchored = true)
    (hcelle : re.code[M]! = ⟨.eod, 0, 0⟩)
    (hcella : re.code[M + 1]! = ⟨.accept, 0, 0⟩) :
    ∀ ts : List Spec.Thread,
      Resumes re s mo start attempt (ts.map fun t => (M, t))
        (gateOut attempt (ts.filter (gateKeep p s mo start attempt))) := by
  intro ts
  induction ts with
  | nil => exact resumes_nil.mpr rfl
  | cons t ts iht =>
      rw [List.map_cons, List.filter_cons]
      by_cases heod : (t.pos == s.size) = true
      · by_cases hrefuse : (t.pos == attempt &&
            (mo.notempty || (mo.notemptyAtStart && attempt == start))) = true
        · have hkeep : gateKeep p s mo start attempt t = false := by
            simp [gateKeep, Spec.acceptable, hrefuse]
          rw [hkeep]
          simp only [Bool.false_eq_true, if_false]
          refine resumes_cons.mpr (runs_eff.mpr ?_)
          rw [show eff re s mo start attempt M t.pos t.regs =
              .goto (M + 1) t.pos t.regs from by
            simp [eff, hcelle, heod]]
          show Runs re s mo start attempt (M + 1) t.pos t.regs _ _
          refine runs_eff.mpr ?_
          rw [show eff re s mo start attempt (M + 1) t.pos t.regs =
              .fail from by
            simp [eff, hcella, hrefuse]]
          exact iht
        · have hkeep : gateKeep p s mo start attempt t = true := by
            simp [gateKeep, Spec.acceptable, Spec.endOk, hend,
              eq_false_of_ne_true hrefuse, heod]
          rw [hkeep]
          simp only [if_true]
          refine resumes_cons.mpr (runs_eff.mpr ?_)
          rw [show eff re s mo start attempt M t.pos t.regs =
              .goto (M + 1) t.pos t.regs from by
            simp [eff, hcelle, heod]]
          show Runs re s mo start attempt (M + 1) t.pos t.regs _ _
          refine runs_eff.mpr ?_
          rw [show eff re s mo start attempt (M + 1) t.pos t.regs =
              .give ⟨t.pos, (t.regs.set! 0 attempt.toUInt32).set! 1
                t.pos.toUInt32⟩ from by
            simp [eff, hcella, hrefuse]]
          rfl
      · have hkeep : gateKeep p s mo start attempt t = false := by
          simp only [gateKeep, Spec.endOk, hend]
          simp [heod]
        rw [hkeep]
        simp only [Bool.false_eq_true, if_false]
        refine resumes_cons.mpr (runs_eff.mpr ?_)
        rw [show eff re s mo start attempt M t.pos t.regs = .fail from by
          simp [eff, hcelle, heod]]
        exact iht

end Gate

/-- The verdict of one attempt, read against the spec's survivors: found
on the first of them, with the two ovector slots written the way accept
writes them and every capture below `novec` agreeing, or no-match when
nothing survives. The machine's file is longer than the spec's — the
repetition counters live above the ovector — so agreement, not equality,
is the most that can be asked. -/
def OutAgrees (novec attempt : Nat) : Out → List Spec.Thread → Prop
  | .found tt, t :: _ =>
      tt.pos = t.pos ∧
      Agree novec tt.regs
        ((t.regs.set! 0 attempt.toUInt32).set! 1 t.pos.toUInt32)
  | .nomatch, [] => True
  | _, _ => False

/-- The gate reads a thread's end position and nothing else, so agreeing
threads survive it together. -/
theorem gateKeep_congr {p : Pat} {s : ByteArray} {mo : MOpts}
    {start attempt : Nat} {t u : Spec.Thread} (h : t.pos = u.pos) :
    gateKeep p s mo start attempt t = gateKeep p s mo start attempt u := by
  simp only [gateKeep, Spec.acceptable, Spec.endOk, h]

/-- Filtering by a test the relation preserves keeps the lists related. -/
theorem forall₂_filter {novec : Nat} {P : Spec.Thread → Bool}
    (hP : ∀ t u, TAgree novec t u → P t = P u) :
    ∀ {l l' : List Spec.Thread}, List.Forall₂ (TAgree novec) l l' →
    List.Forall₂ (TAgree novec) (l.filter P) (l'.filter P) := by
  intro l l' h
  induction h with
  | nil => exact .nil
  | @cons x y xs ys hxy _ ih =>
      rw [List.filter_cons, List.filter_cons, ← hP x y hxy]
      by_cases hx : P x = true
      · rw [if_pos hx, if_pos hx]
        exact .cons hxy ih
      · rw [if_neg hx, if_neg hx]
        exact ih

/-- Reading the mirror's answer on a related list of survivors. -/
theorem outAgrees_of_forall₂ {novec attempt : Nat} :
    ∀ {l l' : List Spec.Thread}, List.Forall₂ (TAgree novec) l l' →
      OutAgrees novec attempt (gateOut attempt l) l' := by
  intro l l' h
  cases h with
  | nil => exact True.intro
  | @cons x y xs ys hxy _ =>
      refine ⟨hxy.1, ?_⟩
      rw [← hxy.1]
      exact (hxy.2.set_both 0 attempt.toUInt32).set_both 1 x.pos.toUInt32

/-- One attempt's threads, spelled with the gate the mirror applies. -/
theorem attemptThreads_eq {p : Pat} {s : ByteArray} {mo : MOpts}
    {start attempt F : Nat} {tsO : List Spec.Thread}
    (h : Spec.search F ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root
      attempt (Array.replicate (2 * (p.ncap + 1)) unset32) = some tsO) :
    Spec.attemptThreads F p s mo start attempt =
      some (tsO.filter (gateKeep p s mo start attempt)) := by
  rw [Spec.attemptThreads, h]
  rfl

/-- S-8, per attempt: on a well-formed pattern a completed `btStep`
attempt answers exactly what `Spec.attemptThreads` filters out of the
search — found on its head thread with the ovector slots written, or
no-match when no thread survives. Resource questions never enter:
`verdict … = some r` is precisely "the attempt completed". -/
theorem attempt_refines {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt fuel F : Nat} {st : BtSt} {r : Out}
    {ts : List Spec.Thread}
    (hc : Covered p.root) (hcaps : CapsBelow (2 * (p.ncap + 1)) p.root)
    (hs : s.size ≤ ceiling) (hbt : st.bt = #[])
    (hregs : st.regs = Array.replicate (compile p).nregs unset32)
    (hatt : attempt ≤ s.size) (hF : F < none32)
    (hden : denot F (mctx (compile p) s mo) (2 * (p.ncap + 1)) 0 p.root attempt
      (Array.replicate (compile p).nregs unset32) = some ts)
    (h : verdict (btStep (compile p) s mo lim start attempt fuel 0 attempt
      st) = some r) :
    ∃ tsO, Spec.attemptThreads F p s mo start attempt = some tsO ∧
      OutAgrees (2 * (p.ncap + 1)) attempt r tsO := by
  obtain ⟨hfrag, hrsz, hopen, hanch⟩ := compile_shape hc
  have hnovec : (compile p).novec = 2 * (p.ncap + 1) := rfl
  have hnregs : (compile p).nregs =
      2 * (p.ncap + 1) + 2 * repCount p.root := by
    show ((compile p).ncap + 1) * 2 + (compile p).reps.size * 2 = _
    rw [hrsz]
    show (p.ncap + 1) * 2 + repCount p.root * 2 = _
    omega
  have hsync : Sync st (Array.replicate (compile p).nregs unset32) [] := by
    refine ⟨hregs, ?_, ?_, ?_⟩
    · rw [hbt]
      rfl
    · intro e he
      rw [hbt] at he
      simp at he
    · rw [hbt]
      simp
  have hruns : Runs (compile p) s mo start attempt 0 attempt
      (Array.replicate (compile p).nregs unset32) [] r :=
    ⟨fuel, btStep_mirror fuel 0 attempt st
      (Array.replicate (compile p).nregs unset32) [] hsync r h⟩
  have hres := (frag_runs hs hfrag F attempt
    (Array.replicate (compile p).nregs unset32) ts (by rw [hnovec]; exact hden)
    hatt hF (by rw [hnovec]; exact hcaps)
    (by rw [hnovec, Array.size_replicate, hnregs]; omega) [] r).mp hruns
  rw [List.append_nil] at hres
  have hgate : Resumes (compile p) s mo start attempt
      (ts.map fun t => ((compileNode p.root 0 rootSt).code.size, t))
      (gateOut attempt (ts.filter (gateKeep p s mo start attempt))) := by
    cases hend : p.opts.endanchored with
    | false => exact resumes_gate_open hend (hopen hend) _
    | true =>
        obtain ⟨h1, h2⟩ := hanch hend
        exact resumes_gate_anchored hend h1 h2 _
  have hr := resumes_det hres hgate
  have hag0 : Agree (2 * (p.ncap + 1))
      (Array.replicate (compile p).nregs unset32)
      (Array.replicate (2 * (p.ncap + 1)) unset32) := by
    refine ⟨by rw [Array.size_replicate, hnregs]; omega,
      by simp, ?_⟩
    intro i hi
    rw [getElem!_pos _ i (by rw [Array.size_replicate, hnregs]; omega),
      getElem!_pos _ i (by rw [Array.size_replicate]; omega)]
    simp
  obtain ⟨tsO, hsearch, hrel⟩ := denot_search hden hag0
  refine ⟨_, attemptThreads_eq hsearch, ?_⟩
  have hfil := forall₂_filter (P := gateKeep p s mo start attempt)
    (fun t u htu => gateKeep_congr htu.1) hrel
  rw [hr]
  exact outAgrees_of_forall₂ hfil



/-- A concatenation is covered as soon as each of its children is:
`catCons` peels one child at a time, down to the empty concatenation. -/
theorem covered_cat : ∀ {kids : List Ast},
    (∀ k ∈ kids, Covered k) → Covered (.cat kids)
  | [], _ => .catNil
  | k :: rest, h =>
      .catCons (h k (by simp)) (covered_cat fun x hx => h x (by simp [hx]))

/-- A non-empty alternation is covered as soon as each of its arms is.
The last arm closes the chain with `altOne`; every earlier one hangs off
it with `altCons`. -/
theorem covered_alt : ∀ {arms : List Ast}, arms ≠ [] →
    (∀ a ∈ arms, Covered a) → Covered (.alt arms)
  | [], hne, _ => absurd rfl hne
  | [a], _, h => .altOne (h a (by simp))
  | a :: b :: rest, _, h =>
      .altCons (h a (by simp))
        (covered_alt (by simp) fun x hx => h x (by simp [hx]))

/-- The parser facts already rule out everything the fragment relation
refuses: the empty alternation is excluded by hand, and a bounded
repetition high stays below the `none32` sentinel. So a well-formed AST
is a covered one, and the compiler theorems apply to it. -/
theorem WfAst.covered : ∀ {a : Ast}, WfAst a → Covered a
  | .cat kids, h => by
      rw [WfAst] at h
      refine covered_cat fun k hk => ?_
      have := List.sizeOf_lt_of_mem hk
      exact WfAst.covered (attach_foldr_forall h k hk)
  | .alt arms, h => by
      rw [WfAst] at h
      refine covered_alt h.1 fun a ha => ?_
      have := List.sizeOf_lt_of_mem ha
      exact WfAst.covered (attach_foldr_forall h.2 a ha)
  | .grp cap body, h => by
      rw [WfAst] at h
      exact .grp (WfAst.covered h)
  | .rep lo hi greedy body, h => by
      rw [WfAst] at h
      match hi with
      | some 0 => exact .repNone
      | some 1 =>
          by_cases hlo : lo = 1
          · subst hlo
            exact .repOne (WfAst.covered h.2)
          · exact .repOpt hlo (WfAst.covered h.2)
      | none => exact .repGen (by simp) (by simp) h.1 (WfAst.covered h.2)
      | some (_ + 2) =>
          exact .repGen (by simp) (by simp) h.1 (WfAst.covered h.2)
  | .nul, _ => .nul
  | .chr b, _ => .chr b
  | .chrCI folded, _ => .chrCI folded
  | .cls bits, _ => .cls bits
  | .any, _ => .any
  | .anyNoNL, _ => .anyNoNL
  | .bsr, _ => .bsr
  | .circ, _ | .circM, _ | .doll, _ | .dollE, _ | .dollM, _
  | .sod, _ | .eod, _ | .eodn, _ | .wordB, _ | .notWordB, _ => .assn rfl
termination_by a _ => sizeOf a
decreasing_by
  all_goals simp
  all_goals omega

/-! ## The search leaves the register file's shape alone

The spec allocates the ovector once and never grows it: the only writes
are a group's two save slots, and they go through `Array.set!`, which
drops an out-of-range write instead of extending the array. Stated for
the four mutually recursive halves of the search, this is what lets the
machine-side arguments compare register files slot by slot without ever
worrying about a size mismatch. -/

mutual

/-- Every thread `search` hands back carries a register file of the same
size as the one it was given. -/
theorem search_size {c : Spec.SCtx} : ∀ {fuel : Nat} {a : Ast} {pos : Nat}
    {regs : Spec.Regs} {ts : List Spec.Thread},
    Spec.search fuel c a pos regs = some ts →
    ∀ t ∈ ts, t.regs.size = regs.size := by
  intro fuel a pos regs ts h
  match a with
  | .cat kids =>
      rw [Spec.search.eq_def] at h
      exact searchCat_size h
  | .alt arms =>
      rw [Spec.search.eq_def] at h
      exact searchAlt_size h
  | .grp cap body =>
      rw [Spec.search.eq_def] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨taken, htaken, rfl⟩ := h
      have hopen :
          (if cap != 0 then regs.set! (2 * cap) pos.toUInt32 else regs).size
            = regs.size := by
        split <;> simp [Array.set!_eq_setIfInBounds]
      intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hu' := (search_size htaken u hu).trans hopen
      split <;> simpa [Array.set!_eq_setIfInBounds] using hu'
  | .rep lo hi greedy body =>
      rw [Spec.search.eq_def] at h
      match hi with
      | some 0 =>
          simp only [Option.some.injEq] at h
          subst h
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          rfl
      | some 1 =>
          simp only [] at h
          split at h
          · exact search_size h
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
            · exact search_size htaken t hmem
            · rfl
      | none => exact searchRep_size h
      | some (_ + 2) => exact searchRep_size h
  | .nul | .chr _ | .chrCI _ | .cls _ | .any | .anyNoNL | .bsr
  | .circ | .circM | .doll | .dollE | .dollM
  | .sod | .eod | .eodn | .wordB | .notWordB =>
      rw [Spec.search.eq_def] at h
      cases h
      intro t ht
      first
        | (simp only [List.mem_singleton] at ht; subst ht; rfl)
        | (split at ht
           · simp only [List.mem_singleton] at ht; subst ht; rfl
           · simp at ht)
termination_by fuel a => (fuel, sizeOf a)

/-- The same for a concatenation, where the tail starts from a thread of
the head and so inherits its size. -/
theorem searchCat_size {c : Spec.SCtx} : ∀ {fuel : Nat} {kids : List Ast}
    {pos : Nat} {regs : Spec.Regs} {ts : List Spec.Thread},
    Spec.searchCat fuel c kids pos regs = some ts →
    ∀ t ∈ ts, t.regs.size = regs.size := by
  intro fuel kids pos regs ts h
  match kids with
  | [] =>
      rw [Spec.searchCat.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      rfl
  | _ :: rest =>
      rw [Spec.searchCat.eq_def] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨heads, hheads, tails, htails, rfl⟩ := h
      intro t ht
      simp only [List.mem_flatten] at ht
      obtain ⟨l, hl, htl⟩ := ht
      obtain ⟨u, hu, hul⟩ := Spec.mapM_mem htails hl
      exact (searchCat_size hul t htl).trans (search_size hheads u hu)
termination_by fuel kids => (fuel, sizeOf kids)

/-- The same for an alternation, where every arm starts from the caller's
own file. -/
theorem searchAlt_size {c : Spec.SCtx} : ∀ {fuel : Nat} {arms : List Ast}
    {pos : Nat} {regs : Spec.Regs} {ts : List Spec.Thread},
    Spec.searchAlt fuel c arms pos regs = some ts →
    ∀ t ∈ ts, t.regs.size = regs.size := by
  intro fuel arms pos regs ts h
  match arms with
  | [] =>
      rw [Spec.searchAlt.eq_def] at h
      simp only [Option.some.injEq] at h
      subst h
      intro t ht
      simp at ht
  | _ :: rest =>
      rw [Spec.searchAlt.eq_def] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨mine, hmine, theirs, htheirs, rfl⟩ := h
      intro t ht
      rcases List.mem_append.mp ht with hm | hm
      · exact search_size hmine t hm
      · exact searchAlt_size htheirs t hm
termination_by fuel arms => (fuel, sizeOf arms)

/-- The same for a counted repetition: each round hands the next one a
thread of the body's answer, and the exit thread is the caller's own. -/
theorem searchRep_size {c : Spec.SCtx} : ∀ {fuel : Nat} {body : Ast}
    {lo : Nat} {hi : Option Nat} {greedy : Bool} {cnt pos : Nat}
    {regs : Spec.Regs} {ts : List Spec.Thread},
    Spec.searchRep fuel c body lo hi greedy cnt pos regs = some ts →
    ∀ t ∈ ts, t.regs.size = regs.size := by
  intro fuel body lo hi greedy cnt pos regs ts h
  match fuel with
  | 0 =>
      rw [Spec.searchRep.eq_def] at h
      exact absurd h (by simp)
  | fuel + 1 =>
      rw [Spec.searchRep.eq_def] at h
      simp only [] at h
      have henter : ∀ v,
          (do
            let taken ← Spec.search fuel c body pos regs
            let onward ← taken.mapM fun t =>
              if hi.isNone && t.pos == pos && cnt + 1 ≥ lo then
                pure [t]
              else
                Spec.searchRep fuel c body lo hi greedy (cnt + 1) t.pos t.regs
            pure onward.flatten : Option (List Spec.Thread)) = some v →
          ∀ t ∈ v, t.regs.size = regs.size := by
        intro v hv
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hv
        obtain ⟨taken, htaken, onward, honward, rfl⟩ := hv
        intro t ht
        simp only [List.mem_flatten] at ht
        obtain ⟨l, hl, htl⟩ := ht
        obtain ⟨u, hu, hul⟩ := Spec.mapM_mem honward hl
        have h1 := search_size htaken u hu
        split at hul
        · simp only [Option.some.injEq] at hul
          subst hul
          simp only [List.mem_singleton] at htl
          subst htl
          exact h1
        · exact (searchRep_size hul t htl).trans h1
      split at h
      · exact henter ts h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          intro t ht
          simp only [List.mem_singleton] at ht
          subst ht
          rfl
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
          · rfl
termination_by fuel body => (fuel, 1 + sizeOf body)

end

/-! ## The whole call: the attempt loop, delivery, and the guards

What is left above the per-attempt theorem is bookkeeping the two layers
do in the same order: the same bumpalong skips, the same stop rules, the
same delivery. The bumpalong is the only one that takes an argument —
the compiled bit is `scan_first`'s verdict and the spec's is `crWalk`'s,
and `crFirst_agrees` says they are the same bit. -/

/-- The bumpalong refusal reads the same three pattern facts on both
sides. -/
theorem skipsAttempt_agrees {p : Pat} (hw : WfAst p.root) (s : ByteArray)
    (pos : Nat) :
    Re.skipsAttempt (compile p) s pos = Spec.skipsAttempt p s pos := by
  have h1 : (compile p).nltype = p.nltype := rfl
  have h2 : (compile p).hascrlf = p.hascrlf := rfl
  rw [Re.skipsAttempt, Spec.skipsAttempt, h1, h2,
    CrFirst.crFirst_agrees p hw.noEmptyAlt]

/-- Agreement below the ovector, plus the spec's own length, makes the
delivered slice the spec's answer outright. -/
theorem extract_eq_of_agree {novec : Nat} {u v : Spec.Regs}
    (h : Agree novec u v) (hv : v.size = novec) : u.extract 0 novec = v := by
  obtain ⟨hu, _, hag⟩ := h
  apply Array.ext
  · rw [Array.size_extract, hv]
    omega
  · intro i h1 h2
    have hi : i < novec := by
      rw [hv] at h2
      exact h2
    have hag' := hag i hi
    rw [getElem!_pos u i (by omega), getElem!_pos v i (by omega)] at hag'
    rw [Array.getElem_extract]
    simpa using hag'

/-- The scan never answers BadInput: that verdict belongs to the guard
above it. -/
theorem scan_ne_badInput {fuel : Nat} {p : Pat} {s : ByteArray} {mo : MOpts}
    {start : Nat} : ∀ (steps attempt : Nat) (r : Spec.MatchAnswer),
    Spec.scan fuel p s mo start attempt steps = some r → r ≠ .badInput := by
  intro steps
  induction steps with
  | zero =>
      intro attempt r h
      rw [Spec.scan.eq_def] at h
      simp at h
  | succ steps ih =>
      intro attempt r h
      rw [Spec.scan.eq_def] at h
      simp only [] at h
      obtain ⟨survivors, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases survivors with
      | cons t rest =>
          simp only [Option.pure_def, Option.some.injEq] at h
          rw [← h]
          simp
      | nil =>
          simp only [] at h
          split at h
          · simp only [Option.pure_def, Option.some.injEq] at h
            rw [← h]
            simp
          · exact ih _ r h

/-- What one answer of the attempt loop means for the spec's scan. -/
def ScanAgrees (p : Pat) (s : ByteArray) (mo : MOpts)
    (start attempt steps : Nat) : RunEnd → Prop
  | .matched st =>
      Spec.scan (Spec.suffFuel s.size p.root) p s mo start attempt steps =
        some (.found (st.regs.extract 0 (2 * (p.ncap + 1))))
  | .noMatch _ =>
      Spec.scan (Spec.suffFuel s.size p.root) p s mo start attempt steps =
        some .notFound
  | .exceeded _ => True

/-- Reading one answer against a different but equal scan. -/
theorem ScanAgrees.step {p : Pat} {s : ByteArray} {mo : MOpts}
    {start a₁ s₁ a₂ s₂ : Nat} {out : RunEnd}
    (h : Spec.scan (Spec.suffFuel s.size p.root) p s mo start a₁ s₁ =
      Spec.scan (Spec.suffFuel s.size p.root) p s mo start a₂ s₂)
    (hout : ScanAgrees p s mo start a₂ s₂ out) :
    ScanAgrees p s mo start a₁ s₁ out := by
  cases out with
  | matched st =>
      rw [ScanAgrees] at hout ⊢
      rw [h]
      exact hout
  | noMatch st =>
      rw [ScanAgrees] at hout ⊢
      rw [h]
      exact hout
  | exceeded st => exact True.intro

/-- The attempt loop against the scan: same starting positions, same
skips, same stop rule, and on a match the same ovector. A budget refusal
is the one answer that claims nothing. -/
theorem btLoop_refines {p : Pat} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} (hw : Wf p) (hs : s.size ≤ ceiling)
    (hwrap : Spec.suffFuel s.size p.root < none32) :
    ∀ (steps attempt : Nat) (st : BtSt), attempt ≤ s.size →
      ScanAgrees p s mo start attempt steps
        (btLoop (compile p) s mo lim start steps attempt st) := by
  have hcov : Covered p.root := hw.1.covered
  have hnreg : 2 * (p.ncap + 1) ≤ (compile p).nregs := by
    show 2 * (p.ncap + 1) ≤ (p.ncap + 1) * 2 + (compile p).reps.size * 2
    omega
  have hsizereg :
      2 * (p.ncap + 1) ≤ (Array.replicate (compile p).nregs unset32).size := by
    rw [Array.size_replicate]
    exact hnreg
  intro steps
  induction steps with
  | zero =>
      intro attempt st _
      rw [btLoop]
      exact True.intro
  | succ steps ih =>
      intro attempt st hatt
      obtain ⟨ts, hden⟩ := Option.isSome_iff_exists.mp
        (denot_some (c := mctx (compile p) s mo) (novec := 2 * (p.ncap + 1))
          (fuel := Spec.suffFuel s.size p.root) (r0 := 0) (a := p.root)
          (pos := attempt) (regs := Array.replicate (compile p).nregs unset32)
          hatt hsizereg (Nat.le_refl _))
      rw [btLoop]
      simp only []
      split
      · exact True.intro
      · split
        next e st' heq =>
            obtain ⟨tsO, hthreads, hout⟩ :=
              attempt_refines hcov hw.2 hs rfl rfl hatt hwrap hden
                (by rw [heq]; rfl)
            -- The spec's first survivor is the thread the gate accepted.
            cases htsO : tsO with
            | nil =>
                rw [htsO] at hout
                exact absurd hout (by simp [OutAgrees])
            | cons t rest =>
                rw [htsO] at hout hthreads
                obtain ⟨hpos, hag0⟩ := hout
                have hag : Agree (2 * (p.ncap + 1)) st'.regs
                    ((t.regs.set! 0 attempt.toUInt32).set! 1
                      t.pos.toUInt32) := hag0
                have hsz : t.regs.size = 2 * (p.ncap + 1) := by
                  rw [Spec.attemptThreads] at hthreads
                  obtain ⟨ths, hths, hfil⟩ :=
                    Option.bind_eq_some_iff.mp hthreads
                  simp only [Option.pure_def, Option.some.injEq] at hfil
                  have hmem : t ∈ ths := by
                    have : t ∈ ths.filter (fun t =>
                        Spec.acceptable mo start attempt t && Spec.endOk p s t) :=
                      hfil ▸ List.mem_cons_self ..
                    exact (List.mem_filter.mp this).1
                  have := search_size hths t hmem
                  rw [this, Array.size_replicate]
                show Spec.scan (Spec.suffFuel s.size p.root) p s mo start
                  attempt (steps + 1) = _
                rw [Spec.scan.eq_def]
                simp only []
                rw [hthreads]
                show some (Spec.MatchAnswer.found
                  ((t.regs.set! 0 attempt.toUInt32).set! 1 t.pos.toUInt32)) = _
                rw [extract_eq_of_agree hag (by
                  simp only [Array.set!_eq_setIfInBounds,
                    Array.size_setIfInBounds]
                  exact hsz)]
        next st' heq => exact True.intro
        next st' heq =>
            obtain ⟨tsO, hthreads, hout⟩ :=
              attempt_refines hcov hw.2 hs rfl rfl hatt hwrap hden
                (by rw [heq]; rfl)
            have htsO : tsO = [] := by
              cases tsO with
              | nil => rfl
              | cons t rest => exact absurd hout (by simp [OutAgrees])
            rw [htsO] at hthreads
            have hanch : ((compile p).anchored || mo.anchored ||
                decide (attempt ≥ s.size)) =
                (p.opts.anchored || mo.anchored || decide (attempt ≥ s.size)) :=
              rfl
            split
            next hstop =>
                show Spec.scan (Spec.suffFuel s.size p.root) p s mo start
                  attempt (steps + 1) = _
                rw [Spec.scan.eq_def]
                simp only []
                rw [hthreads]
                show (if (p.opts.anchored || mo.anchored ||
                    decide (attempt ≥ s.size)) = true then
                      some Spec.MatchAnswer.notFound else _) = _
                rw [if_pos (by rw [← hanch]; exact hstop)]
            next hstop =>
                have hlt : attempt < s.size := by
                  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hstop
                  omega
                have hskip := skipsAttempt_agrees hw.1 s (attempt + 1)
                rw [hskip]
                have hnext : (if Spec.skipsAttempt p s (attempt + 1) then
                    attempt + 1 + 1 else attempt + 1) ≤ s.size := by
                  split
                  next hsk =>
                      have := Spec.skipsAttempt_lt hsk
                      omega
                  next => omega
                refine ScanAgrees.step ?_ (ih _ st' hnext)
                rw [Spec.scan.eq_def]
                simp only []
                rw [hthreads]
                show (if (p.opts.anchored || mo.anchored ||
                    decide (attempt ≥ s.size)) = true then
                      some Spec.MatchAnswer.notFound else _) = _
                rw [if_neg (by rw [← hanch]; exact hstop)]

/-! ## The target: S-8's backtracking half

Three reading notes on the side conditions. `Wf p` is the parser facts.
`s.size ≤ ceiling` resolves the one guard asymmetry honestly: `Spec.matchesF` answers BadInput for a
subject past the documented cap while `btRun` does not — that check
lives in `Exec`'s validation, not in the raw run — so the raw-run
statement carries the cap as a hypothesis, and the `Exec`-level
corollary can drop it. `suffFuel s.size p.root < none32` is the
counter-wrap bound: every count the search can reach is below the
sufficient fuel, so the machine's 32-bit counters never wrap nor collide
with the `none32` sentinel; it mentions the subject length, which is why
it is a hypothesis here rather than a `Wf` clause — and it always holds
for parser output on capped subjects, whose quantifiers stay at or below
65535. -/

/-- Whenever the metered backtracking run completes, its answer is the
spec's: found with the very ovector, no-match, and bad-input agreeing
under the guard hypotheses. -/
def BtRunRefinesMatches : Prop :=
  ∀ (p : Pat) (s : ByteArray) (start : Nat) (mo : MOpts) (lim : Limits)
    (btCap trailCap : Nat),
    Wf p → s.size ≤ ceiling →
    Spec.suffFuel s.size p.root < none32 →
    ((btRun (compile p) s start mo lim btCap trailCap).outcome =
        .matched →
      Spec.Matches p s start mo =
        .found (btRun (compile p) s start mo lim btCap trailCap).ovec) ∧
    ((btRun (compile p) s start mo lim btCap trailCap).outcome =
        .noMatch →
      Spec.Matches p s start mo = .notFound) ∧
    ((btRun (compile p) s start mo lim btCap trailCap).outcome =
        .badInput ↔
      Spec.Matches p s start mo = .badInput)

/-- S-8's backtracking half. The per-attempt theorem, the loop against
the scan, and the two guards: a start outside the subject is the only
BadInput either layer can answer under the documented cap, and a match
delivers the very ovector the spec computes. -/
theorem btRun_refines_matches : BtRunRefinesMatches := by
  intro p s start mo lim btCap trailCap hw hs hwrap
  by_cases hstart : start > s.size
  · -- Outside the subject both layers refuse at the door.
    have hbad : (btRun (compile p) s start mo lim btCap trailCap).outcome =
        .badInput := by
      rw [btRun, if_pos hstart]
    have hmb : Spec.Matches p s start mo = .badInput := by
      have hst := Spec.matches_stable p s start mo _ (Nat.le_refl _)
      have hcond : (decide (start > s.size) || decide (s.size > ceiling)) =
          true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl hstart
      rw [Spec.matchesF, if_pos hcond] at hst
      exact (Option.some.inj hst).symm
    exact ⟨by intro h; rw [hbad] at h; exact absurd h (by decide),
      by intro h; rw [hbad] at h; exact absurd h (by decide),
      by rw [hbad, hmb]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩
  · have hstart' : start ≤ s.size := by omega
    have hmf : Spec.scan (Spec.suffFuel s.size p.root) p s mo start start
        (s.size + 1 - start) = some (Spec.Matches p s start mo) := by
      have hst := Spec.matches_stable p s start mo _ (Nat.le_refl _)
      have hcond : ¬ (decide (start > s.size) || decide (s.size > ceiling)) =
          true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
        omega
      rwa [Spec.matchesF, if_neg hcond] at hst
    have hnb : Spec.Matches p s start mo ≠ .badInput := by
      intro hb
      rw [hb] at hmf
      exact scan_ne_badInput _ _ _ hmf rfl
    have hloop : ∀ (st : BtSt) (out : RunEnd),
        btLoop (compile p) s mo lim start (s.size + 1 - start) start st =
          out → ScanAgrees p s mo start start (s.size + 1 - start) out :=
      fun st out h => h ▸ btLoop_refines hw hs hwrap _ _ st hstart'
    rw [btRun, if_neg hstart]
    simp only []
    split
    · exact ⟨by intro h; simp at h, by intro h; simp at h,
        ⟨by intro h; simp at h, fun h => absurd h hnb⟩⟩
    · split
      next st heq =>
          have h1 := hloop _ _ heq
          rw [ScanAgrees] at h1
          split
          · exact ⟨by intro h; simp at h, by intro h; simp at h,
              ⟨by intro h; simp at h, fun h => absurd h hnb⟩⟩
          · refine ⟨fun _ => ?_, by intro h; simp at h,
              ⟨by intro h; simp at h, fun h => absurd h hnb⟩⟩
            rw [hmf] at h1
            exact Option.some.inj h1
      next st heq =>
          have h1 := hloop _ _ heq
          rw [ScanAgrees] at h1
          refine ⟨by intro h; simp at h, fun _ => ?_,
            ⟨by intro h; simp at h, fun h => absurd h hnb⟩⟩
          rw [hmf] at h1
          exact Option.some.inj h1
      next st heq =>
          exact ⟨by intro h; simp at h, by intro h; simp at h,
            ⟨by intro h; simp at h, fun h => absurd h hnb⟩⟩

end Pcrevera.Refine
