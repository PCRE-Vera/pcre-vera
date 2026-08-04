import Pcrevera.Ref.VM
import Pcrevera.Spec.Total
import Pcrevera.Proofs.Meter
import Pcrevera.Proofs.CrFirst
import Batteries.Tactic.OpenPrivate
import Batteries.Data.List.Basic

/-!
# The S-8 development: VM refinement (leaves, alternation, groups)

The compiler-correctness half of S-8, scaled up from the RefineProto
shape: whenever the backtracking VM completes an attempt — found or
exhausted, never exceeded — its answer is what `Spec.attemptThreads`
would filter out of the search. Covered here: every wave 1 construct
except repetitions that need the four Rep opcodes — bounded above one or
unbounded. The split-compiled repetition forms are in: `{0,0}` (compiles
to nothing), `hi = 1` with `lo = 1` (the body alone) and with `lo ≠ 1`
(the optional item's split, both greedinesses). Also in: all consuming
leaves including classes and
\R, the ten assertions, concatenation, non-empty alternation, and groups
with their capture registers; the accept gate carries the real
empty-match refusal and the ENDANCHORED eod-before-accept, matched
against the spec's `acceptable` and `endOk` filters.

The proto's architecture survives, with two structural upgrades:

* **Effects.** `eff` classifies what one instruction does — goto (with a
  register write folded in), fork, fail, deliver, or uncovered — so the
  mirror `run`/`dispatch`, monotonicity, and the frame laws
  (`runs_append`/`resumes_append`) case on five shapes instead of
  twenty-four opcodes, and `runs_eff` is the single one-step lemma every
  per-opcode fact reduces to. Every test in `eff` is copied from
  `btStep` verbatim; the metered bridge depends on that.

* **The trail discipline.** With `save` in play the machine writes
  registers through an undo trail, so a backtrack entry now decodes to
  the register file at push time: `snapAt` replays the trail above the
  entry's mark. Three lemmas carry the whole discipline — a mark at the
  top replays nothing (`snapAt_full`), a write-plus-undo pair cancels
  (`replay_push_cancel`), and replay factors through any intermediate
  mark (`replay_stage`) — and the `Sync` invariant packages them: files
  agree, the decoded stack is the pending list, marks sit at or below
  the trail's size and nondecreasing bottom to top.

The chain: `frag_runs` (fragment theorem over `FragAt`, which now pins
class-table rows semantically and group save brackets), `search_covered`
(`Spec.search` is the fuel-free `enum` on `Covered` input),
`compileNode_facts`/`compileAlt_facts` (the compiler establishes
`FragAt` under the `Grows` table discipline), `btStep_mirror` (the
metered bridge, on the VM's own fuel), and `attempt_refines` composing
them against `Spec.attemptThreads`.

`Covered` is this round's well-formedness predicate. Its one refusal
beyond the missing repetitions is the empty alternation: the compiler
emits nothing for `alt []`, which behaves like `nul`, while
`searchAlt []` matches nothing. The shape is representable — the corpus
decoder will happily build it — but the engine's parser never emits an
alternation without arms, and `Pat.Wf` will own the clause eventually.
Left for the next rounds:
counted repetitions proper and the whole-call level: `btLoop` against
`scan`, delivery, and the bumpalong analysis.

The redesign the Rep opcodes force is underway at the end of this file:
their counter registers live above the ovector, so the canonical pending
list can no longer be computed from spec threads alone. `Wf` states the
parser facts the full proof will assume; `denot` is the full-register
reference enumeration — `Spec.search` re-run with the counter writes the
VM makes, repetition indices threaded compile-style; and `denot_search`
is the ovector projection, proven for the whole wave 1 AST including the
general counted repetition with its empty-match rule: whatever `denot`
answers, `Spec.search` answers the same skeleton from any
ovector-agreeing file, on the same fuel. What remains for the Rep round
is the other half of the joint: `FragAt`/`Grows` cases for the compiled
Rep block, the mirror's four Rep effects, the fragment theorem restated
against `denot`, and the UInt32-versus-Nat counter bridge under the
`Wf`/fuel bounds.
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
  | .accept =>
      let empty := pos == attempt
      let refuse := empty &&
        (mo.notempty || (mo.notemptyAtStart && attempt == start))
      if refuse then .fail
      else .give ⟨pos, (regs.set! 0 attempt.toUInt32).set! 1 pos.toUInt32⟩
  | _ => .stuck

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

/-! ## The covered subset and its enumeration

`Covered` is this round's well-formedness predicate: everything but the
repetitions that compile to Rep opcodes, with one deliberate exclusion —
the empty alternation. The compiler emits nothing for `alt []`, which behaves like
`nul`, while `searchAlt []` matches nothing; the engine's parser never
emits an alternation without arms, so `Covered` refuses the shape, and
the eventual `Pat.Wf` will discharge the same clause. -/

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

/-- The conventions the mirror reads, packed the way the spec wants them.
Every leaf-test alignment below is a projection of this record. -/
def mctx (re : Re) (s : ByteArray) (mo : MOpts) : Spec.SCtx :=
  ⟨s, re.nltype, re.bsrtype, mo.notbol, mo.noteol⟩

/-- Every match of a covered node, in preference order: `Spec.search`
with the fuel stripped — on this subset the search never spends any —
and the assertion family routed through `assertionHolds` exactly as the
spec's catch-all does. -/
def enum (c : Spec.SCtx) : Ast → Nat → Spec.Regs → List Spec.Thread
  | .nul, pos, regs => [⟨pos, regs⟩]
  | .chr b, pos, regs =>
      if pos < c.s.size && byteAt c.s pos == b then [⟨pos + 1, regs⟩] else []
  | .chrCI folded, pos, regs =>
      if pos < c.s.size && lowerByte (byteAt c.s pos) == folded then
        [⟨pos + 1, regs⟩] else []
  | .cls bits, pos, regs =>
      if pos < c.s.size && bits.has (byteAt c.s pos) then
        [⟨pos + 1, regs⟩] else []
  | .any, pos, regs => if pos < c.s.size then [⟨pos + 1, regs⟩] else []
  | .anyNoNL, pos, regs =>
      if pos < c.s.size && newlineAt c.s pos c.nl == 0 then
        [⟨pos + 1, regs⟩] else []
  | .bsr, pos, regs =>
      let eaten := bsrAt c.s pos c.bsr
      if eaten != 0 then [⟨pos + eaten, regs⟩] else []
  | .cat [], pos, regs => [⟨pos, regs⟩]
  | .cat (k :: kids), pos, regs =>
      (enum c k pos regs).flatMap fun t => enum c (.cat kids) t.pos t.regs
  | .alt [], _, _ => []
  | .alt (a :: arms), pos, regs =>
      enum c a pos regs ++ enum c (.alt arms) pos regs
  | .grp cap body, pos, regs =>
      let opened := if cap != 0 then regs.set! (2 * cap) pos.toUInt32 else regs
      (enum c body pos opened).map fun t =>
        if cap != 0 then ⟨t.pos, t.regs.set! (2 * cap + 1) t.pos.toUInt32⟩
        else t
  | .rep _ (some 0) _ _, pos, regs => [⟨pos, regs⟩]
  | .rep lo (some 1) greedy body, pos, regs =>
      if lo == 1 then enum c body pos regs
      else if greedy then enum c body pos regs ++ [⟨pos, regs⟩]
      else ⟨pos, regs⟩ :: enum c body pos regs
  | .rep _ _ _ _, _, _ => []
  | a, pos, regs => if Spec.assertionHolds c a pos then [⟨pos, regs⟩] else []

/-! ## The fragment relation

Where a covered node's compiled form sits: one cell per leaf, juxtaposed
cat pieces, the split/branch/jump chain, and a group's optional save
brackets. A class leaf also pins its slice of the class table — not cell
by cell but semantically, as the membership test the VM will actually
run, which is the only thing the fragment theorem needs and the only
thing that survives table growth. -/

inductive FragAt (code : Array Inst) (classes : Array UInt8) :
    Ast → Nat → Nat → Prop where
  | nul {lo : Nat} : FragAt code classes .nul lo lo
  | chr {b : UInt8} {lo : Nat}
      (hcell : code[lo]! = ⟨.chr, b.toNat, 0⟩) :
      FragAt code classes (.chr b) lo (lo + 1)
  | chrCI {folded : UInt8} {lo : Nat}
      (hcell : code[lo]! = ⟨.chrCI, folded.toNat, 0⟩) :
      FragAt code classes (.chrCI folded) lo (lo + 1)
  | cls {bits : ClassBits} {idx lo : Nat}
      (hcell : code[lo]! = ⟨.cls, idx, 0⟩)
      (hblob : idx * 32 + 32 ≤ classes.size)
      (hsem : ∀ b : UInt8,
        (classes[idx * 32 + (b >>> 3).toNat]! &&& (1 <<< (b &&& 7)) != 0) =
          bits.has b) :
      FragAt code classes (.cls bits) lo (lo + 1)
  | any {lo : Nat} (hcell : code[lo]! = ⟨.any, 0, 0⟩) :
      FragAt code classes .any lo (lo + 1)
  | anyNoNL {lo : Nat} (hcell : code[lo]! = ⟨.anyNoNL, 0, 0⟩) :
      FragAt code classes .anyNoNL lo (lo + 1)
  | bsr {lo : Nat} (hcell : code[lo]! = ⟨.bsr, 0, 0⟩) :
      FragAt code classes .bsr lo (lo + 1)
  | assn {a : Ast} {op : Op} {lo : Nat}
      (ha : assnOp a = some op) (hcell : code[lo]! = ⟨op, 0, 0⟩) :
      FragAt code classes a lo (lo + 1)
  | catNil {lo : Nat} : FragAt code classes (.cat []) lo lo
  | catCons {k : Ast} {kids : List Ast} {lo mid hi : Nat}
      (hk : FragAt code classes k lo mid)
      (hkids : FragAt code classes (.cat kids) mid hi) :
      FragAt code classes (.cat (k :: kids)) lo hi
  | altOne {a : Ast} {lo hi : Nat}
      (ha : FragAt code classes a lo hi) :
      FragAt code classes (.alt [a]) lo hi
  | altCons {a b : Ast} {rest : List Ast} {lo j hi : Nat}
      (hsplit : code[lo]! = ⟨.split, lo + 1, j + 1⟩)
      (ha : FragAt code classes a (lo + 1) j)
      (hjump : code[j]! = ⟨.jump, hi, 0⟩)
      (hrest : FragAt code classes (.alt (b :: rest)) (j + 1) hi) :
      FragAt code classes (.alt (a :: b :: rest)) lo hi
  | grpZero {body : Ast} {lo hi : Nat}
      (hbody : FragAt code classes body lo hi) :
      FragAt code classes (.grp 0 body) lo hi
  | grpCap {cap : Nat} {body : Ast} {lo j : Nat}
      (hcap : cap ≠ 0)
      (hopen : code[lo]! = ⟨.save, 2 * cap, 0⟩)
      (hbody : FragAt code classes body (lo + 1) j)
      (hclose : code[j]! = ⟨.save, 2 * cap + 1, 0⟩) :
      FragAt code classes (.grp cap body) lo (j + 1)
  | repNone {lo' : Nat} {greedy : Bool} {body : Ast} {lo : Nat} :
      FragAt code classes (.rep lo' (some 0) greedy body) lo lo
  | repOne {greedy : Bool} {body : Ast} {lo hi : Nat}
      (hbody : FragAt code classes body lo hi) :
      FragAt code classes (.rep 1 (some 1) greedy body) lo hi
  | repOpt {lo' : Nat} {greedy : Bool} {body : Ast} {sp j : Nat}
      (hlo : lo' ≠ 1)
      (hsplit : code[sp]! =
        (if greedy then ⟨.split, sp + 1, j⟩ else ⟨.split, j, sp + 1⟩))
      (hbody : FragAt code classes body (sp + 1) j) :
      FragAt code classes (.rep lo' (some 1) greedy body) sp j

/-- The byte's high-bit index stays inside a 32-byte class row. -/
private theorem shr3_lt (b : UInt8) : (b >>> 3).toNat < 32 := by
  have hb : b.toNat < 256 := b.toNat_lt
  have : (b >>> 3).toNat = b.toNat / 8 := by
    rw [UInt8.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  omega

theorem FragAt.le {code : Array Inst} {classes : Array UInt8} {a : Ast}
    {lo hi : Nat} (h : FragAt code classes a lo hi) : lo ≤ hi := by
  induction h <;> omega

/-- A fragment only pins code cells inside its range and class cells
below the table's size, so any code that agrees there — and any larger
table that preserves the prefix — carries the same fragment. -/
theorem FragAt.mono {code code' : Array Inst} {classes classes' : Array UInt8}
    {a : Ast} {lo hi : Nat} (h : FragAt code classes a lo hi)
    (hag : ∀ pc, lo ≤ pc → pc < hi → code'[pc]! = code[pc]!)
    (hcsz : classes.size ≤ classes'.size)
    (hcag : ∀ j, j < classes.size → classes'[j]! = classes[j]!) :
    FragAt code' classes' a lo hi := by
  induction h with
  | nul => exact .nul
  | chr hcell =>
      exact .chr ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | chrCI hcell =>
      exact .chrCI ((hag _ (Nat.le_refl _) (Nat.lt_succ_self _)).trans hcell)
  | @cls bits idx lo hcell hblob hsem =>
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

/-- A fragment derivation is a subset witness. -/
theorem FragAt.covered {code : Array Inst} {classes : Array UInt8} {a : Ast}
    {lo hi : Nat} (h : FragAt code classes a lo hi) : Covered a := by
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

/-! ## The fragment theorem -/

section Frag

variable {re : Re} {s : ByteArray} {mo : MOpts} {start attempt : Nat}

/-- The assertion family's enumeration, computed once for all ten. -/
theorem enum_assn {c : Spec.SCtx} {a : Ast} {op : Op}
    (h : assnOp a = some op) (pos : Nat) (regs : Spec.Regs) :
    enum c a pos regs =
      if Spec.assertionHolds c a pos then [⟨pos, regs⟩] else [] := by
  cases a <;> simp only [assnOp] at h <;> try cases h
  all_goals rw [enum] <;> simp

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

/-- Continuing every pending thread of a fragment into its continuation:
the list-level engine of the cat case. -/
theorem resumes_bind {mid hi : Nat} {f : Spec.Thread → List Spec.Thread}
    (hpt : ∀ (t : Spec.Thread) (stk : List Entry) (r : Out),
      Runs re s mo start attempt mid t.pos t.regs stk r ↔
      Resumes re s mo start attempt (((f t).map fun u => (hi, u)) ++ stk) r) :
    ∀ (ts : List Spec.Thread) (stk : List Entry) (r : Out),
      Resumes re s mo start attempt ((ts.map fun t => (mid, t)) ++ stk) r ↔
      Resumes re s mo start attempt
        (((ts.flatMap f).map fun u => (hi, u)) ++ stk) r := by
  intro ts
  induction ts with
  | nil => intro stk r; simp
  | cons t ts ihp =>
      intro stk r
      simp only [List.map_cons, List.cons_append, resumes_cons]
      rw [hpt]
      rw [resumes_congr_tail fun r' => ihp stk r']
      simp [List.flatMap_cons, List.map_append, List.append_assoc]

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

/-- The fragment theorem: running the mirror from a fragment's entry with
any pending stack behaves exactly like queuing the spec's matches —
retargeted at the fragment's exit — in front of that stack. -/
theorem frag_runs {a : Ast} {lo hi : Nat}
    (h : FragAt re.code re.classes a lo hi) :
    ∀ (pos : Nat) (regs : Spec.Regs) (stk : List Entry) (r : Out),
      Runs re s mo start attempt lo pos regs stk r ↔
      Resumes re s mo start attempt
        (((enum (mctx re s mo) a pos regs).map fun t => (hi, t)) ++ stk) r := by
  induction h with
  | nul =>
      intro pos regs stk r
      simp only [enum, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | @chr b lo hcell =>
      intro pos regs stk r
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && byteAt s pos == b then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell, UInt8.ofNat_toNat]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      simp [enum, mctx]
  | @chrCI folded lo hcell =>
      intro pos regs stk r
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && lowerByte (byteAt s pos) == folded then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell, UInt8.ofNat_toNat]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      simp [enum, mctx]
  | @cls bits idx lo hcell hblob hsem =>
      intro pos regs stk r
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
      simp [enum, mctx]
  | @any lo hcell =>
      intro pos regs stk r
      have heff : eff re s mo start attempt lo pos regs =
          if decide (pos < s.size) then .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      simp [enum, mctx]
  | @anyNoNL lo hcell =>
      intro pos regs stk r
      have heff : eff re s mo start attempt lo pos regs =
          if pos < s.size && newlineAt s pos re.nltype == 0 then
            .goto (lo + 1) (pos + 1) regs
          else .fail := by
        simp [eff, hcell]
      rw [frag_leaf (t := ⟨pos + 1, regs⟩) heff]
      simp [enum, mctx]
  | @bsr lo hcell =>
      intro pos regs stk r
      have heff : eff re s mo start attempt lo pos regs =
          if bsrAt s pos re.bsrtype != 0 then
            .goto (lo + 1) (pos + bsrAt s pos re.bsrtype) regs
          else .fail := by
        simp [eff, hcell]
      rw [frag_leaf (t := ⟨pos + bsrAt s pos re.bsrtype, regs⟩) heff]
      simp [enum, mctx]
  | @assn a op lo ha hcell =>
      intro pos regs stk r
      rw [frag_leaf (t := ⟨pos, regs⟩) (eff_assn ha hcell), enum_assn ha]
  | catNil =>
      intro pos regs stk r
      simp only [enum, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | @catCons k kids lo mid hi hk hkids ihk ihkids =>
      intro pos regs stk r
      rw [ihk pos regs stk r]
      have := resumes_bind (fun t stk' r' => ihkids t.pos t.regs stk' r')
        (enum (mctx re s mo) k pos regs) stk r
      simpa only [enum] using this
  | @altOne a lo hi ha iha =>
      intro pos regs stk r
      rw [iha pos regs stk r]
      simp [enum]
  | @altCons a b rest lo j hi hsplit ha hjump hrest iha ihrest =>
      intro pos regs stk r
      have heff : eff re s mo start attempt lo pos regs =
          .fork (lo + 1) (j + 1) := by
        simp [eff, hsplit]
      rw [runs_eff, heff]
      simp only [Eff.judg]
      rw [iha pos regs ((j + 1, (⟨pos, regs⟩ : Spec.Thread)) :: stk) r]
      have hjt : ∀ (t : Spec.Thread) (stk' : List Entry) (r' : Out),
          Runs re s mo start attempt j t.pos t.regs stk' r' ↔
          Runs re s mo start attempt hi (id t).pos (id t).regs stk' r' := by
        intro t stk' r'
        have heffj : eff re s mo start attempt j t.pos t.regs =
            .goto hi t.pos t.regs := by
          simp [eff, hjump]
        rw [runs_eff, heffj]
        exact Iff.rfl
      rw [resumes_retarget hjt (enum (mctx re s mo) a pos regs) _ r]
      have hstep : ∀ r', Resumes re s mo start attempt
          ((j + 1, (⟨pos, regs⟩ : Spec.Thread)) :: stk) r' ↔
          Resumes re s mo start attempt
            (((enum (mctx re s mo) (Ast.alt (b :: rest)) pos regs).map
              fun t => (hi, t)) ++ stk) r' := by
        intro r'
        rw [resumes_cons]
        exact ihrest pos regs stk r'
      refine Iff.trans (resumes_congr_tail hstep) ?_
      simp [enum, List.map_append, List.append_assoc]
  | @grpZero body lo hi hbody ihbody =>
      intro pos regs stk r
      rw [ihbody pos regs stk r]
      simp [enum]
  | @grpCap cap body lo j hcap hopen hbody hclose ihbody =>
      intro pos regs stk r
      have hcap' : (cap != 0) = true := by simpa using hcap
      have heff : eff re s mo start attempt lo pos regs =
          .goto (lo + 1) pos (regs.set! (2 * cap) pos.toUInt32) := by
        simp [eff, hopen]
      rw [runs_eff, heff]
      simp only [Eff.judg]
      rw [ihbody pos (regs.set! (2 * cap) pos.toUInt32) stk r]
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
      rw [resumes_retarget hstep
        (enum (mctx re s mo) body pos (regs.set! (2 * cap) pos.toUInt32)) stk r]
      simp [enum, hcap', List.map_map, Function.comp_def]
  | repNone =>
      intro pos regs stk r
      simp only [enum, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, resumes_cons]
  | repOne hbody ihbody =>
      intro pos regs stk r
      rw [ihbody pos regs stk r]
      simp [enum]
  | @repOpt lo' greedy body sp j hlo hsplit hbody ihbody =>
      intro pos regs stk r
      have hlo' : (lo' == 1) = false := by simp [hlo]
      cases greedy with
      | true =>
          rw [if_pos rfl] at hsplit
          have heff : eff re s mo start attempt sp pos regs =
              .fork (sp + 1) j := by
            simp [eff, hsplit]
          rw [runs_eff, heff]
          simp only [Eff.judg]
          rw [ihbody pos regs ((j, (⟨pos, regs⟩ : Spec.Thread)) :: stk) r]
          simp [enum, hlo', List.map_append, List.append_assoc]
      | false =>
          rw [if_neg (by simp)] at hsplit
          have heff : eff re s mo start attempt sp pos regs =
              .fork j (sp + 1) := by
            simp [eff, hsplit]
          rw [runs_eff, heff]
          simp only [Eff.judg]
          rw [runs_congr_stack (L₂ :=
            (((enum (mctx re s mo) body pos regs).map fun t => (j, t)) ++ stk))
            (fun r' => by
              rw [resumes_cons]
              exact ihbody pos regs stk r')]
          simp only [enum, hlo', Bool.false_eq_true, if_false,
            List.map_cons, List.cons_append]
          exact (resumes_cons (t := ⟨pos, regs⟩)).symm

end Frag

/-! ## The spec side: `enum` is `Spec.search` on the covered subset -/

/-- The assertion family's search, computed once for all ten. -/
theorem search_assn {c : Spec.SCtx} {a : Ast} {op : Op}
    (h : assnOp a = some op) (fuel pos : Nat) (regs : Spec.Regs) :
    Spec.search fuel c a pos regs =
      some (if Spec.assertionHolds c a pos then [⟨pos, regs⟩] else []) := by
  cases a <;> simp only [assnOp] at h <;> try cases h
  all_goals rw [Spec.search] <;> simp

/-- `mapM` over a list every element of which succeeds. -/
theorem mapM_eq_some {α β : Type _} {f : α → Option β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.mapM_cons, h x (List.mem_cons_self ..),
        mapM_eq_some xs fun y hy => h y (List.mem_cons_of_mem x hy)]
      rfl

/-- On the covered subset the spec search spends no fuel and answers the
enumeration, registers and all. -/
theorem search_covered {c : Spec.SCtx} {a : Ast} (h : Covered a) :
    ∀ (fuel pos : Nat) (regs : Spec.Regs),
      Spec.search fuel c a pos regs = some (enum c a pos regs) := by
  induction h with
  | nul =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | chr b =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | chrCI folded =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | cls bits =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | any =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | anyNoNL =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | bsr =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | assn ha =>
      intro fuel pos regs
      rw [search_assn ha, enum_assn ha]
  | catNil =>
      intro fuel pos regs
      rw [Spec.search, Spec.searchCat, enum]
  | @catCons k kids hck hckids ihk ihkids =>
      intro fuel pos regs
      have ihkids' : ∀ (pos' : Nat) (regs' : Spec.Regs),
          Spec.searchCat fuel c kids pos' regs' =
            some (enum c (.cat kids) pos' regs') := by
        intro pos' regs'
        have := ihkids fuel pos' regs'
        rwa [Spec.search] at this
      rw [Spec.search, Spec.searchCat, ihk fuel pos regs]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind]
      rw [mapM_eq_some _ fun (t : Spec.Thread) _ => ihkids' t.pos t.regs]
      simp only [Option.some.injEq]
      rw [enum]
      simp [List.flatMap_def]
  | @altOne a hac iha =>
      intro fuel pos regs
      rw [Spec.search, Spec.searchAlt, iha fuel pos regs, Spec.searchAlt]
      simp [enum]
  | @altCons a b rest hac hrestc iha ihrest =>
      intro fuel pos regs
      have ihrest' : Spec.searchAlt fuel c (b :: rest) pos regs =
          some (enum c (.alt (b :: rest)) pos regs) := by
        have := ihrest fuel pos regs
        rwa [Spec.search] at this
      rw [Spec.search, Spec.searchAlt, iha fuel pos regs, ihrest']
      simp [enum]
  | @grp cap body hbc ihbody =>
      intro fuel pos regs
      rw [Spec.search,
        ihbody fuel pos (if cap != 0 then regs.set! (2 * cap) pos.toUInt32
          else regs)]
      rw [enum]
      rfl
  | repNone =>
      intro fuel pos regs
      rw [Spec.search, enum]
  | @repOne greedy body hbc ihbody =>
      intro fuel pos regs
      rw [Spec.search]
      simp only [beq_self_eq_true, if_true]
      rw [ihbody fuel pos regs, enum]
      simp
  | @repOpt lo greedy body hlo hbc ihbody =>
      intro fuel pos regs
      have hlo' : (lo == 1) = false := by simp [hlo]
      rw [Spec.search]
      simp only [hlo', Bool.false_eq_true, if_false]
      rw [ihbody fuel pos regs, enum]
      simp [hlo']

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

private theorem getBang_modify_ne (a : Array Inst) (j : Nat)
    {f : Inst → Inst} {i : Nat} (h : i ≠ j) :
    (a.modify j f)[i]! = a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos (a.modify j f) i (by simpa using hi),
      getElem!_pos a i hi]
    exact Array.getElem_modify_of_ne (Ne.symm h) f (by simpa using hi)
  · rw [getElem!_neg (a.modify j f) i (by simpa using hi),
      getElem!_neg a i hi]

private theorem getBang_modify_eq (a : Array Inst) (j : Nat)
    {f : Inst → Inst} (h : j < a.size) :
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

/-- What compiling any covered construct does to the tables: code grows
and keeps its prefix, the class table grows by whole 32-byte rows and
keeps its prefix, the repetition table is untouched. -/
structure Grows (st st' : CState) : Prop where
  code_le : st.code.size ≤ st'.code.size
  code_pre : ∀ pc, pc < st.code.size → st'.code[pc]! = st.code[pc]!
  cls_le : st.classes.size ≤ st'.classes.size
  cls_pre : ∀ j, j < st.classes.size → st'.classes[j]! = st.classes[j]!
  cls_mod : st.classes.size % 32 = 0 → st'.classes.size % 32 = 0
  reps_eq : st'.reps = st.reps

theorem Grows.refl (st : CState) : Grows st st :=
  ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, id, rfl⟩

theorem Grows.comp {st₁ st₂ st₃ : CState}
    (h₁ : Grows st₁ st₂) (h₂ : Grows st₂ st₃) : Grows st₁ st₃ :=
  ⟨Nat.le_trans h₁.code_le h₂.code_le,
   fun pc hpc => (h₂.code_pre pc (by have := h₁.code_le; omega)).trans
     (h₁.code_pre pc hpc),
   Nat.le_trans h₁.cls_le h₂.cls_le,
   fun j hj => (h₂.cls_pre j (by have := h₁.cls_le; omega)).trans
     (h₁.cls_pre j hj),
   fun h => h₂.cls_mod (h₁.cls_mod h),
   h₂.reps_eq.trans h₁.reps_eq⟩

/-- A finished fragment survives the rest of the compilation. -/
theorem FragAt.grow {st st' : CState} {a : Ast} {lo hi : Nat}
    (h : FragAt st.code st.classes a lo hi) (hg : Grows st st')
    (hhi : hi ≤ st.code.size) : FragAt st'.code st'.classes a lo hi :=
  h.mono (fun pc _ h2 => hg.code_pre pc (by omega)) hg.cls_le hg.cls_pre

/-- A single emitted instruction: the cell lands at the old end. -/
private theorem emit_facts (st : CState) (i : Inst) :
    Grows st (emit st i).1 ∧
    (emit st i).1.code[st.code.size]! = i ∧
    (emit st i).1.code.size = st.code.size + 1 := by
  refine ⟨⟨?_, ?_, Nat.le_refl _, fun _ _ => rfl, id, rfl⟩, ?_, ?_⟩
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
        (st.classes.size % 32 = 0 →
          FragAt (compileNode a here st).code (compileNode a here st).classes
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
        (compileAlt arm rest inside jumps st).reps = st.reps ∧
        (st.classes.size % 32 = 0 →
          FragAt (compileAlt arm rest inside jumps st).code
            (compileAlt arm rest inside jumps st).classes
            (.alt (arm :: rest)) st.code.size
            (compileAlt arm rest inside jumps st).code.size) := by
  intro rest
  induction rest with
  | nil =>
      intro arm hszarm hcarm _ inside jumps st hj
      obtain ⟨hg, hfrag⟩ :=
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
      have hgreps : (compileNode arm st.regions.size
          (altBranchSt inside st)).reps = st.reps := hg.reps_eq
      have hfrag' : st.classes.size % 32 = 0 →
          FragAt (compileNode arm st.regions.size (altBranchSt inside st)).code
            (compileNode arm st.regions.size (altBranchSt inside st)).classes
            arm st.code.size
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · rw [hreps, hgreps]
      · intro hmod
        rw [hsize, hclasses]
        refine .altOne ((hfrag' hmod).mono ?_ (Nat.le_refl _) fun _ _ => rfl)
        intro pc h1 h2
        rw [hcode]
        exact hfpre pc fun hin => absurd (hj pc hin) (by omega)
  | cons bb rest' ihrest =>
      intro arm hszarm hcarm helems inside jumps st hj
      rw [compileAlt_cons_eq]
      have hsplitsz : (altSplitSt st).code.size = st.code.size + 1 := by
        simp [altSplitSt]
      obtain ⟨hg, hfrag⟩ :=
        ih hszarm hcarm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st))
      have hmid : compileNode arm (altSplitSt st).regions.size
            (altBranchSt inside (altSplitSt st)) = altMid arm inside st := rfl
      rw [hmid] at hg hfrag
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
      have hgreps : (altMid arm inside st).reps = st.reps := hg.reps_eq
      have hfrag' : st.classes.size % 32 = 0 →
          FragAt (altMid arm inside st).code (altMid arm inside st).classes
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
      obtain ⟨cle, cpre, chit, ccle, ccpre, ccmod, creps, cfrag⟩ :=
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
      have hmem_push : ∀ p,
          p ∈ (jumps.push (altMid arm inside st).code.size).toList ↔
          (p ∈ jumps.toList ∨ p = (altMid arm inside st).code.size) := by
        intro p
        rw [Array.toList_push, List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · rw [creps, houtr, hgreps]
      · intro hmod
        refine .altCons (j := (altMid arm inside st).code.size) ?_ ?_ ?_ ?_
        · rw [cpre st.code.size (by omega) (by
              rw [hmem_push]
              rintro (h' | h')
              · have := hj st.code.size h'; omega
              · omega)]
          exact hout_split
        · refine ((hfrag' hmod).mono ?_ ?_ ?_)
          · intro pc h1 h2
            rw [cpre pc (by omega) (by
                  rw [hmem_push]
                  rintro (h' | h')
                  · have := hj pc h'; omega
                  · omega),
              hout_pre pc (by omega) (by omega)]
          · exact ccle
          · exact ccpre
        · have hcell := chit (altMid arm inside st).code.size
            ((hmem_push (altMid arm inside st).code.size).mpr (.inr rfl))
          rw [hcell, hout_jump]
        · exact cfrag (hgcmod hmod)

/-- Growth by table equality: a step that only touches regions. -/
private theorem grows_of_eq {st st' : CState} (hc : st'.code = st.code)
    (hcl : st'.classes = st.classes) (hr : st'.reps = st.reps) :
    Grows st st' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hr⟩
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

/-- Compiling a covered node: the tables grow by the `Grows` discipline,
and — as long as the class table arrived row-aligned — the new code range
is a fragment of the node. -/
theorem compileNode_facts :
    ∀ (n : Nat) {a : Ast}, sizeOf a ≤ n → Covered a →
    ∀ (here : Nat) (st : CState),
      Grows st (compileNode a here st) ∧
      (st.classes.size % 32 = 0 →
        FragAt (compileNode a here st).code (compileNode a here st).classes a
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
          exact ⟨Grows.refl st, fun _ => .nul⟩
      | chr b =>
          have hstep : compileNode (.chr b) here st =
              (emit st ⟨.chr, b.toNat, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.chr, b.toNat, 0⟩
          rw [hstep]
          exact ⟨hg, fun _ => hsz' ▸ .chr hcell⟩
      | chrCI folded =>
          have hstep : compileNode (.chrCI folded) here st =
              (emit st ⟨.chrCI, folded.toNat, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.chrCI, folded.toNat, 0⟩
          rw [hstep]
          exact ⟨hg, fun _ => hsz' ▸ .chrCI hcell⟩
      | any =>
          have hstep : compileNode .any here st =
              (emit st ⟨.any, 0, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.any, 0, 0⟩
          rw [hstep]
          exact ⟨hg, fun _ => hsz' ▸ .any hcell⟩
      | anyNoNL =>
          have hstep : compileNode .anyNoNL here st =
              (emit st ⟨.anyNoNL, 0, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.anyNoNL, 0, 0⟩
          rw [hstep]
          exact ⟨hg, fun _ => hsz' ▸ .anyNoNL hcell⟩
      | bsr =>
          have hstep : compileNode .bsr here st =
              (emit st ⟨.bsr, 0, 0⟩).1 := by rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨.bsr, 0, 0⟩
          rw [hstep]
          exact ⟨hg, fun _ => hsz' ▸ .bsr hcell⟩
      | @assn a' op ha =>
          have hstep := compileNode_assn ha here st
          obtain ⟨hg, hcell, hsz'⟩ := leaf ⟨op, 0, 0⟩
          rw [hstep]
          exact ⟨hg, fun _ => hsz' ▸ .assn ha hcell⟩
      | cls bits =>
          have hstep : compileNode (.cls bits) here st =
              (emit { st with classes := st.classes ++ bits.toArray }
                ⟨.cls, st.classes.size / 32, 0⟩).1 := by
            rw [compileNode]
          obtain ⟨hg, hcell, hsz'⟩ :=
            emit_facts { st with classes := st.classes ++ bits.toArray }
              ⟨.cls, st.classes.size / 32, 0⟩
          rw [hstep]
          constructor
          · refine Grows.comp
              (st₂ := { st with classes := st.classes ++ bits.toArray })
              ⟨Nat.le_refl _, fun _ _ => rfl, ?_, ?_, ?_, rfl⟩ hg
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
          exact ⟨Grows.refl st, fun _ => .catNil⟩
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
          obtain ⟨hg1, hfrag1⟩ := ih hszk.1 hck here st
          obtain ⟨hg2, hfrag2⟩ :=
            ih hszk.2 hckids here (compileNode k here st)
          rw [hstep]
          refine ⟨Grows.comp hg1 hg2, ?_⟩
          intro hmod
          exact .catCons
            ((hfrag1 hmod).grow hg2 (Nat.le_refl _))
            (hfrag2 (hg1.cls_mod hmod))
      | @altOne a1 hca =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have hstep : compileNode (.alt [a1]) here st =
              compileNode a1 here st := by
            rw [compileNode]
          obtain ⟨hg, hfrag⟩ := ih hsza hca here st
          rw [hstep]
          exact ⟨hg, fun hmod => .altOne (hfrag hmod)⟩
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
          obtain ⟨h1, h2, _, h4, h5, h6, h7, h8⟩ :=
            compileAlt_facts (fun h hc => ih h hc) (b :: rest) a1 hsza hca
              helems st.regions.size #[]
              { st with regions := (st.regions.push
                  ⟨.alt, here, st.code.size, st.code.size⟩) }
              (by simp)
          rw [hstep]
          refine ⟨⟨h1, fun pc hpc => h2 pc hpc (by simp), h4, h5, h6, h7⟩, ?_⟩
          intro hmod
          exact h8 hmod
      | @grp cap body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          by_cases hcap : (cap != 0) = true
          · rw [compileNode_grp_pos body here st hcap]
            obtain ⟨hgo, hocell, hosz⟩ :=
              emit_facts (grpSt here st) ⟨.save, 2 * cap, 0⟩
            obtain ⟨hgb, hfragb⟩ := ih hszb hcbody st.regions.size
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
                  body (st.code.size + 1)
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
            constructor
            · exact Grows.comp hgo'
                (Grows.comp hgb (Grows.comp hgc
                  (grows_of_eq hdc hdcl hdr)))
            · intro hmod
              rw [hdc, hdcl, hcsz]
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
            obtain ⟨hgb, hfragb⟩ :=
              ih hszb hcbody st.regions.size (grpSt here st)
            obtain ⟨hdc, hdcl, hdr⟩ := finish_tables
              (compileNode body st.regions.size (grpSt here st))
              st.regions.size
            have hfragb' : st.classes.size % 32 = 0 →
                FragAt (compileNode body st.regions.size (grpSt here st)).code
                  (compileNode body st.regions.size (grpSt here st)).classes
                  body st.code.size
                  (compileNode body st.regions.size
                    (grpSt here st)).code.size := hfragb
            constructor
            · exact Grows.comp
                (grows_of_eq (st := st) (st' := grpSt here st) rfl rfl rfl)
                (Grows.comp hgb (grows_of_eq hdc hdcl hdr))
            · intro hmod
              rw [hdc, hdcl]
              exact .grpZero (hfragb' hmod)
      | @repNone lo greedy body =>
          have hstep : compileNode (.rep lo (some 0) greedy body) here st =
              st := by
            rw [compileNode]
          rw [hstep]
          exact ⟨Grows.refl st, fun _ => .repNone⟩
      | @repOne greedy body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hstep : compileNode (.rep 1 (some 1) greedy body) here st =
              compileNode body here st := by
            rw [compileNode]
            simp
          obtain ⟨hg, hfrag⟩ := ih hszb hcbody here st
          rw [hstep]
          exact ⟨hg, fun hmod => .repOne (hfrag hmod)⟩
      | @repOpt lo greedy body hlo hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hlo' : (lo == 1) = false := by simp [hlo]
          rw [compileNode_repOpt_eq greedy body here st hlo']
          have hrsz : (repOptSt here st).code.size = st.code.size + 1 := by
            simp [repOptSt]
          obtain ⟨hg, hfrag⟩ :=
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
          have hgreps : (compileNode body st.regions.size
              (repOptSt here st)).reps = st.reps := hg.reps_eq
          have hfrag' : st.classes.size % 32 = 0 →
              FragAt (compileNode body st.regions.size
                  (repOptSt here st)).code
                (compileNode body st.regions.size (repOptSt here st)).classes
                body (st.code.size + 1)
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
          constructor
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
            · exact hgreps
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
            · refine ((hfrag' hmod).mono ?_ (Nat.le_refl _) fun _ _ => rfl)
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

/-- The opcodes this round covers: everything but the four counted
repetition instructions. Reads past the end answer the default cell,
whose opcode is `chr`, so the predicate holds there vacuously. -/
def SubsetOp (op : Op) : Prop :=
  op ≠ .repZero ∧ op ≠ .repLoop ∧ op ≠ .repEnter ∧ op ≠ .repNext

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
    {start attempt : Nat}
    (hsub : ∀ pc : Nat, SubsetOp (re.code[pc]!).op) :
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
        cases hop : (re.code[pc]!).op
        case repZero => exact absurd hop (hsub pc).1
        case repLoop => exact absurd hop (hsub pc).2.1
        case repEnter => exact absurd hop (hsub pc).2.2.1
        case repNext => exact absurd hop (hsub pc).2.2.2
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
              obtain ⟨hbt2, htr2, hrg2⟩ := fork_shape hf
              have hbt2' : st2.bt =
                  st.bt.push ⟨(re.code[pc]!).alt, pos, st.trail.size⟩ := hbt2
              have htr2' : st2.trail = st.trail := htr2
              have hrg2' : st2.regs = st.regs := hrg2
              refine ih (re.code[pc]!).arg pos st2 regs
                ((((re.code[pc]!).alt, ⟨pos, regs⟩) : Entry) :: stk)
                ⟨?_, ?_, ?_, ?_⟩ r h
              · rw [hrg2', hregs]
              · rw [htr2', hrg2', hbt2', stackOf_push, hstack, hregs]
              · intro e he
                rw [htr2']
                rw [hbt2', Array.toList_push] at he
                rcases List.mem_append.mp he with he' | he'
                · exact hmle e he'
                · rw [List.mem_singleton] at he'
                  subst he'
                  exact Nat.le_refl _
              · rw [hbt2', Array.toList_push, List.pairwise_append]
                refine ⟨hmmono, by simp, ?_⟩
                intro a ha b hb
                rw [List.mem_singleton] at hb
                subst hb
                exact hmle a ha
        case save =>
          simp only [hop] at h
          rw [run]
          simp only [eff, hop]
          cases hw : writeReg { st with m := { st.m with cost := st.m.cost + 1 } }
              lim (re.code[pc]!).arg pos.toUInt32 with
          | none => rw [hw] at h; simp [verdict] at h
          | some st2 =>
              rw [hw] at h
              obtain ⟨hrg2, hbt2, htr2⟩ := writeReg_shape hw
              have hrg2' : st2.regs =
                  st.regs.set! (re.code[pc]!).arg pos.toUInt32 := hrg2
              have hbt2' : st2.bt = st.bt := hbt2
              refine ih (pc + 1) pos st2
                (regs.set! (re.code[pc]!).arg pos.toUInt32) stk
                ⟨?_, ?_, ?_, ?_⟩ r h
              · rw [hrg2', hregs]
              · rcases htr2 with ⟨_, htr⟩ | ⟨hzero, htr⟩
                · have htr' : st2.trail = st.trail.push
                      ⟨(re.code[pc]!).arg,
                        st.regs[(re.code[pc]!).arg]!⟩ := htr
                  rw [htr', hbt2', hrg2',
                    stackOf_write st.trail st.regs st.bt _ _ hmle, hstack]
                · have htr' : st2.trail = st.trail := htr
                  have hzero' : st.bt.size = 0 := hzero
                  have hbt0 : st.bt = #[] := Array.size_eq_zero_iff.mp hzero'
                  rw [htr', hbt2', hrg2', hbt0]
                  rw [hbt0] at hstack
                  rw [← hstack]
                  rfl
              · intro e he
                rw [hbt2'] at he
                rcases htr2 with ⟨_, htr⟩ | ⟨_, htr⟩
                · have htr' : st2.trail = st.trail.push
                      ⟨(re.code[pc]!).arg,
                        st.regs[(re.code[pc]!).arg]!⟩ := htr
                  rw [htr']
                  have := hmle e he
                  simp
                  omega
                · have htr' : st2.trail = st.trail := htr
                  rw [htr']
                  exact hmle e he
              · rw [hbt2']
                exact hmmono
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

/-- Every cell a fragment pins is a covered opcode. -/
theorem FragAt.ops {code : Array Inst} {classes : Array UInt8} {a : Ast}
    {lo hi : Nat} (h : FragAt code classes a lo hi) :
    ∀ pc, lo ≤ pc → pc < hi → SubsetOp (code[pc]!).op := by
  induction h with
  | nul => intro pc h1 h2; omega
  | @chr b lo hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      simp [SubsetOp]
  | @chrCI folded lo hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      simp [SubsetOp]
  | @cls bits idx lo hcell _ _ =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      simp [SubsetOp]
  | @any lo hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      simp [SubsetOp]
  | @anyNoNL lo hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      simp [SubsetOp]
  | @bsr lo hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      simp [SubsetOp]
  | @assn a op lo ha hcell =>
      intro pc h1 h2
      have hpc : pc = lo := by omega
      subst hpc
      rw [hcell]
      cases a <;> simp only [assnOp] at ha <;> try cases ha
      all_goals simp [SubsetOp]
  | catNil => intro pc h1 h2; omega
  | @catCons k kids lo mid hi hk hkids ihk ihkids =>
      intro pc h1 h2
      by_cases hcut : pc < mid
      · exact ihk pc h1 hcut
      · exact ihkids pc (by omega) h2
  | altOne ha iha => exact iha
  | @altCons a b rest lo j hi hsplit ha hjump hrest iha ihrest =>
      intro pc h1 h2
      have hb1 := ha.le
      have hb2 := hrest.le
      by_cases hlo : pc = lo
      · subst hlo
        rw [hsplit]
        simp [SubsetOp]
      · by_cases hltj : pc < j
        · exact iha pc (by omega) hltj
        · by_cases hjq : pc = j
          · subst hjq
            rw [hjump]
            simp [SubsetOp]
          · exact ihrest pc (by omega) h2
  | grpZero hbody ihbody => exact ihbody
  | @grpCap cap body lo j hcap hopen hbody hclose ihbody =>
      intro pc h1 h2
      have hb1 := hbody.le
      by_cases hlo : pc = lo
      · subst hlo
        rw [hopen]
        simp [SubsetOp]
      · by_cases hltj : pc < j
        · exact ihbody pc (by omega) hltj
        · have hpc : pc = j := by omega
          subst hpc
          rw [hclose]
          simp [SubsetOp]
  | repNone => intro pc h1 h2; omega
  | repOne hbody ihbody => exact ihbody
  | @repOpt lo' greedy body sp j hlo hsplit hbody ihbody =>
      intro pc h1 h2
      have hb := hbody.le
      by_cases hpc : pc = sp
      · subst hpc
        rw [hsplit]
        cases greedy <;> simp [SubsetOp]
      · exact ihbody pc (by omega) h2

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

/-- The compiled form of a covered pattern: the root's fragment from 0,
then the optional ENDANCHORED `eod` assertion, then `accept` — and no
uncovered opcode anywhere, the out-of-range default cell included. -/
theorem compile_shape {p : Pat} (hc : Covered p.root) :
    FragAt (compile p).code (compile p).classes p.root 0
      (compileNode p.root 0 rootSt).code.size ∧
    (∀ pc : Nat, SubsetOp ((compile p).code[pc]!).op) ∧
    (p.opts.endanchored = false →
      (compile p).code[(compileNode p.root 0 rootSt).code.size]! =
        ⟨.accept, 0, 0⟩) ∧
    (p.opts.endanchored = true →
      (compile p).code[(compileNode p.root 0 rootSt).code.size]! =
        ⟨.eod, 0, 0⟩ ∧
      (compile p).code[(compileNode p.root 0 rootSt).code.size + 1]! =
        ⟨.accept, 0, 0⟩) := by
  obtain ⟨⟨hopen, hanch⟩, hclasses, _⟩ := compile_code (p := p)
  obtain ⟨hg, hfrag⟩ :=
    compileNode_facts (sizeOf p.root) (Nat.le_refl _) hc 0 rootSt
  have hfrag' : FragAt (compileNode p.root 0 rootSt).code
      (compileNode p.root 0 rootSt).classes p.root 0
      (compileNode p.root 0 rootSt).code.size := hfrag (by rfl)
  have hfragc : FragAt (compile p).code (compile p).classes p.root 0
      (compileNode p.root 0 rootSt).code.size := by
    refine hfrag'.mono ?_ ?_ ?_
    · intro pc _ h2
      by_cases hend : p.opts.endanchored = true
      · rw [hanch hend, getBang_push_lt _ _ (by simp; omega),
          getBang_push_lt _ _ h2]
      · rw [hopen (eq_false_of_ne_true hend), getBang_push_lt _ _ h2]
    · rw [hclasses]
      exact Nat.le_refl _
    · intro j _
      rw [hclasses]
  refine ⟨hfragc, ?_, ?_, ?_⟩
  · intro pc
    by_cases hlt : pc < (compileNode p.root 0 rootSt).code.size
    · exact hfragc.ops pc (Nat.zero_le _) hlt
    · by_cases hend : p.opts.endanchored = true
      · rw [hanch hend]
        by_cases h1 : pc = (compileNode p.root 0 rootSt).code.size
        · subst h1
          rw [getBang_push_lt _ _ (by simp), getBang_push_eq]
          simp [SubsetOp]
        · by_cases h2 : pc = (compileNode p.root 0 rootSt).code.size + 1
          · subst h2
            rw [show (compileNode p.root 0 rootSt).code.size + 1 =
                ((compileNode p.root 0 rootSt).code.push
                  ⟨.eod, 0, 0⟩).size from by simp,
              getBang_push_eq]
            simp [SubsetOp]
          · rw [getElem!_neg _ pc (by simp; omega)]
            show SubsetOp (default : Inst).op
            exact ⟨by decide, by decide, by decide, by decide⟩
      · rw [hopen (eq_false_of_ne_true hend)]
        by_cases h1 : pc = (compileNode p.root 0 rootSt).code.size
        · subst h1
          rw [getBang_push_eq]
          simp [SubsetOp]
        · rw [getElem!_neg _ pc (by simp; omega)]
          show SubsetOp (default : Inst).op
          exact ⟨by decide, by decide, by decide, by decide⟩
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

/-- This round's S-8, per attempt: on a covered pattern — leaves,
alternations, groups; both empty-match refusals live; ENDANCHORED in
either state — a completed `btStep` attempt from the compiled entry
answers exactly what `Spec.attemptThreads` filters out of the search:
found on its head thread with the ovector slots written, or no-match
when no thread survives. Resource questions never enter: `verdict … =
some r` is precisely "the attempt completed". -/
theorem attempt_refines {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start attempt fuel : Nat} {st : BtSt} {r : Out}
    (hc : Covered p.root)
    (hbt : st.bt = #[])
    (hregs : st.regs = Array.replicate (2 * (p.ncap + 1)) unset32)
    (h : verdict (btStep (compile p) s mo lim start attempt fuel 0 attempt
      st) = some r) :
    ∀ F : Nat,
      Spec.attemptThreads F p s mo start attempt = some
        ((enum ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root attempt
          (Array.replicate (2 * (p.ncap + 1)) unset32)).filter
          (gateKeep p s mo start attempt)) ∧
      r = gateOut attempt
        ((enum ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root attempt
          (Array.replicate (2 * (p.ncap + 1)) unset32)).filter
          (gateKeep p s mo start attempt)) := by
  obtain ⟨hfrag, hsub, hopen, hanch⟩ := compile_shape hc
  have hsync : Sync st (Array.replicate (2 * (p.ncap + 1)) unset32) [] := by
    refine ⟨hregs, ?_, ?_, ?_⟩
    · rw [hbt]
      rfl
    · intro e he
      rw [hbt] at he
      simp at he
    · rw [hbt]
      simp
  have hrun := btStep_mirror hsub fuel 0 attempt st
    (Array.replicate (2 * (p.ncap + 1)) unset32) [] hsync r h
  have hruns : Runs (compile p) s mo start attempt 0 attempt
      (Array.replicate (2 * (p.ncap + 1)) unset32) [] r := ⟨fuel, hrun⟩
  have hres := (frag_runs hfrag attempt
    (Array.replicate (2 * (p.ncap + 1)) unset32) [] r).mp hruns
  rw [List.append_nil] at hres
  have hmc : mctx (compile p) s mo =
      (⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ : Spec.SCtx) := rfl
  rw [hmc] at hres
  have hgate : Resumes (compile p) s mo start attempt
      (((enum ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root attempt
        (Array.replicate (2 * (p.ncap + 1)) unset32)).map
        fun t => ((compileNode p.root 0 rootSt).code.size, t)))
      (gateOut attempt
        ((enum ⟨s, p.nltype, p.bsrtype, mo.notbol, mo.noteol⟩ p.root attempt
          (Array.replicate (2 * (p.ncap + 1)) unset32)).filter
          (gateKeep p s mo start attempt))) := by
    cases hend : p.opts.endanchored with
    | false => exact resumes_gate_open hend (hopen hend) _
    | true =>
        obtain ⟨h1, h2⟩ := hanch hend
        exact resumes_gate_anchored hend h1 h2 _
  have hr := resumes_det hres hgate
  intro F
  refine ⟨?_, hr⟩
  rw [Spec.attemptThreads]
  rw [search_covered hc F attempt (Array.replicate (2 * (p.ncap + 1))
    unset32)]
  rfl

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

/-! ## The target: S-8's backtracking half

Stated now so the assembly has an agreed shape; the proof is the coming
rounds' composition of everything above. Three reading notes on the side
conditions. `Wf p` is the parser facts. `s.size ≤ ceiling` resolves the
one guard asymmetry honestly: `Spec.matchesF` answers BadInput for a
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
under the guard hypotheses. The proof of this proposition is the S-8
backtracking assembly. -/
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

end Pcrevera.Refine
