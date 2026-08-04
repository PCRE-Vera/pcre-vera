import Pcrevera.Ref.Context
import Pcrevera.Spec.Match

/-!
# The execution semantics (S-5, S-6, S-7's subject, and R-4's equation)

`Config` is the internal configuration domain of DESIGN.md section 6,
deliberately wider than the public API: Pike, backtracking and memoized,
each plain or behind a preallocated context named by its creation
parameters. `Exec` is the one operational function over it.

One definitional choice is worth stating plainly, because THEOREMS.md
frames R-4 around it. The specification of *what a pattern means* is
`Spec.Matches` and nothing else; the specification of *execution* — cost
accounting, limit behavior, context discipline — is this file, and it is
definitionally the reference engine: `Exec cfg p` validates the call the
way the engine's entry points do and then runs `Ref.run cfg` on
`Ref.compile p`. R-4's equation therefore holds by definition (and is
recorded as `run_compile_eq_exec`), and the semantic weight rests entirely
on S-8: whenever this function answers Found or NotFound, the answer is
`Matches`. That composition — not R-4 alone — is what says the reference
engine returns exactly what the trusted spec means.

Validation mirrors the wrappers and the engine together: limits must be
representable in the section 2.4 sense, a subject must fit the documented
cap, memoization is BadInput until M9 activates it, an ineligible
configuration is BadInput, and a context call may lower its creation
limits, never raise them, with its memory component pinned to the
reservation.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- Which matcher a configuration runs. -/
inductive Matcher where
  | pike | backtrack | memo
deriving DecidableEq, Repr

/-- The internal configuration domain (S-5): a matcher, plain or behind a
context created with a declared maximum and creation limits. -/
inductive Config where
  | plain (m : Matcher)
  | inCtx (m : Matcher) (maxlen : Nat) (creation : Limits)
deriving DecidableEq, Repr

/-- The section 2.4 validity rules for a limit triple: cost within the
counter, memory within the byte ceiling, stack within the derived entry
cap. Anything else is BadInput, never a clamp. -/
def Limits.valid (lim : Limits) : Bool :=
  lim.cost ≤ counterMax && lim.stack ≤ maxStack && lim.mem ≤ ceiling

/-- Which matcher compilation selected: the routing of `match`. -/
def Re.selected (re : Re) : Matcher :=
  if re.pike then .pike else .backtrack

/-- R.run: the engine's entry points over a compiled pattern, dispatched by
configuration. The plain paths are `match`'s routing plus the internal
`bt_match` testing entry; a context path re-derives the context from its
creation parameters (creation is deterministic) and calls through it. -/
def run (cfg : Config) (cp : CompiledPat) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) : RunResult :=
  if !lim.valid || s.size > ceiling then ⟨.badInput, #[], {}⟩ else
  match cfg with
  | .plain .memo => ⟨.badInput, #[], {}⟩
  | .plain .pike => pikeRun cp.re s start mo lim {}
  | .plain .backtrack => btRun cp.re s start mo lim 0 0
  | .inCtx m maxlen creation =>
      if m != cp.re.selected then ⟨.badInput, #[], {}⟩
      else if !creation.valid then ⟨.badInput, #[], {}⟩
      else
        match ctxCreate cp 0 maxlen creation with
        | (.ok, some ctx) =>
            if lim.mem != ctx.memcap then ⟨.badInput, #[], {}⟩
            else ctxMatch ctx s start mo lim.cost lim.stack
        | _ => ⟨.badInput, #[], {}⟩

/-- S-6's CreateCtx: the creation step, its reservation and zeroing charged
against the creation limits, answering a valid configuration or the
deterministic refusal. -/
def createCtx (cp : CompiledPat) (m : Matcher) (maxlen : Nat)
    (creation : Limits) : CreateSt × Option Config :=
  if m == .memo then (.badInput, none)
  else if m != cp.re.selected then (.badInput, none)
  else if !creation.valid then (.badInput, none)
  else
    match ctxCreate cp 0 maxlen creation with
    | (.ok, some _) => (.ok, some (.inCtx m maxlen creation))
    | (status, _) => (status, none)

/-- Exec (S-5): execution over the internal configuration domain, defined
as the reference pipeline on the compiled pattern. -/
def Exec (cfg : Config) (p : Pat) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) : RunResult :=
  run cfg (compileFull p).2 s start mo lim

/-- R-4, `run_compile_eq_exec`: soundness and completeness of the compiled
pipeline against the execution semantics, in one equation. It holds by
definition — see the module docstring — and is stated so the composition
with S-8 can be drawn where THEOREMS.md draws it. -/
theorem run_compile_eq_exec (cfg : Config) (p : Pat) (s : ByteArray)
    (start : Nat) (mo : MOpts) (lim : Limits) :
    run cfg ⟨compile p, (certInstall (compile p)).2.1,
      (certInstall (compile p)).2.2⟩ s start mo lim =
      Exec cfg p s start mo lim := rfl

end Pcrevera.Ref
