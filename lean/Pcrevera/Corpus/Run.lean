import Pcrevera.Corpus.Decode
import Pcrevera.Ref.Exec
import Pcrevera.Proofs.WfDecide

/-!
# Replaying the corpora through the reference engine (R-10)

The Lean twin of `gen/go/internal/engine/sweep_test.go` and the conformance
runner: compile every bridged AST, hold the program to the engine's own
tables, run every recorded trial, and compare outcome, ovector and usage to
the unit. Limits derive from the recorded bound exactly the way the other
runners derive them — the certificate's number, never more than the sweep's
budget — so a reference engine whose accounting drifted runs at different
limits and fails on the usage rather than passing quietly.

Bytecode equality has one deliberate loosening: the engine numbers character
classes at parse time and `R.compile` numbers them in emission order, and a
construct dropped between the two (a `{0}` quantifier) can shift every
index after it. A class instruction is therefore compared by the 32 bytes
its argument resolves to, which is the meaning of the instruction, while
every other field is compared exactly.
-/

namespace Pcrevera.Corpus

open Pcrevera Pcrevera.Ref

/-- The selected-path match, the routing `match` fixes at compilation. -/
def selectedRun (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) : RunResult :=
  if re.pike then pikeRun re s start mo lim {}
  else btRun re s start mo lim 0 0

/-- The backtracking path, the internal testing entry point. -/
def backtrackRun (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) : RunResult :=
  btRun re s start mo lim 0 0

/-- An ovector as the record spells it: -1 for unset. -/
def offsets (ov : Array UInt32) : List Int :=
  ov.toList.map fun v => if v == unset32 then -1 else Int.ofNat v.toNat

/-- The well-formedness the refinement theorems quantify over, asked of the
tree the engine's own parser produced. `Wf` names the shapes a parse never
emits, and until M10 proves the parser that is a claim to be tested rather
than assumed — so every replayed case checks it, and a pattern that failed
would be a finding about the hypothesis rather than about the run. -/
def wfAgrees (p : Pat) : Option String :=
  if Refine.wfB p then none
  else some "the parsed tree is not well formed for the refinement theorems"

/-- One instruction against the engine's, classes compared by meaning. -/
def instAgrees (mine : Inst) (mineClasses : Array UInt8)
    (theirs : Inst) (theirClasses : Array UInt8) : Bool :=
  mine.op == theirs.op && mine.alt == theirs.alt &&
    (if mine.op == .cls then
      (List.range 32).all fun k =>
        mineClasses[mine.arg * 32 + k]! == theirClasses[theirs.arg * 32 + k]!
    else mine.arg == theirs.arg)

/-- `R.compile`'s output against the engine's compile, field for field. -/
def compileAgrees (mine : Re) (theirs : BridgeRe) : Option String :=
  if mine.code.size != theirs.code.size then
    some s!"code size {mine.code.size} vs {theirs.code.size}"
  else if !(List.range mine.code.size).all (fun i =>
      instAgrees mine.code[i]! mine.classes theirs.code[i]! theirs.classes) then
    some "an instruction disagrees"
  else if mine.reps.toList != theirs.reps.toList then
    some "the repetition tables disagree"
  else if mine.regions.toList != theirs.regions.toList then
    some "the region tables disagree"
  else if mine.ncap != theirs.ncap then
    some s!"ncap {mine.ncap} vs {theirs.ncap}"
  else if mine.nregs != theirs.nregs then
    some s!"nregs {mine.nregs} vs {theirs.nregs}"
  else if mine.crfirst != theirs.crfirst then
    some s!"crfirst {mine.crfirst} vs {theirs.crfirst}"
  else if mine.hascrlf != theirs.hascrlf then
    some s!"hascrlf {mine.hascrlf} vs {theirs.hascrlf}"
  else if mine.pike != theirs.pike then
    some s!"pike {mine.pike} vs {theirs.pike}"
  else none

/-- A bridge polynomial: base and low-to-high coefficients. -/
def polyOfJson (j : Lean.Json) : D Poly := do
  let coefs ← (← arrField j "coefs").mapM asNat
  .ok ⟨← natField j "base", coefs[0]!, coefs[1]!, coefs[2]!, coefs[3]!,
    coefs[4]!⟩

def cfgOfJson (name : String) : D Cfg :=
  match name with
  | "CfgBacktrack" => .ok .backtrack
  | "CfgPike" => .ok .pike
  | "CfgMemo" => .ok .memo
  | _ => .error s!"{name} names no configuration"

def ccOfJson (name : String) : D Cc :=
  match name with
  | "CcNotProvenLinear" => .ok .notProvenLinear
  | "CcLinear" => .ok .linear
  | _ => .error s!"{name} names no complexity"

/-- A bridge certificate, in the engine's own field order. -/
def certOfJson (j : Lean.Json) : D Cert := do
  let prices ← (← arrField j "prices").mapM fun p => do
    .ok (⟨← polyOfJson (← field p "work"), ← polyOfJson (← field p "outs"),
      ← polyOfJson (← field p "stack"), ← polyOfJson (← field p "trail")⟩ :
      Price)
  .ok { config := ← cfgOfJson (← strField j "config")
        complexity := ← ccOfJson (← strField j "complexity")
        cost := ← polyOfJson (← field j "cost")
        stack := ← polyOfJson (← field j "stack")
        trail := ← polyOfJson (← field j "trail")
        mem := ← polyOfJson (← field j "mem")
        prices }

/-- The analysis half of the bridge held to `certInstall`: the verdict is
the engine's CrOk, and each kept certificate matches slot for slot. -/
def certsAgree (verdict : Cr) (cp : CompiledPat) (theirs : BridgeRe) :
    D (Option String) := do
  if verdict != .crOk then
    return some "certInstall refused what the engine accepted"
  if cp.cert.isSome != theirs.hascert then
    return some s!"hascert {cp.cert.isSome} vs {theirs.hascert}"
  if cp.pikecert.isSome != theirs.haspikecert then
    return some s!"haspikecert {cp.pikecert.isSome} vs {theirs.haspikecert}"
  if theirs.hascert then
    let want ← certOfJson theirs.cert
    if cp.cert != some want then
      return some "the backtracking certificates disagree"
  if theirs.haspikecert then
    let want ← certOfJson theirs.pikecert
    if cp.pikecert != some want then
      return some "the Pike certificates disagree"
  return none

/-- A recorded bound: a number per dimension, or the ExceedsBudget null. -/
structure RecBound where
  cost : Option Nat := none
  stack : Option Nat := none
  mem : Option Nat := none

def recBoundOf (j : Lean.Json) : D RecBound := do
  let read := fun name => (fieldOpt j name).mapM asNat
  .ok { cost := ← read "cost", stack := ← read "stack", mem := ← read "mem" }

/-- The other runners' `sweepLimitsFor`: the certificate's own number, never
more than the budget. -/
def limitsFor (bound : RecBound) (budget : Limits) : Limits :=
  { cost := min budget.cost (bound.cost.getD budget.cost)
    stack := min budget.stack (bound.stack.getD budget.stack)
    mem := min budget.mem (bound.mem.getD budget.mem) }

def usageOf (j : Lean.Json) : D Usage := do
  .ok { cost := ← natField j "cost", stack := ← natField j "stack"
        mem := ← natField j "mem" }

def sameUsage (got : Usage) (want : Usage) : Bool :=
  got.cost == want.cost && got.stack == want.stack && got.mem == want.mem

/-- One dimension moved to the observed value less `down`. -/
def atEdge (limits : Limits) (used : Usage) (dim : Nat) (down : Nat) :
    Nat × Limits :=
  match dim with
  | 0 => (used.cost, { limits with cost := used.cost - down })
  | 1 => (used.stack, { limits with stack := used.stack - down })
  | _ => (used.mem, { limits with mem := used.mem - down })

/-- The limit edges of DESIGN.md section 8: at the observed value the run
answers what it just answered, one below it is refused. -/
def runEdges (run : Limits → RunResult) (used : Usage) (limits : Limits)
    (got : RunResult) : Option String := Id.run do
  for dim in [0, 1, 2] do
    let (observed, edge) := atEdge limits used dim 0
    let again := run edge
    if again.outcome != got.outcome || offsets again.ovec != offsets got.ovec
        || !sameUsage again.usage used then
      return some s!"at the observed limit (dim {dim}, {observed}) the run changed"
    if observed != 0 then
      let (_, below) := atEdge limits used dim 1
      if (run below).outcome != .resourceExceeded then
        return some s!"one below the observed limit (dim {dim}, {observed}) was not refused"
  return none

/-- One accessor against the recorded bound: a null is the ExceedsBudget
refusal, a number is (ok, that number). -/
def accessorAgrees (what : String) (got : Answer) (want : Option Nat) :
    Option String :=
  match want with
  | none =>
      if got.status != .exceedsBudget then
        some s!"the {what} accessor answered {got.status.toNat}, want ExceedsBudget"
      else none
  | some v =>
      if got.status != .ok || got.value != v then
        some s!"the {what} accessor answered ({got.status.toNat},{got.value}), want {v}"
      else none

/-- The backtracking bound read off the pattern's own certificate, the way
the cross-matcher check derives its limits. -/
def btBoundOf (cp : CompiledPat) (n : Nat) : RecBound :=
  match cp.cert with
  | none => {}
  | some cert =>
      let read := fun kind =>
        let held := certBound cert kind n
        if held.ok then some held.value else none
      { cost := read .cost, stack := read .stack, mem := read .mem }

def sameRecBound (got want : RecBound) : Bool :=
  got.cost == want.cost && got.stack == want.stack && got.mem == want.mem

/-- One sweep trial: the accessors at this subject length, the
recorded-limit call, the usage, the edges, and the cross-matcher half with
its bound recomputed from the certificate. -/
def runTrial (cp : CompiledPat) (budget : Limits) (trial : Lean.Json) :
    D (Option String) := do
  let re := cp.re
  let subject ← hexBytes (← strField trial "subject")
  let start ← natField trial "start"
  let mo := moptsOf (← natField trial "matchFlags")
  let bound ← recBoundOf (← field trial "bound")
  let limits := limitsFor bound budget
  if let some why := accessorAgrees "cost" (reCost cp 0 subject.size) bound.cost then
    return some why
  if let some why := accessorAgrees "stack" (reStack cp 0 subject.size) bound.stack then
    return some why
  if let some why := accessorAgrees "mem" (reMem cp 0 subject.size) bound.mem then
    return some why
  let outcome ← natField trial "outcome"
  let got := selectedRun re subject start mo limits
  if got.outcome.toNat != outcome then
    return some s!"outcome {got.outcome.toNat}, want {outcome}"
  if outcome == 0 then
    let want ← (← arrField trial "ovector").toList.mapM fun v =>
      match v.getInt? with
      | .ok i => pure i
      | .error e => .error e
    if offsets got.ovec != want then
      return some s!"ovector {offsets got.ovec}, want {want}"
  let usage ← usageOf (← field trial "usage")
  if !sameUsage got.usage usage then
    return some s!"usage ({got.usage.cost},{got.usage.stack},{got.usage.mem}), want ({usage.cost},{usage.stack},{usage.mem})"
  let edged := ((fieldOpt trial "edges").map
    (·.getBool?.toOption.getD false)).getD false
  if edged then
    if let some why := runEdges (selectedRun re subject start mo) usage limits got then
      return some why
  match fieldOpt trial "cross" with
  | none => return none
  | some cross =>
      let cbound ← recBoundOf (← field cross "bound")
      let derived := btBoundOf cp subject.size
      if !sameRecBound derived cbound then
        return some "the backtracking bound disagrees with the record"
      let climits := limitsFor cbound budget
      let cgot := backtrackRun re subject start mo climits
      let coutcome ← natField cross "outcome"
      if cgot.outcome.toNat != coutcome then
        return some s!"cross outcome {cgot.outcome.toNat}, want {coutcome}"
      if coutcome == 0 then
        let want ← (← arrField cross "ovector").toList.mapM fun v =>
          match v.getInt? with
          | .ok i => pure i
          | .error e => .error e
        if offsets cgot.ovec != want then
          return some s!"cross ovector {offsets cgot.ovec}, want {want}"
      let cusage ← usageOf (← field cross "usage")
      if !sameUsage cgot.usage cusage then
        return some s!"cross usage ({cgot.usage.cost},{cgot.usage.stack},{cgot.usage.mem}), want ({cusage.cost},{cusage.stack},{cusage.mem})"
      if ((fieldOpt cross "edges").map (·.getBool?.toOption.getD false)).getD false then
        if let some why := runEdges (backtrackRun re subject start mo) cusage climits cgot then
          return some s!"cross: {why}"
      return none

/-- The context half of a sweep case: creation status and reservation, the
creation edge, every recorded call, and the per-call cost and stack edges
on the call the record names. Creation runs with the budget's memory as its
cost ceiling, the way every other runner does, so the binding refusal is
always about the reservation. -/
def runContext (cp : CompiledPat) (caseJ : Lean.Json) (budget : Limits) :
    D (List String) := do
  let ctxJ ← field caseJ "context"
  let maxlen ← natField caseJ "maxlen"
  let wantStatus ← natField ctxJ "status"
  let creation : Limits := ⟨budget.mem, budget.stack, budget.mem⟩
  let (status, held) := ctxCreate cp 0 maxlen creation
  if status.toNat != wantStatus then
    return [s!"creation answered {status.toNat}, want {wantStatus}"]
  match held with
  | none => return []
  | some ctx =>
  let memcap ← natField ctxJ "memcap"
  let mut failures : List String := []
  if ctx.memcap != memcap then
    return [s!"the context reserves {ctx.memcap}, want {memcap}"]
  if ctx.resident != ctx.memcap then
    failures := failures ++
      [s!"the context holds {ctx.resident} bytes, having reserved {ctx.memcap}"]
  let (atRes, _) := ctxCreate cp 0 maxlen { creation with mem := memcap }
  if atRes != .ok then
    failures := failures ++ ["creation at exactly the reservation was refused"]
  if memcap > 0 then
    let (below, _) := ctxCreate cp 0 maxlen { creation with mem := memcap - 1 }
    if below != .resourceExceeded then
      failures := failures ++ ["creation one byte under the reservation was not refused"]
  let calls ← arrField ctxJ "calls"
  let trials ← arrField caseJ "trials"
  for i in [0 : calls.size] do
    let call := calls[i]!
    let trial := trials[i]!
    let subject ← hexBytes (← strField trial "subject")
    let start ← natField trial "start"
    let mo := moptsOf (← natField trial "matchFlags")
    let got := ctxMatch ctx subject start mo budget.mem budget.stack
    let wantOutcome ← natField call "outcome"
    if got.outcome.toNat != wantOutcome then
      failures := failures ++
        [s!"context call {i} answered {got.outcome.toNat}, want {wantOutcome}"]
    else
      let usage ← usageOf (← field call "usage")
      if !sameUsage got.usage usage then
        failures := failures ++
          [s!"context call {i} used ({got.usage.cost},{got.usage.stack},{got.usage.mem}), want ({usage.cost},{usage.stack},{usage.mem})"]
      let plainOutcome ← natField trial "outcome"
      if plainOutcome == 0 && got.outcome == .matched then
        let want ← (← arrField trial "ovector").toList.mapM fun v =>
          match v.getInt? with
          | .ok x => pure x
          | .error e => .error e
        if offsets got.ovec != want then
          failures := failures ++
            [s!"context call {i} answered {offsets got.ovec}, the plain call {want}"]
  match fieldOpt ctxJ "edges" with
  | none => return failures
  | some at_ =>
      let i ← asNat at_
      let trial := trials[i]!
      let subject ← hexBytes (← strField trial "subject")
      let start ← natField trial "start"
      let mo := moptsOf (← natField trial "matchFlags")
      let first := ctxMatch ctx subject start mo budget.mem budget.stack
      let run := fun (cost stack : Nat) => ctxMatch ctx subject start mo cost stack
      for dim in [0, 1] do
        let observed := if dim == 0 then first.usage.cost else first.usage.stack
        let at_ := fun v =>
          if dim == 0 then run v budget.stack else run budget.mem v
        let again := at_ observed
        if again.outcome != first.outcome ||
            offsets again.ovec != offsets first.ovec ||
            !sameUsage again.usage first.usage then
          failures := failures ++
            [s!"a context call at its observed limit (dim {dim}) changed"]
        if observed != 0 then
          if (at_ (observed - 1)).outcome != .resourceExceeded then
            failures := failures ++
              [s!"a context call one below its observed limit (dim {dim}) was not refused"]
      return failures

/-- One sweep case: compile against the bridge, hold the analysis to the
record, replay every trial, pin the Pike VM's refusal on an ineligible
program, and replay the context half. -/
def runSweepCase (bridge : BridgeCase) (caseJ : Lean.Json) (budget : Limits) :
    D (List String) := do
  let kind ← strField (← field caseJ "compile") "kind"
  match bridge.skip with
  | some code =>
      -- A skip is the bridge saying the engine refused this pattern, and the
      -- record says so too or one of them is wrong. Without this a bridge
      -- that skipped everything would replay nothing and report success.
      if kind == "compiled" then
        return ["the bridge skipped a case the record says compiled"]
      let want ← natField (← field caseJ "compile") "code"
      if code != want then
        return [s!"the bridge skipped with {code}, the record refuses with {want}"]
      return []
  | none =>
  if kind != "compiled" then
    return [s!"the bridge carries a tree for a case the record records as {kind}"]
  let some ast := bridge.ast | .error "a bridged case carries no AST"
  let some expected := bridge.expected | .error "a bridged case carries no re"
  let flags ← natFieldD caseJ "flags" 0
  let p : Pat :=
    { root := ast
      opts := patOptsOf flags
      nltype := ← nlOf (← natFieldD caseJ "newline" 0)
      bsrtype := ← bsrOf (← natFieldD caseJ "bsr" 0)
      hascrlf := expected.hascrlf }
  let (verdict, cp) := compileFull p
  let re := cp.re
  let mut failures : List String := []
  if let some why := wfAgrees p then
    failures := failures ++ [why]
  if let some why := compileAgrees re expected then
    return [s!"compile: {why}"]
  if let some why := ← certsAgree verdict cp expected then
    return [s!"certificates: {why}"]
  if re.pike != (← boolField caseJ "pike") then
    failures := failures ++ [s!"pike {re.pike}"]
  let recorded ← boolField (← field caseJ "cert") "backtrack"
  let recordedPike ← boolField (← field caseJ "cert") "pike"
  if cp.cert.isSome != recorded || cp.pikecert.isSome != recordedPike then
    failures := failures ++ ["the certificate flags disagree with the record"]
  let classGot := reClass cp
  match fieldOpt caseJ "class" with
  | none =>
      if classGot.status != .exceedsBudget then
        failures := failures ++ ["the class accessor did not answer ExceedsBudget"]
  | some v =>
      let want ← asNat v
      if classGot.status != .ok || classGot.value != want then
        failures := failures ++
          [s!"the class accessor answered ({classGot.status.toNat},{classGot.value}), want {want}"]
  if !re.pike then
    let probe := pikeRun re ByteArray.empty 0 {} budget {}
    if probe.outcome != .badInput then
      failures := failures ++ ["an ineligible program was not refused by the Pike VM"]
  let trials ← arrField caseJ "trials"
  for i in [0 : trials.size] do
    match ← runTrial cp budget trials[i]! with
    | some why => failures := failures ++ [s!"trial {i}: {why}"]
    | none => pure ()
  failures := failures ++ (← runContext cp caseJ budget)
  return failures

/-- One conformance case: outcome and ovector at the default limits. -/
def runCorpusCase (bridge : BridgeCase) (caseJ : Lean.Json) : D (List String) := do
  let expect ← field caseJ "expect"
  let kind ← strField expect "kind"
  match bridge.skip with
  | some code =>
      -- The same cross-check as the sweep's: the bridge and the record have
      -- to agree that the engine refused this pattern, and on the code.
      if kind != "compileError" then
        return [s!"the bridge skipped a case the record records as {kind}"]
      let want ← natField expect "code"
      if code != want then
        return [s!"the bridge skipped with {code}, the record refuses with {want}"]
      return []
  | none =>
  if kind == "compileError" then
    return ["the bridge carries a tree for a case the record refuses"]
  let some ast := bridge.ast | .error "a bridged case carries no AST"
  let some expected := bridge.expected | .error "a bridged case carries no re"
  let flags ← natFieldD caseJ "flags" 0
  let p : Pat :=
    { root := ast
      opts := patOptsOf flags
      nltype := ← nlOf (← natFieldD caseJ "newline" 0)
      bsrtype := ← bsrOf (← natFieldD caseJ "bsr" 0)
      hascrlf := expected.hascrlf }
  let (verdict, cp) := compileFull p
  let re := cp.re
  if let some why := wfAgrees p then
    return [why]
  if let some why := compileAgrees re expected then
    return [s!"compile: {why}"]
  if let some why := ← certsAgree verdict cp expected then
    return [s!"certificates: {why}"]
  let expect ← field caseJ "expect"
  let kind ← strField expect "kind"
  let defaults : Limits := ⟨10000000, 100000, 64 * 1024 * 1024⟩
  match kind with
  | "compiled" =>
      let captures ← natField expect "captures"
      if re.ncap != captures then
        return [s!"captures {re.ncap}, want {captures}"]
      return []
  | "match" | "nomatch" =>
      let subject ← hexBytes (← strField caseJ "subject")
      let start ← natFieldD caseJ "start" 0
      let mo := moptsOf (← natFieldD caseJ "matchFlags" 0)
      let got := selectedRun re subject start mo defaults
      if kind == "nomatch" then
        if got.outcome != .noMatch then
          return [s!"outcome {got.outcome.toNat}, want nomatch"]
        return []
      if got.outcome != .matched then
        return [s!"outcome {got.outcome.toNat}, want a match"]
      let want ← (← arrField expect "ovector").toList.mapM fun v =>
        match v.getInt? with
        | .ok i => pure i
        | .error e => .error e
      if offsets got.ovec != want then
        return [s!"ovector {offsets got.ovec}, want {want}"]
      return []
  | other => .error s!"{other} is not an expectation this runner knows"

end Pcrevera.Corpus
