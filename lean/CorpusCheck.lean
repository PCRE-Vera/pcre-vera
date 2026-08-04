import Pcrevera.Corpus.Run

/-!
# The corpus executable (R-10)

Reads the two conformance corpora and the AST bridge, replays every
compiled case through `R.compile` and both matchers, and exits nonzero on
the first sign of disagreement. `make lean` runs it, so executability and
engine agreement are exercised on every build rather than discovered at the
end of the milestone.
-/

open Pcrevera Pcrevera.Corpus Pcrevera.Ref

def loadJson (path : System.FilePath) : IO Lean.Json := do
  match Lean.Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

def orDie {α : Type} (what : String) : Except String α → IO α
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

def main (args : List String) : IO UInt32 := do
  let (corpusPath, sweepPath, bridgePath) ←
    match args with
    | [c, s, b] => pure (c, s, b)
    | _ => throw (IO.userError
        "usage: corpuscheck corpus.json sweep.json bridge.json")
  let corpus ← loadJson corpusPath
  let sweep ← loadJson sweepPath
  let bridge ← loadJson bridgePath

  let mut failures : List String := []
  let mut replayed := 0
  let mut skipped := 0

  let corpusBridge ← orDie "bridge corpus" (field bridge "corpus")
  let cases ← orDie "corpus cases" (arrField corpus "cases")
  for c in cases do
    let name ← orDie "case name" (strField c "name")
    let entry ← orDie s!"bridge {name}" (field corpusBridge name)
    let decoded ← orDie s!"bridge {name}" (bridgeCaseOf entry)
    if decoded.skip.isSome then skipped := skipped + 1
    else replayed := replayed + 1
    -- Called for a skip too: the runner cross-checks it against the record,
    -- so a bridge that skipped everything fails rather than replaying nothing
    -- and reporting success.
    match runCorpusCase decoded c with
    | .error e => failures := failures ++ [s!"corpus {name}: {e}"]
    | .ok bad => failures := failures ++ bad.map (s!"corpus {name}: {·}")

  let budgetJ ← orDie "sweep budget" (field sweep "budget")
  let budget : Limits :=
    { cost := ← orDie "budget" (natField budgetJ "cost")
      stack := ← orDie "budget" (natField budgetJ "stack")
      mem := ← orDie "budget" (natField budgetJ "memory") }

  let sweepBridge ← orDie "bridge sweep" (field bridge "sweep")
  let sweepCases ← orDie "sweep cases" (arrField sweep "cases")
  for c in sweepCases do
    let family ← orDie "family" (strField c "family")
    let index ← orDie "index" (natField c "index")
    let key := s!"{family}-{index}"
    let entry ← orDie s!"bridge {key}" (field sweepBridge key)
    let decoded ← orDie s!"bridge {key}" (bridgeCaseOf entry)
    if decoded.skip.isSome then skipped := skipped + 1
    else replayed := replayed + 1
    match runSweepCase decoded c budget with
    | .error e => failures := failures ++ [s!"sweep {key}: {e}"]
    | .ok bad => failures := failures ++ bad.map (s!"sweep {key}: {·}")

  let regBridge ← orDie "bridge regressions" (field bridge "regressions")
  let regressions ← orDie "sweep regressions" (arrField sweep "regressions")
  for c in regressions do
    let name ← orDie "regression name" (strField c "name")
    let entry ← orDie s!"bridge {name}" (field regBridge name)
    let decoded ← orDie s!"bridge {name}" (bridgeCaseOf entry)
    let budgetJ ← orDie s!"{name} budget" (field c "budget")
    let own : Limits :=
      { cost := ← orDie "budget" (natField budgetJ "cost")
        stack := ← orDie "budget" (natField budgetJ "stack")
        mem := ← orDie "budget" (natField budgetJ "memory") }
    if decoded.skip.isSome then skipped := skipped + 1
    else replayed := replayed + 1
    match runSweepCase decoded c own with
    | .error e => failures := failures ++ [s!"regression {name}: {e}"]
    | .ok bad => failures := failures ++ bad.map (s!"regression {name}: {·}")

  for f in failures do
    IO.eprintln f
  if failures.isEmpty then
    IO.println s!"corpuscheck: {replayed} cases replayed, {skipped} skipped \
      (compile refusals stay with the parser), 0 disagreements, every \
      replayed tree well formed for the refinement theorems"
    return 0
  else
    IO.eprintln s!"corpuscheck: {failures.length} disagreements"
    return 1
