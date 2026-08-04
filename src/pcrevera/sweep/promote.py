"""Moving a minimized case into the committed corpus.

The last step of DESIGN.md section 8's failure loop: a disagreement is found,
reduced, fixed, and then the small case that caught it becomes a case somebody
reads. A generated population is rebuilt from a seed, so a bug that only that
seed reaches would be a bug nothing guards once the seed moves on.

Which corpus it goes to depends on what disagreed, and getting that wrong is
how a regression test comes to guard nothing. A compile or match disagreement
is about what the engine answers, and `oracle/corpus/wave1.json` is where
answers are pinned — with pcre2's own answer, taken from the pinned build at
promotion time, because a regression case's job is to hold the engine to the
arbiter rather than to somebody's reading of the manual. Everything else — a
bound violation, a limit edge, a context, the two matchers disagreeing, an
internal contradiction — is about an invariant no semantic corpus checks, so it
goes to `oracle/corpus/sweep-regressions.json`, whose cases are replayed
through the whole sweep battery in all three languages, exactly as a generated
case is.

Either way the case is only promoted once nothing about it fails any more —
the whole sweep battery, under the budget the failure was found with, since a
bound violation or a context reservation survives any compile-and-match
comparison. For a case whose right answer is a documented decline that means
pcre2 is never consulted at all, which is the oracle policy of DESIGN.md
section 1 rather than an exception to it. Promoting a case that still fails
would be committing a red test, and the failure record is where a known-broken
case belongs until it is fixed.

The budget and the edge count are stored with the case, not just used to check
it. A regression found only under a custom limit is a regression only under
that limit, and a corpus that recorded the case but not the conditions would be
one whose entries stop guarding what they were kept for the moment somebody
runs a sweep with a different budget.

The wave 1 file is hand-formatted — one case per line, blank lines grouping the
families — so a promoted case is spliced in as text rather than written by a
serializer that would reflow the whole thing into something unreviewable. The
regression file is generated-shaped and is rewritten wholesale.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from ..engine.driver import Compiled, CompileError, Engine, Match, NoMatch
from ..oracle import conformance
from ..oracle.corpus import WAVE1_PATH, load
from ..paths import CORPUS_DIR
from .checks import DEFAULT_EDGES, agrees, run_case
from .manifest import DEFAULT_BUDGET, decode, encode
from .population import Case

REGRESSIONS_PATH = CORPUS_DIR / "sweep-regressions.json"

REGRESSIONS_NOTE = (
    "Cases the differential sweep found and a reducer shrank, kept because a "
    "generated population is rebuilt from a seed and would not find them "
    "again once the seed moved on. What each one guards is an invariant no "
    "semantic corpus checks — a certified bound, a limit edge, a preallocated "
    "context, the two matchers agreeing, the analyzer and the checker agreeing "
    "— so they are replayed through the whole sweep battery rather than "
    "compared to an expected answer. Their answers live in the regressions "
    "section of conformance/sweep.json, which every implementation replays."
)

SEMANTIC = frozenset({"compile", "match"})
"""The classes `oracle/corpus/wave1.json` can hold, because they are about the
answer. Every other class is about an invariant that corpus never asks."""


def expectation(answer: object) -> Any:
    """What pcre2 said, in the spelling the wave 1 corpus writes it in."""
    if isinstance(answer, Match):
        return {"match": list(answer.ovector)}
    if isinstance(answer, NoMatch):
        return "nomatch"
    if isinstance(answer, CompileError):
        return {"cerror": {"code": answer.code, "offset": answer.offset}}
    if isinstance(answer, Compiled):
        held: dict[str, Any] = {"captures": answer.capture_count}
        if answer.names:
            # Group names are part of what a compile answers, and a case that
            # dropped them would pass on an engine that lost one.
            held["names"] = {
                name.decode("latin-1"): number for name, number in answer.names
            }
        return {"compiled": held}
    raise ValueError(f"a corpus case has no form for {answer!r}")


def _asked(oracle: object, case: Case, at: int | None):
    """One question about the case, asked of pcre2 and of our engine.

    A case with no trials asks about compilation alone, which is what a
    minimized compile disagreement reduces to; a case with trials asks about
    the trial the reducer kept. Only the wave 1 half asks this at all: what it
    is for is the expectation that file records, and a case whose right answer
    is a decline has none to record.
    """
    engine = Engine()
    shared = {
        "options": case.options,
        "newline": case.newline,
        "bsr": case.bsr,
    }
    if at is None:
        return (
            oracle.compile(case.pattern, **shared),
            engine.compile(case.pattern, **shared),
        )
    trial = case.trials[at]
    asked = {
        **shared,
        "start": trial.start,
        "match_options": trial.match_options,
    }
    return (
        oracle.match(case.pattern, trial.subject, **asked),
        engine.match(case.pattern, trial.subject, **asked),
    )


def fixed(
    oracle: object, case: Case, name: str, budget: dict[str, int], edges: int
) -> None:
    """The case passes every check the sweep would put it through, now.

    The whole battery rather than the one comparison the corpus will record,
    because most of what a sweep finds is not an answer: a bound violation, a
    limit edge, a context reservation or the two matchers disagreeing would all
    survive a compile-and-match comparison, and promoting one of those while it
    still reproduces would be filing a red test as a green one. It also lets a
    case whose right answer is a decline be promoted, since the oracle policy
    of DESIGN.md section 1 lives inside this battery and not in `agrees`.
    """
    outcome = run_case(Engine(), case, budget=budget, oracle=oracle, edges=edges)
    if outcome.findings:
        raise ValueError(
            f"{name} still fails — {outcome.findings[0]} — so it is a failure "
            "record rather than a corpus case"
        )


def confirmed(
    oracle: object, case: Case, name: str, budget: dict[str, int], edges: int
) -> object:
    """pcre2's answer about this case, once nothing about it fails any more."""
    fixed(oracle, case, name, budget, edges)
    theirs, ours = _asked(oracle, case, 0 if case.trials else None)
    if not agrees(ours, theirs):
        raise ValueError(
            f"{name} still disagrees with pcre2 — ours {ours!r}, pcre2 {theirs!r} — "
            "so it is a failure record rather than a corpus case"
        )
    return theirs


def entry(
    oracle: object,
    case: Case,
    name: str,
    note: str,
    budget: dict[str, int] | None = None,
    edges: int = DEFAULT_EDGES,
) -> dict[str, Any]:
    """One wave 1 case, with pcre2's answer, checked against our own first.

    The conditions default here and nowhere below: this is the entry point a
    test reaches for, and everything inside takes them as arguments so that a
    caller cannot check a case under conditions that are not the ones the
    failure was found under.
    """
    theirs = confirmed(oracle, case, name, budget or DEFAULT_BUDGET, edges)
    built: dict[str, Any] = {"name": name, "pattern_hex": case.pattern.hex()}
    if case.trials:
        trial = case.trials[0]
        built["subject_hex"] = trial.subject.hex()
        if trial.match_options:
            built["match_options"] = list(trial.match_options)
        if trial.start:
            built["start"] = trial.start
    if case.options:
        built["options"] = list(case.options)
    if case.newline != "LF":
        built["newline"] = case.newline
    if case.bsr != "UNICODE":
        built["bsr"] = case.bsr
    built["expect"] = expectation(theirs)
    built["note"] = note
    return built


def line(built: dict[str, Any]) -> str:
    """A case as the committed file spells one: compact, on its own line."""
    return "    " + json.dumps(built, separators=(", ", ": "))


def splice(text: str, lines: list[str]) -> str:
    """The corpus with those cases added, and nothing else touched.

    The last case of the array loses nothing but its lack of a comma, which is
    the whole edit: everything above it stays byte for byte where it was, so a
    promotion reads as an addition in a diff.
    """
    marker = "\n  ]\n}"
    body = text.rstrip("\n")
    if not body.endswith(marker):
        raise ValueError("the corpus does not end the way this expects")
    head = body[: -len(marker)]
    return head + ",\n" + ",\n".join(lines) + marker + "\n"


def regressions(path: Path = REGRESSIONS_PATH) -> list[dict[str, Any]]:
    """The kept sweep cases, or nothing at all if none has been kept yet."""
    if not path.exists():
        return []
    return conformance.section(conformance.read(path), "cases", path)


def regression_cases(path: Path = REGRESSIONS_PATH) -> list[tuple[Case, dict[str, Any]]]:
    """Each kept case, decoded, beside the entry that says what it guards.

    The entry carries the budget and the edge count the failure was found
    under, which is what it has to be rerun under: the conditions are part of
    the regression, not of whoever is replaying it.
    """
    return [(decode(one["case"]), one) for one in regressions(path)]


def _fresh(names: list[str], taken: set[str], where: str) -> None:
    for name in names:
        if name in taken:
            raise ValueError(f"the {where} corpus already has a case called {name!r}")
        taken.add(name)


def promote(
    oracle: object,
    cases: list[tuple[Case, str, str, str]],
    path: Path = WAVE1_PATH,
    kept: Path = REGRESSIONS_PATH,
    budget: dict[str, int] | None = None,
    edges: int = DEFAULT_EDGES,
) -> dict[str, list[str]]:
    """Add each (case, class, name, note) to whichever corpus it belongs in.

    Nothing is written until everything has been checked: the names against
    each corpus and against each other, and every answer against pcre2. A case
    can fail in more than one way and a failure document can therefore hold two
    records for it, so a name derived from the case alone can repeat — and the
    wave 1 loader refuses a duplicate name, which would leave the file broken
    after a promotion that reported success. Half a promotion is worse still,
    which is why the two files are written at the end rather than as they go.
    """
    semantic = [(case, name, note) for case, kind, name, note in cases if kind in SEMANTIC]
    invariant = [
        (case, name, note) for case, kind, name, note in cases if kind not in SEMANTIC
    ]
    _fresh([name for _, name, _ in semantic], {one.name for one in load(path).cases}, "wave 1")
    held = regressions(kept)
    _fresh([name for _, name, _ in invariant], {one["name"] for one in held}, "regression")

    asked = budget or DEFAULT_BUDGET
    lines = [
        line(entry(oracle, case, name, note, asked, edges))
        for case, name, note in semantic
    ]
    for case, name, note in invariant:
        fixed(oracle, case, name, asked, edges)
        held.append(
            {
                "name": name,
                "note": note,
                "budget": dict(asked),
                "edges": edges,
                "case": encode(case),
            }
        )

    if lines:
        path.write_text(splice(path.read_text(), lines))
    if invariant:
        kept.parent.mkdir(parents=True, exist_ok=True)
        kept.write_text(conformance.text(conformance.document(REGRESSIONS_NOTE, held)))
    return {
        "wave1": [name for _, name, _ in semantic],
        "regressions": [name for _, name, _ in invariant],
    }
