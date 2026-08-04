"""The slice of the sweep that ordinary CI runs.

DESIGN.md section 8 wants the campaign's infrastructure exercised on every
commit without waiting for the campaign, so this is one deterministic slice of
the same population — every seventh case of a small one — recorded as
`conformance/sweep.json` and replayed by all three engines.

It is generated from the engine alone, with no pcre2 in sight, and that is
deliberate. Regenerating a committed file must not need a build of the pinned
library, or `make generate-verify` would stop being something a contributor can
run. What the file records is therefore what our engine answers, and pcre2's
opinion of it is a test — `tests/test_sweep.py` replays the same shard through
the oracle — so the chain is the same one the wave 1 corpus has: pcre2 agrees
with Python, and Go and JavaScript agree with the file.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from ..engine.driver import Engine
from ..oracle import conformance
from ..paths import CONFORMANCE_DIR
from . import campaign, manifest, promote
from .checks import run_case
from .population import CROSS

PATH = CONFORMANCE_DIR / "sweep.json"

SEED = 20260803
STRUCTURED = len(CROSS)
"""The atom-by-quantifier product and nothing past it: the shard is here for
the opcodes and the option families, and the grammar is the campaign's."""

HOSTILE = 64
SUBJECTS = 8
STRIDE = 7
"""Co-prime with the twelve quantifiers, so the slice walks every atom rather
than taking the same quantifier from each."""

NOTE = (
    campaign.NOTE
    + " This is the committed shard: one case in every seven of a small "
    "population, generated from the engine alone so that regenerating it needs "
    "no build of pcre2. What pcre2 says about the same cases is a test, not a "
    "file. The regressions section holds the same answers for the cases the "
    "sweep has actually found and a reducer has shrunk, which are kept in "
    "oracle/corpus/sweep-regressions.json rather than generated; every runner "
    "replays them exactly as it replays the generated ones, since what they "
    "guard is an invariant rather than an answer."
)


def document() -> dict[str, Any]:
    """The shard's manifest, which the recorded answers name by hash."""
    return manifest.build(
        SEED,
        structured=STRUCTURED,
        hostile=HOSTILE,
        subjects=SUBJECTS,
        stride=STRIDE,
    )


def _clean(findings, what: str) -> None:
    if findings:
        raise AssertionError(
            f"the committed shard cannot be generated from a failing {what}:\n"
            + "\n".join(str(one) for one in findings[:20])
        )


def kept(
    engine: Engine | None = None, path: Path = promote.REGRESSIONS_PATH
) -> list[dict[str, Any]]:
    """The regression cases, run the same way the generated ones are.

    These came out of a real sweep and a reducer rather than out of the
    generator, which is exactly why they are replayed through the same battery:
    what each one guards is a bound, an edge, a context or the two matchers
    agreeing, and none of that is a question a corpus of expected answers asks.

    A repository that has not found one yet keeps none, and the section is
    written empty rather than left out: every runner has to be able to tell a
    section it should have replayed from one nobody wrote.

    Each is rerun under the budget and the edge count its own entry carries,
    which are the ones its failure was found under; a regression found only
    under a custom limit stops guarding anything the moment it is replayed
    under another. That budget goes into the record too, since the runners
    would otherwise apply the containing document's and get numbers they
    cannot reproduce.
    """
    held = engine or Engine()
    out = []
    for case, entry in promote.regression_cases(path):
        asked = entry["budget"]
        outcome = run_case(held, case, budget=asked, edges=entry["edges"])
        _clean(outcome.findings, f"regression ({entry['name']})")
        assert outcome.record is not None
        out.append(
            {
                "name": entry["name"],
                "note": entry["note"],
                "budget": asked,
                **outcome.record,
            }
        )
    return out


def corpus(engine: Engine | None = None) -> dict[str, Any]:
    """The shard, run: every case with every answer attached."""
    held = engine or Engine()
    report = campaign.run(manifest.read(document()), engine=held)
    _clean(report.findings, "run")
    built = report.document(
        structured=STRUCTURED,
        hostile=HOSTILE,
        subjects=SUBJECTS,
        stride=STRIDE,
        regressions=kept(held),
    )
    built["note"] = NOTE
    return built


def corpus_text() -> str:
    return conformance.text(corpus())


def load(path: Path = PATH) -> dict[str, Any]:
    """The committed shard, with its envelope checked."""
    return conformance.read(path)
