"""The language-neutral conformance corpus, run through the Python interpreter.

The same two files run against the generated Go (`gen/go/conformance_test.go`)
and the generated JavaScript (`gen/js/test/conformance.test.mjs`). Three
implementations agreeing with one committed file is what DESIGN.md section 8
means by agreeing bit for bit, and it is a stronger statement than three
implementations agreeing pairwise, because the file is also what pcre2 agrees
with.

What agreement means is `oracle/corpus.py`'s answer, not a second opinion: the
committed file decodes back into the same `Case` values the wave 1 corpus
loads, so `check` is the same function the wave 1 tests call.
"""

from __future__ import annotations

import pytest

from pcretruste.backends import lowering
from pcretruste.engine import Engine
from pcretruste.oracle import conformance
from pcretruste.oracle import corpus as wave1


@pytest.fixture(scope="module")
def committed() -> wave1.Corpus:
    return conformance.load()


@pytest.fixture(scope="module")
def probe() -> dict:
    return conformance.read(lowering.PATH)


def test_the_corpus_covers_every_outcome(committed: wave1.Corpus) -> None:
    """A corpus that stopped exercising an outcome would still pass every case."""
    kinds = {type(case.expect).__name__ for case in committed.cases}
    assert kinds == {
        "MatchExpectation",
        "NoMatchExpectation",
        "CompileErrorExpectation",
        "CompiledExpectation",
    }
    assert len(committed.cases) > 200


def test_the_interpreter_agrees_with_the_corpus(committed: wave1.Corpus) -> None:
    failures = wave1.check(Engine(), committed)
    assert not failures, "\n".join(f"{case.name}: {why}" for case, why in failures)


def test_the_corpus_says_the_same_thing_as_the_wave_1_one(committed: wave1.Corpus) -> None:
    """The neutral file is derived, so it has to still be a faithful restatement.

    Not "carries the same patterns" but "decodes to the same cases": every
    field the runners read, in the same order, including the note a failure
    quotes back.
    """
    assert committed.cases == wave1.load(wave1.WAVE1_PATH).cases


def test_the_probe_asks_about_every_branch(probe: dict) -> None:
    """The values are the drift check's business; this is about the coverage.

    `tests/test_backends.py` regenerates the file and compares it byte for
    byte, which is the Python interpreter answering all 4031 cases, so
    replaying them here would only ask the same question twice.
    """
    numbers = lowering.kinds()
    assert {case["name"] for case in probe["cases"]} == set(numbers)
    for case in probe["cases"]:
        assert case["kind"] == numbers[case["name"]]
    assert probe["shift"] == lowering.SHIFT
