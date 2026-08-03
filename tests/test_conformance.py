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

from pcrevera.backends import lowering
from pcrevera.engine import Engine
from pcrevera.engine import certificate_corpus
from pcrevera.oracle import conformance
from pcrevera.oracle import corpus as wave1


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


@pytest.mark.parametrize(
    "held",
    [None, [], {}, {"a": 1}, "cases", 0, 1],
    ids=["absent", "empty", "empty-object", "object", "string", "zero", "number"],
)
def test_a_section_is_a_list_with_something_in_it(tmp_path, held) -> None:
    """A corpus is one thing in three languages, so a bad one is refused in three.

    JavaScript wants an array and Go decodes into a slice or fails, and both
    then ask whether it is empty. Python asking only whether the value is
    truthy would take an object or a string, which is a corpus none of the
    other two would read.
    """
    path = tmp_path / "corpus.json"
    document = {"schema": conformance.SCHEMA, "cases": [{}]}
    if held is not None:
        document["analyses"] = held
    path.write_text(conformance.text(document))
    with pytest.raises(ValueError, match="holds no analyses"):
        conformance.section(conformance.read(path), "analyses", path)


def test_the_three_sections_of_a_corpus_are_read_the_same_way() -> None:
    """The certificate corpus is the one that carries more than one array."""
    built = conformance.read(certificate_corpus.PATH)
    for name in ("cases", "analyses", "accessors"):
        assert conformance.section(built, name, certificate_corpus.PATH)
