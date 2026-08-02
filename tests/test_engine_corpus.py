"""The wave 1 differential corpus, run against both engines.

Every case is inside the subset DESIGN.md section 2.1 claims for wave 1, so the
hand-written expectation, the pinned pcre2, and our own engine are supposed to
be three statements of the same thing. A case only pcre2 agrees with is a bug
of ours; a case only we agree with means the expectation was written from what
we do rather than from what PCRE means, which is the failure mode the seed
corpus's doctrine exists to prevent.
"""

from __future__ import annotations

import pytest

from pcretruste.engine import Engine
from pcretruste.oracle import corpus as corpus_module


@pytest.fixture(scope="module")
def wave1() -> corpus_module.Corpus:
    return corpus_module.load(corpus_module.WAVE1_PATH)


def _report(failures) -> str:
    return "\n".join(f"{case.name}: {why}" for case, why in failures)


def test_the_corpus_is_not_empty(wave1: corpus_module.Corpus) -> None:
    assert len(wave1.cases) > 200


def test_our_engine_agrees_with_the_expectations(wave1: corpus_module.Corpus) -> None:
    failures = corpus_module.check(Engine(), wave1)
    assert not failures, _report(failures)


def test_pcre2_agrees_with_the_expectations(oracle, wave1: corpus_module.Corpus) -> None:
    failures = corpus_module.check(oracle, wave1)
    assert not failures, _report(failures)


def _comparable(outcome) -> object:
    """An outcome stripped to the fields DESIGN.md section 2.4 makes a contract.

    The message text of a compile error is ours, deliberately, so it is not part
    of what the two engines have to agree on; the code and the byte offset are.
    """
    from pcretruste.oracle.client import Compiled, CompileError

    if isinstance(outcome, CompileError):
        return ("cerror", outcome.code, outcome.offset)
    if isinstance(outcome, Compiled):
        return ("compiled", outcome.capture_count, tuple(sorted(outcome.names)))
    return outcome


def test_the_two_engines_agree_case_by_case(oracle, wave1: corpus_module.Corpus) -> None:
    """Same question, same answer, quite apart from what the corpus expected."""
    engine = Engine()
    disagreements = []
    for case in wave1.cases:
        ours = _comparable(corpus_module.run(engine, case))
        theirs = _comparable(corpus_module.run(oracle, case))
        if ours != theirs:
            disagreements.append(f"{case.name}: ours {ours!r}, pcre2 {theirs!r}")
    assert not disagreements, "\n".join(disagreements)
