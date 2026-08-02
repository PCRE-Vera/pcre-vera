"""The bound certificate: what the checker accepts, and what it refuses.

The analyzer does not exist yet, which is the point — DESIGN.md section 5 keeps
it untrusted by having a small checker stand between it and anything that
believes a bound. So the cases hand the checker certificates directly, well
formed and otherwise, and they are the specification the analyzer will have to
be written against.

They live in `engine/certificate_corpus.py` rather than here, because the same
list becomes `conformance/certificates.json` and is answered by the generated Go
and JavaScript too — and this file reads the committed JSON rather than the
objects it was written from, so an encoding that lost something fails here
instead of quietly agreeing with itself.

What only Python asks is the rest: the arithmetic at subject lengths worth
naming one at a time, and the boundary where a value that is not a TIR value at
all gets refused before the checker ever sees it.
"""

from __future__ import annotations

import pytest

from pcretruste.engine import certificate_corpus
from pcretruste.engine.certificate_corpus import CASES, CODE, KINDS, priced, root
from pcretruste.engine import Certificate, Engine, EngineError, Term, spec
from pcretruste.engine.program import program
from pcretruste.tir.types import CAP, CEILING

COMMITTED = certificate_corpus.load()
"""The corpus as the file spells it, which is what the other two runners read."""

IDS = [case.name for case in COMMITTED]


@pytest.fixture(scope="module")
def engine() -> Engine:
    return Engine()


def cert(name: str) -> Certificate:
    """The certificate one of the committed cases is about."""
    return next(case.cert for case in COMMITTED if case.name == name)


# --- the verdicts, and the bounds the file records ---


def test_the_corpus_says_the_same_thing_as_the_cases_it_came_from() -> None:
    """Not "carries the same names" but "decodes to the same cases".

    Every field the runners read, the enum ordinals back as the variants they
    stand for, and the note a failure in any of the three quotes back.
    """
    assert COMMITTED == CASES


@pytest.mark.parametrize("case", COMMITTED, ids=IDS)
def test_the_checker_draws_the_verdict_the_case_names(engine, case) -> None:
    assert engine.check_certificate(case.cert, case.codelen) == case.check, case.note


@pytest.mark.parametrize("case", COMMITTED, ids=IDS)
def test_the_bounds_are_the_ones_the_corpus_records(engine, case) -> None:
    for row in case.bounds:
        for key, which in KINDS:
            assert engine.bound(case.cert, which, row["n"]) == row[key], f"{key} at n={row['n']}"


def test_every_verdict_the_checker_can_give_has_a_case() -> None:
    # A refusal nothing trips is a refusal nobody has read, and the checker is
    # the piece the proofs will lean on hardest.
    assert {case.check for case in COMMITTED} == set(program().enum_map["Cr"].variants)


def test_no_two_cases_share_a_name() -> None:
    # The three runners report a failure by name, so a duplicate would send a
    # reader to the wrong case.
    assert len(IDS) == len(set(IDS))


# --- evaluating a bound ---


def test_a_polynomial_bound_evaluates_at_the_subject_length(engine) -> None:
    at = cert("polynomial")
    assert engine.bound(at, "BkCost", 0) == 3
    assert engine.bound(at, "BkCost", 1) == 6
    assert engine.bound(at, "BkCost", 10) == 123


def test_a_bound_with_no_terms_is_zero(engine) -> None:
    assert engine.bound(cert("root-only"), "BkCost", 1000) == 0


def test_an_exponential_bound_is_finite_until_it_is_not(engine) -> None:
    at = cert("exponential")
    assert engine.bound(at, "BkCost", 10) == 1024
    assert engine.bound(at, "BkCost", 52) == 2**52
    # 2^53 is one past what a counter holds, and "at least 2^53" is not a
    # budget anybody can plan with.
    assert engine.bound(at, "BkCost", 53) is None


def test_a_bound_of_exactly_the_saturation_point_is_still_a_number(engine) -> None:
    assert engine.bound(cert("at-the-saturation-point"), "BkCost", 4) == CAP


def test_arithmetic_that_would_saturate_is_reported_rather_than_clamped(engine) -> None:
    assert engine.bound(cert("one-past-the-saturation-point"), "BkCost", 4) is None
    assert engine.bound(cert("product-that-would-saturate"), "BkCost", 2) is None
    assert engine.bound(cert("product-that-just-fits"), "BkCost", 2) == 2 * (CAP // 2)


@pytest.mark.parametrize(
    "kind, ceiling, at, past",
    [
        ("BkStack", spec.MAX_STACK, "at-the-stack-ceiling", "past-the-stack-ceiling"),
        ("BkMem", CEILING, "at-the-memory-ceiling", "past-the-memory-ceiling"),
    ],
)
def test_a_bound_no_limit_could_accept_is_exceeds_budget(
    engine, kind, ceiling, at, past
) -> None:
    # Section 2.4 asks for more than "it fits in a counter": any number these
    # accessors give back has to be one the caller can turn round and pass as a
    # limit, so the two projections with a ceiling of their own refuse at it.
    assert engine.bound(cert(at), kind, 4) == ceiling
    assert engine.bound(cert(past), kind, 4) is None


def test_cost_has_no_ceiling_below_the_saturation_point(engine) -> None:
    # Which is the whole difference between the three: a number that is far
    # too much memory to ever be reserved is still a fine amount of work.
    at = cert("past-the-memory-ceiling")
    assert engine.bound(at, "BkCost", 4) == CEILING + 1
    assert engine.bound(at, "BkMem", 4) is None


def test_the_whole_pattern_bound_is_the_roots(engine) -> None:
    # A child's terms price the child. Nothing sums them behind the accessor's
    # back, because the composition rule that would justify doing so is the
    # analyzer's to state and the checker's to verify, and neither exists yet.
    assert engine.bound(cert("children-are-not-summed-behind-the-accessor"), "BkCost", 4) == 7


def test_a_certificate_the_checker_refused_answers_rather_than_traps(engine) -> None:
    # The accessors are only ever reached after the checker has accepted, so
    # this is about what the engine does with a certificate nobody vouched for:
    # an answer, never a read past the end of the term table.
    assert engine.bound(cert("sum-runs-past-the-table"), "BkCost", 4) is None
    assert engine.bound(cert("term-worth-nothing"), "BkCost", 53) == 0
    assert engine.bound(Certificate(regions=()), "BkCost", 4) is None


# --- the boundary between Python and a TIR value ---


@pytest.mark.parametrize(
    "bad, length",
    [
        (priced(Term(-1)), CODE),
        (priced(Term(CAP + 1)), CODE),
        (priced(Term(1, base=2**32)), CODE),
        (Certificate(regions=(root(hi=2**32),)), CODE),
        (Certificate(regions=(root(),)), -1),
        (Certificate(regions=(root(kind="RkWhatever"),)), CODE),
        (Certificate(regions=(root(),), complexity="CcWhatever"), CODE),
        (priced(*((Term(1),) * (spec.MAX_TERMS + 1))), CODE),
    ],
)
def test_a_value_no_tir_could_hold_never_reaches_the_checker(engine, bad, length) -> None:
    # The checker distrusts what it is handed, which is the point of it, but a
    # test that handed it something no TIR value can even be would be testing
    # the interpreter rather than the rule it meant to.
    with pytest.raises(EngineError):
        engine.check_certificate(bad, length)


def test_a_bound_is_asked_for_by_a_name_the_engine_knows(engine) -> None:
    with pytest.raises(EngineError):
        engine.bound(Certificate(regions=(root(),)), "BkWhatever", 4)


def test_a_region_names_a_construct_the_compiler_emits(engine) -> None:
    # Every wave 1 region kind, so that adding a lookaround kind in wave 2 is a
    # deliberate act rather than a string that happened to typecheck.
    kinds = {region.kind for case in COMMITTED for region in case.cert.regions}
    assert kinds == set(program().enum_map["Rk"].variants)
