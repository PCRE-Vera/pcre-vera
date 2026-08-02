"""The bound certificate: what the checker accepts, and what it refuses.

The analyzer does not exist yet, which is the point — DESIGN.md section 5 keeps
it untrusted by having a small checker stand between it and anything that
believes a bound. So the cases hand the checker certificates directly, exact
and otherwise, and they are the specification the analyzer will have to be
written against.

They live in `engine/certificate_corpus.py` rather than here, because the same
list becomes `conformance/certificates.json` and is answered by the generated Go
and JavaScript too — and this file reads the committed JSON rather than the
objects it was written from, so an encoding that lost something fails here
instead of quietly agreeing with itself.

What only Python asks is the rest: that an accepted certificate really does
bound a run of the matcher, that the arithmetic says the right thing at subject
lengths worth naming one at a time, and that a value which is not a TIR value
at all gets refused before the checker ever sees it.
"""

from __future__ import annotations

import itertools

import pytest

from pcretruste.engine import Certificate, Engine, EngineError, Poly, Price, Region, spec
from pcretruste.engine import certificate_corpus
from pcretruste.engine.certificate_corpus import (
    CASES,
    KINDS,
    LITERAL,
    STAR,
    UNCAPTURED,
    compiled,
    minimal,
    read,
    region,
    root,
    unpriced,
)
from pcretruste.engine.driver import CompiledPattern, Limits, ResourceExceeded
from pcretruste.oracle import corpus as wave1
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
    verdict = engine.check_certificate(case.subject(), case.cert, case.config)
    assert verdict == case.check, case.note


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


def test_a_region_names_a_construct_the_compiler_emits() -> None:
    # Every wave 1 region kind, so that adding a lookaround kind in wave 2 is a
    # deliberate act rather than a string that happened to typecheck.
    kinds = {
        one.kind
        for pattern in SHAPES + PRICED
        for one in read(compiled(pattern)).regions
    }
    assert kinds == set(program().enum_map["Rk"].variants)


# --- and does an accepted certificate bound the run? ---

PRICED = (
    b"abc",
    b"(a)",
    b"a|b",
    b"a?",
    b"a??",
    b"a*",
    b"a{2,5}",
    b"(ab)*c",
    b"(a|b)*c",
    b"(?:a|a){0,3}",
    b"(?:a|a)*",
)
"""The patterns the corpus prices, which is what there is to hold to a run."""

SUBJECTS = (b"", b"a", b"c", b"ab", b"aa", b"abc", b"aab", b"aaaa", b"abab", b"aabbc")

OPTIONS = ("NOTBOL", "NOTEOL", "NOTEMPTY", "NOTEMPTY_ATSTART", "ANCHORED")

ROOMY = Limits(cost=50_000_000, stack=100_000, memory=64 * 1024 * 1024)


@pytest.mark.parametrize("pattern", PRICED, ids=[p.decode() for p in PRICED])
def test_an_accepted_certificate_bounds_every_run_of_the_matcher(engine, pattern) -> None:
    """The claim `CrOk` actually makes, exercised rather than argued.

    Every subject below, from every start offset, under every option and every
    pair of options, with what the matcher reports having used held against
    what the certificate said it could. This is the small version of the fuzz
    assertion M5 finishes with; what it buys today is that the composition
    rules of BOUNDS.md were transcribed the way they were meant.
    """
    case = next(one for one in COMMITTED if one.pattern == pattern and one.check == "CrOk")
    built = compiled(pattern)
    assert engine.check_certificate(built, case.cert) == "CrOk"
    combinations = [()] + [(one,) for one in OPTIONS] + list(itertools.combinations(OPTIONS, 2))
    for subject in SUBJECTS:
        bounds = {key: engine.bound(case.cert, which, len(subject)) for key, which in KINDS}
        for start in range(len(subject) + 1):
            for options in combinations:
                out = engine.match_compiled(
                    built, subject, start=start, match_options=list(options), limits=ROOMY
                )
                assert not isinstance(out, ResourceExceeded), (subject, start, options)
                used = engine.last_usage
                where = f"{pattern!r} on {subject!r} from {start} with {options}"
                for key, seen in (
                    ("cost", used.cost),
                    ("stack", used.stack),
                    ("mem", used.memory),
                ):
                    limit = bounds[key]
                    assert limit is None or seen <= limit, f"{key}: {seen} over {limit}, {where}"


def test_the_certificate_of_one_program_is_not_the_certificate_of_another(engine) -> None:
    # The whole of what the length could not say. These two programs are four
    # instructions over the same three regions, and the difference between them
    # is that two of the instructions are saves.
    assert engine.check_certificate(compiled(b"(?:abc)"), UNCAPTURED) == "CrOk"
    assert engine.check_certificate(compiled(b"(a)"), UNCAPTURED) == "CrRegionTrail"


# --- evaluating a bound ---


def test_a_bound_evaluates_at_the_subject_length(engine) -> None:
    # 24 + 12 * (n + 1): the register file and the ovector zeroed once and the
    # ovector copied back out once, then four instructions and the register
    # clearing at each starting position.
    at = cert("literal")
    assert engine.bound(at, "BkCost", 0) == 36
    assert engine.bound(at, "BkCost", 1) == 48
    assert engine.bound(at, "BkCost", 10) == 156


def test_a_bound_with_no_coefficients_is_zero(engine) -> None:
    assert engine.bound(cert("literal"), "BkStack", 1000) == 0


def test_an_exponential_bound_is_finite_until_it_is_not(engine) -> None:
    # The stack bound of `(?:a|a)*` is 8 * 2^n: two ways round the loop, one
    # entry pushed per pass through the head, and the coefficient the flow
    # picks up on the way.
    at = cert("exponential")
    assert engine.bound(at, "BkStack", 10) == 8192
    assert engine.bound(at, "BkStack", 24) == 8 * 2**24
    # And it meets the stack ceiling long before it meets the saturation point,
    # because an entry count no limit could name is no use to a caller either.
    assert engine.bound(at, "BkStack", 25) is None


def test_a_bound_of_exactly_the_saturation_point_is_still_a_number(engine) -> None:
    assert engine.bound(cert("over-claimed-to-every-ceiling"), "BkCost", 0) == CAP


def test_arithmetic_that_would_saturate_is_reported_rather_than_clamped(engine) -> None:
    assert engine.bound(cert("over-claimed-to-every-ceiling"), "BkCost", 1) is None
    assert engine.bound(cert("over-claimed-past-every-ceiling"), "BkCost", 0) is None


@pytest.mark.parametrize(
    "kind, ceiling", [("BkStack", spec.MAX_STACK), ("BkMem", CEILING)]
)
def test_a_bound_no_limit_could_accept_is_exceeds_budget(engine, kind, ceiling) -> None:
    # Section 2.4 asks for more than "it fits in a counter": any number these
    # accessors give back has to be one the caller can turn round and pass as a
    # limit, so the two projections with a ceiling of their own refuse at it.
    assert engine.bound(cert("over-claimed-to-every-ceiling"), kind, 4) == ceiling
    assert engine.bound(cert("over-claimed-past-every-ceiling"), kind, 4) is None


def test_cost_has_no_ceiling_below_the_saturation_point(engine) -> None:
    # Which is the whole difference between the three: a number that is far
    # too much memory to ever be reserved is still a fine amount of work.
    at = cert("past-the-memory-ceiling-and-still-a-cost")
    assert engine.bound(at, "BkCost", 4) == CEILING + 1 + 12 * 5
    assert engine.bound(at, "BkMem", 4) is None


def test_a_certificate_the_checker_refused_answers_rather_than_traps(engine) -> None:
    # The accessors are only ever reached after the checker has accepted, so
    # this is about what the engine does with a certificate nobody vouched for:
    # an answer, never a read past the end of anything.
    assert engine.bound(Certificate(prices=()), "BkCost", 4) == 0
    assert engine.bound(cert("a-bound-with-no-base"), "BkCost", 4) == 0
    assert engine.bound(cert("a-bound-with-no-base"), "BkCost", 0) == 1


# --- the tree the compiler emits ---

SHAPES = (
    # Empty alternation arms, which compile to a branch region of no width.
    b"(a|)", b"(|a)", b"(a||b)", b"(?:|)", b"|", b"a|",
    # Patched jump boundaries: every branch but the last leaves by one.
    b"a|b|c|d", b"(a|b|c)x", b"(?:a|bb|ccc)+", b"x(a|b)(c|d)y",
    # Repetitions beside each other and inside each other.
    b"a*b*", b"a+b?c{2,3}", b"(a*)(b*)", b"(?:a*)+", b"(a+)+", b"((a|b)*c)*",
    # Groups, nested and named.
    b"(a)(b)", b"((a))", b"(?:(?:(a)))", b"(?<n>a)(?P<m>b)",
    # Optionals, both greedinesses, and the quantifiers that compile to
    # nothing at all or to the body alone.
    b"a?", b"a??", b"(ab)?", b"(a|b)?", b"a{0,1}?", b"(?:x)?y",
    b"a{0}", b"(?:)", b"()", b"a{1}", b"(?:x){1}", b"a{3}", b"a{2,}",
    b"^(?:ab|cd)*$", rb"\b(?:\w+|\d)*\b", b"[a-z]+(?:[0-9]|_)*",
)

STRUCTURE = frozenset(
    {
        "CrNoRegions", "CrRootKind", "CrRootParent", "CrRootRange", "CrTwoRoots",
        "CrParentOrder", "CrBackwards", "CrNotNested", "CrOverlap",
        "CrOpcode", "CrShape", "CrChildren",
    }
)
"""The verdicts that are about the tree rather than about the numbers in it."""


def _emitted(patterns):
    for pattern in patterns:
        built = certificate_corpus.ENGINE.compile_pattern(pattern)
        if isinstance(built, CompiledPattern):
            yield pattern, built


def _describes(engine, built) -> str:
    """The verdict for a certificate that claims nothing, which is about the tree."""
    return engine.check_certificate(built, unpriced(len(read(built).regions)))


@pytest.mark.parametrize("pattern", SHAPES, ids=[p.decode() for p in SHAPES])
def test_the_tree_the_compiler_emits_describes_the_bytecode(engine, pattern) -> None:
    """Canonical emission, one shape at a time.

    The certificate claims nothing, so every rule about the numbers refuses;
    what this asks is the other half, that no rule about the tree does. A
    region that started in the wrong place, an alternation whose branches do
    not line up with its splits, an instruction nothing covers — all of those
    are structural, and none of them may happen for a program this compiler
    wrote.
    """
    built = compiled(pattern)
    assert _describes(engine, built) not in STRUCTURE, [
        (one.kind, one.parent, one.lo, one.hi) for one in read(built).regions
    ]


def test_every_pattern_of_the_wave_one_corpus_emits_a_tree_that_checks(engine) -> None:
    # The shapes above are the ones chosen to be awkward; this is everything
    # else the engine is held to, which is where a shape nobody thought of
    # would be.
    for pattern, built in _emitted(one.pattern for one in wave1.load().cases):
        assert _describes(engine, built) not in STRUCTURE, pattern


def test_almost_every_shape_prices_as_well(engine) -> None:
    """And the numbers, for the shapes the composition rules have an answer for.

    The four that have none are the nested unbounded loops, where the pass
    count would be a power of a polynomial. That is a refusal BOUNDS.md names
    rather than a gap, so it is written down here as the list it is.
    """
    refused = []
    for pattern, built in _emitted(SHAPES):
        try:
            priced = certificate_corpus.price(read(built))
        except ValueError:
            refused.append(pattern)
            continue
        assert engine.check_certificate(built, priced) == "CrOk", pattern
    assert refused == [rb"(?:a*)+", rb"(a+)+", rb"((a|b)*c)*", rb"\b(?:\w+|\d)*\b"]


def test_a_generous_certificate_is_accepted_and_a_short_one_is_not(engine) -> None:
    # The rule is domination, not equality, so an analyzer that rounds up is
    # believed and one that rounds down is not.
    built = compiled(b"a*")
    doubled = certificate_corpus.claiming(
        STAR, cost=Poly(tuple(2 * one for one in STAR.cost.coefs))
    )
    assert engine.check_certificate(built, doubled) == "CrOk"
    assert engine.check_certificate(built, certificate_corpus.less(STAR, "cost", 2)) == (
        "CrTotalCost"
    )


def test_domination_is_coefficient_by_coefficient(engine) -> None:
    # A huge constant does not pay for a term in n, and refusing to work that
    # out is what keeps the rule something Layer A can prove in one line.
    lumped = certificate_corpus.claiming(LITERAL, cost=certificate_corpus.const(CAP))
    assert engine.check_certificate(compiled(b"abc"), lumped) == "CrTotalCost"


def test_a_pattern_the_rules_cannot_price_gets_no_certificate(engine) -> None:
    # Not a wrong number and not a silent zero: `price` is the corpus's own
    # statement of the same rules, and it refuses in the same place the checker
    # does (`CrAmbiguous` for this pattern).
    with pytest.raises(ValueError):
        minimal(b"(?:a*)*")


# --- the boundary between Python and a TIR value ---


@pytest.mark.parametrize(
    "bad",
    [
        Certificate(prices=(), cost=Poly((-1,))),
        Certificate(prices=(), cost=Poly((CAP + 1,))),
        Certificate(prices=(), cost=Poly((1,), base=CAP + 1)),
        Certificate(prices=(), cost=Poly((1, 1, 1, 1, 1, 1))),
        Certificate(prices=(Price(),), complexity="CcWhatever"),
        Certificate(prices=(Price(),) * (spec.MAX_REGIONS + 1)),
    ],
)
def test_a_value_no_tir_could_hold_never_reaches_the_checker(engine, bad) -> None:
    # The checker distrusts what it is handed, which is the point of it, but a
    # test that handed it something no TIR value can even be would be testing
    # the interpreter rather than the rule it meant to.
    with pytest.raises(EngineError):
        engine.check_certificate(compiled(b"abc"), bad)


@pytest.mark.parametrize(
    "bad",
    [
        (region("RkRoot", spec.NONE, 0, 2**32),),
        (region("RkWhatever", spec.NONE, 0, 4),),
        (root(4),) * (spec.MAX_REGIONS + 1),
    ],
)
def test_a_region_table_no_tir_could_hold_is_refused_here_too(engine, bad) -> None:
    with pytest.raises(EngineError):
        compiled(b"abc").with_regions(bad)


def test_a_configuration_is_named_by_a_name_the_engine_knows(engine) -> None:
    with pytest.raises(EngineError):
        engine.check_certificate(compiled(b"abc"), unpriced(2), "CfgWhatever")


def test_a_bound_is_asked_for_by_a_name_the_engine_knows(engine) -> None:
    with pytest.raises(EngineError):
        engine.bound(Certificate(prices=()), "BkWhatever", 4)


def test_a_region_that_is_not_a_region_is_refused_here(engine) -> None:
    with pytest.raises(EngineError):
        compiled(b"abc").with_regions(
            (Region(kind="RkRoot", parent=spec.NONE, lo=0, hi=-1),)
        )


def test_the_reference_pricer_reads_the_shared_cost_model(monkeypatch) -> None:
    """The corpus predicts what the matcher charges, from the same constants.

    `spec.py` owns the register width and the growth schedule so that the
    matcher, the checker and this pricer cannot drift apart; a pricer that had
    copied the numbers instead would keep agreeing with itself while the other
    two moved. The checker is built from the same constants at generation time,
    which is why moving them here is only half a change and this only asks for
    the half it can see.
    """
    before = certificate_corpus.price(read(compiled(b"(a)*")))
    for name in ("REG_SIZE", "GROW_MIN", "GROW_FACTOR"):
        monkeypatch.setattr(spec, name, 2 * getattr(spec, name))
    assert certificate_corpus.price(read(compiled(b"(a)*"))).cost != before.cost


def test_the_reference_pricer_refuses_what_a_counter_could_not_hold(engine) -> None:
    # `price` promises a certificate the checker accepts, and a bound Python
    # can write down and the engine cannot hold is not one. The checker answers
    # `CrOverflow` for the same thing.
    with pytest.raises(ValueError):
        minimal(b"(?:(?:a){10}){10}")
