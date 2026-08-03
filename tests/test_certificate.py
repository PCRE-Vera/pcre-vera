"""The bound certificate: what the analyzer produces and the checker believes.

DESIGN.md section 5 keeps the analyzer untrusted by having a small checker
stand between it and anything that believes a bound, so there are two things to
hold to. The checker's cases hand it certificates directly, exact and
otherwise; the analyzer's are patterns, because compiling one runs it.

Both live in `engine/certificate_corpus.py` rather than here, because the same
lists become `conformance/certificates.json` and are answered by the generated
Go and JavaScript too — and this file reads the committed JSON rather than the
objects it was written from, so an encoding that lost something fails here
instead of quietly agreeing with itself.

What only Python asks is the rest: that what the analyzer produced is exactly
what an independent statement of the same rules produces, that an accepted
certificate really does bound a run of the matcher, that the arithmetic says
the right thing at subject lengths worth naming one at a time, and that a value
which is not a TIR value at all gets refused before the checker ever sees it.
"""

from __future__ import annotations

import itertools
from dataclasses import replace

import pytest

import test_engine_differential as differential
from pcrevera.engine import (
    Certificate,
    Engine,
    EngineError,
    Poly,
    Price,
    InternalError,
    Region,
    spec,
)
from pcrevera.engine import certificate_corpus
from pcrevera.engine.certificate_corpus import (
    CASES,
    KINDS,
    LENGTHS,
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
from pcrevera.engine import driver
from pcrevera.engine.driver import CompiledPattern, Limits, ResourceExceeded
from pcrevera.oracle import corpus as wave1
from pcrevera.engine.program import program
from pcrevera.tir.interp import Cell
from pcrevera.tir.types import CAP, CEILING, StructType

COMMITTED = certificate_corpus.load()
"""The corpus as the file spells it, which is what the other two runners read."""

ANALYSED = certificate_corpus.load_analyses()

IDS = [case.name for case in COMMITTED]

ANALYSIS_IDS = [one.name for one in ANALYSED]


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

    Recorded bounds are out of that comparison, since they are read off the
    engine rather than written by the case, so their row count is asked for
    here: the tests that check them are loops, and a loader that dropped every
    row would leave those loops empty and this equality green.
    """
    assert COMMITTED == CASES
    assert [len(case.bounds) for case in COMMITTED] == [len(LENGTHS)] * len(CASES)


@pytest.mark.parametrize("case", COMMITTED, ids=IDS)
def test_the_checker_draws_the_verdict_the_case_names(engine, case) -> None:
    verdict = engine.check_certificate(case.subject(), case.cert, case.config)
    assert verdict == case.check, case.note


@pytest.mark.parametrize("case", COMMITTED, ids=IDS)
def test_the_tree_half_of_the_checker_draws_the_verdict_recorded(engine, case) -> None:
    """`cert_shape` is the checker without the certificate, and this is its half.

    Not "CrOk or the verdict", which would be satisfied by a `cert_shape` that
    never said anything: the corpus records which of the two halves answered
    each case, and the relation that produced it — a verdict about the tree
    comes from this half, a verdict about the numbers leaves it silent — is
    checked when the file is written. All three runners ask, because an
    extraction that drifted in one backend is what three of them are for.
    """
    assert engine.check_shape(case.subject()) == case.shape, case.note


def _records(rows, evaluate, note: str) -> None:
    """Every recorded bound, at every length the corpus names one for."""
    for row in rows:
        for key, which in KINDS:
            where = f"{note}: {key} at n={row['n']}"
            assert evaluate(which, row["n"]) == row[key], where


@pytest.mark.parametrize("case", COMMITTED, ids=IDS)
def test_the_bounds_are_the_ones_the_corpus_records(engine, case) -> None:
    _records(case.bounds, lambda which, n: engine.bound(case.cert, which, n), case.name)


def test_the_analysis_corpus_says_the_same_thing_as_the_entries_it_came_from() -> None:
    # And the same row count, for the same reason, except that an entry the
    # analyzer found no bound for has nothing to evaluate and records nothing.
    assert ANALYSED == certificate_corpus.ANALYSES
    assert [len(one.bounds) for one in ANALYSED] == [
        0 if one.complexity is None else len(LENGTHS) for one in ANALYSED
    ]


@pytest.mark.parametrize("entry", ANALYSED, ids=ANALYSIS_IDS)
def test_compiling_produces_the_certificate_the_corpus_records(engine, entry) -> None:
    """The production path, from a pattern to the three numbers a caller reads.

    The verdict comes from running the analyzer again, so that a pattern with
    no bound is refused for the reason the corpus names rather than for
    whichever one came first. Everything else is read off the compiled pattern,
    which is the only place the rest of the engine will ever look.
    """
    built = compiled(entry.pattern)
    found, _ = engine.analyze(built)
    assert found == entry.found, entry.note
    cert = built.certificate
    assert (None if cert is None else cert.complexity) == entry.complexity, entry.note
    # Off the certificate the pattern carries, which is what the Go and
    # JavaScript runners evaluate; `bound` would take one that had been out of
    # the engine and back in, and a round trip is not what they are testing.
    _records(entry.bounds, lambda which, n: engine.bound_of(built, which, n), entry.name)


def test_compilation_prices_the_pike_path_exactly_as_the_restatement(engine) -> None:
    """Not merely accepted, equal: the certificate compilation stores for the
    Pike path is the one `lockstep` computes from BOUNDS.md section 9.

    Domination alone would let the engine's pricing drift conservatively away
    from the document; equality on patterns where every count bites — groups
    for the block width, Saves for the copy-on-write term — pins it.
    """
    for pattern in (b"abc", b"", b"(a)(b*)", b"(?:a|a)*", b"a*b*c*d*"):
        built = compiled(pattern)
        assert engine.pike_eligible(built), pattern
        assert built.pike_certificate == certificate_corpus.lockstep(pattern), pattern


# --- the public accessors, as the corpus pins them ---


ACCESSED = certificate_corpus.load_accessors()

ACCESS_IDS = [one["name"] for one in ACCESSED]


def test_the_accessor_corpus_says_the_same_thing_as_the_entries_it_came_from() -> None:
    assert ACCESSED == certificate_corpus.accesses()


@pytest.mark.parametrize("entry", ACCESSED, ids=ACCESS_IDS)
def test_the_public_accessors_answer_what_the_corpus_pins(engine, entry) -> None:
    """The whole accessor surface, one query at a time.

    This is the same file the Go and JavaScript runners read against their
    wrappers, so the three languages are held to identical statuses and
    identical numbers, refusals included.
    """
    built = compiled(bytes.fromhex(entry["pattern"]))
    want = (entry["class"]["status"], entry["class"]["value"])
    assert engine.complexity_class(built) == want, entry["note"]
    for row in entry["queries"]:
        for key, _ in KINDS:
            got = engine.worst_case(built, key, row["n"], row["config"])
            where = f"{entry['name']}: {key} at n={row['n']} config={row['config']}"
            assert got == (row[key]["status"], row[key]["value"]), where


@pytest.mark.parametrize("entry", ACCESSED, ids=ACCESS_IDS)
def test_a_pinned_bound_is_a_sufficient_limit(engine, entry) -> None:
    """Every exercise row, run: the three bounds unchanged as the limits.

    The sufficiency half of the contract through the public surface — a match
    at exactly the reported bounds may find or not find, but it may not run
    out — plus the usage reading back under every one of them.
    """
    built = compiled(bytes.fromhex(entry["pattern"]))
    for row in entry["queries"]:
        if not row["exercise"]:
            continue
        limits = Limits(
            cost=row["cost"]["value"],
            stack=row["stack"]["value"],
            memory=row["mem"]["value"],
        )
        outcome = engine.match_compiled(built, b"a" * row["n"], limits=limits)
        where = f"{entry['name']} at n={row['n']}"
        assert not isinstance(outcome, (ResourceExceeded, driver.BadInput)), where
        use = engine.last_usage
        assert use is not None
        assert use.cost <= row["cost"]["value"], where
        assert use.stack <= row["stack"]["value"], where
        assert use.memory <= row["mem"]["value"], where


def test_some_row_really_is_exercised() -> None:
    """The test above is a loop over a flag the generator computes, so an
    engine that stopped marking any row would leave it green and empty."""
    assert any(row["exercise"] for one in ACCESSED for row in one["queries"])


def test_a_length_nothing_represents_is_bad_input(engine) -> None:
    """What no counter holds is refused at the door, exactly like the limits.

    The corpus can only carry lengths every language can spell, so the ones
    Python alone can — a negative, a float, a bool, a value past the
    saturation point — are pinned here, per DESIGN.md section 2.4's
    exact-integer rule.
    """
    built = compiled(b"abc")
    for length in (-1, CAP + 1, True, False, 1.5, 10.0):
        assert engine.worst_case(built, "cost", length) == (spec.BAD_INPUT, 0), length
    for config in (-1, 2**32, True, 0.5):
        assert engine.worst_case(built, "cost", 10, config) == (spec.BAD_INPUT, 0), config


def test_the_match_configuration_is_part_of_the_match_surface(engine) -> None:
    """`match` takes the same configuration the accessors price.

    The default is the path compilation selected; the memoized value exists
    and is BadInput until M9; an ordinal nobody defined is BadInput forever;
    and what no u32 holds is refused before the engine sees it.
    """
    built = compiled(b"abc")
    good = engine.match_compiled(built, b"xabc", match_config=spec.MC_DEFAULT)
    assert not isinstance(good, driver.BadInput)
    for config in (spec.MC_MEMO, 2, 7, 0xFFFFFFFF, -1, 2**32, 0.5, True):
        got = engine.match_compiled(built, b"xabc", match_config=config)
        assert isinstance(got, driver.BadInput), config


def test_every_answer_the_analyzer_can_give_is_exercised(engine) -> None:
    # `ArShape` is the one no pattern reaches, because it means this engine
    # read its own compiler's tree and did not recognise it. The only way to
    # ask for it is to hand the analyzer a tree no compiler wrote, which is the
    # same thing the checker's structural cases do.
    doctored = compiled(b"abc").with_regions(
        (root(4), region("RkRepeat", 0, 0, 3))
    )
    seen = {engine.analyze(doctored)[0]} | {one.found for one in ANALYSED}
    assert seen == set(program().enum_map["Ar"].variants)


def test_a_reused_result_does_not_carry_the_last_patterns_certificate() -> None:
    """`compile` writes every field of its result, the certificate included.

    Python builds a fresh one per call, so this goes under the driver to ask
    what a caller of the generated Go or JavaScript would see if they did not.
    A slot left alone by a pattern the analyzer found no bound for would pair
    one pattern's bytecode with another pattern's bound, which is the one
    reading the availability flag exists to prevent.
    """
    interp = Engine()._interp()
    out = Cell(interp.zero(StructType("Out")))
    for pattern, wanted in ((b"abc", True), (b"a*b*c*d*", False)):
        interp.call("compile", [driver._blob(pattern), 0, 0, 0, out])
        assert out.value.fields["err"] == 0, pattern
        assert out.value.fields["re"].fields["hascert"] is wanted, pattern


@pytest.mark.parametrize("pattern", [b"(a+)+", b"a*b*c*d*"], ids=["ambiguous", "overflow"])
def test_the_tree_is_checked_even_when_there_is_no_bound_to_check(engine, pattern) -> None:
    """Where the two halves of the checker have to be asked separately.

    A pattern the composition rules cannot price still has a region tree, and a
    compiler that emitted a bad one is a bug of ours whether or not there was
    ever going to be a certificate. Gating the tree check on a certificate
    arriving would have left that bug hiding behind exactly the patterns the
    analyzer gives up on, so compilation asks `cert_shape` before it asks the
    analyzer for anything.
    """
    built = compiled(pattern)
    assert built.certificate is None
    tree = list(read(built).regions)
    doctored = built.with_regions((replace(tree[0], parent=0), *tree[1:]))
    assert engine.analyze(doctored)[0] in ("ArAmbiguous", "ArOverflow")
    assert engine.check_shape(doctored) == "CrRootParent"


def test_nothing_structural_is_left_in_the_pricing_walk(engine) -> None:
    """The split, asked of trees the corpus does not contain.

    Every verdict `cert_shape` is allowed to draw is one it has to draw:
    anything the whole checker refuses for a structural reason, the half that
    takes no certificate has to refuse for the same reason and by itself. A
    rule left behind in the pricing walk would still reach `cert_check` — the
    corpus would not notice — and would still be invisible to compilation on
    any pattern the analyzer gives up on, which is the whole of the finding.

    One field of one region at a time, which is enough: what the split can lose
    is a rule, and a rule that is gone is gone for the simplest tree that trips
    it.
    """
    seen = set()
    for pattern in (b"abc", b"(a)", b"a|b", b"a?", b"a*", b"a{2,5}", b"(ab)*c", b"(a|)"):
        built = compiled(pattern)
        tree = read(built).regions
        for at, one in enumerate(tree):
            for field, values in (
                ("kind", program().enum_map["Rk"].variants),
                ("parent", (0, 1, spec.NONE)),
                ("lo", (0, 1, one.hi + 1)),
                ("hi", (0, 1, one.lo, one.hi + 1)),
            ):
                now = getattr(one, field)
                for value in (v for v in values if v != now):
                    bent = (*tree[:at], replace(one, **{field: value}), *tree[at + 1 :])
                    try:
                        doctored = built.with_regions(bent)
                    except EngineError:
                        continue
                    verdict = engine.check_certificate(doctored, unpriced(len(bent)))
                    if verdict not in STRUCTURE:
                        continue
                    seen.add(verdict)
                    assert engine.check_shape(doctored) == verdict, (pattern, at, field, value)
    # A sweep that tripped two rules would pass this test while saying nothing
    # about the rest, so what it reached is named.
    assert len(seen) >= 8


def test_a_pattern_with_no_bound_still_compiles_and_still_matches(engine) -> None:
    # The contract of DESIGN.md section 5: the analysis may fail to find a
    # bound, and that is a fact about the bound rather than about the pattern.
    built = compiled(b"(?:a*)*")
    assert built.certificate is None
    assert engine.match_compiled(built, b"aaa").ovector[:2] == (0, 3)


def test_every_verdict_the_checker_can_give_has_a_case() -> None:
    # A refusal nothing trips is a refusal nobody has read, and the checker is
    # the piece the proofs will lean on hardest.
    assert {case.check for case in COMMITTED} == set(program().enum_map["Cr"].variants)


@pytest.mark.parametrize("names", [IDS, ANALYSIS_IDS], ids=["cases", "analyses"])
def test_no_two_entries_share_a_name(names) -> None:
    # The three runners report a failure by name, so a duplicate would send a
    # reader to the wrong one. The two halves are named apart, since they are
    # about a pattern from opposite ends and share several of them.
    assert len(names) == len(set(names))


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
    what the certificate said it could. The certificate is the one compilation
    produced, so this is the production path end to end. It is the small
    version of the fuzz assertion M5 finishes with; what it buys today is that
    the composition rules of BOUNDS.md were transcribed the way they were meant.
    """
    built = compiled(pattern)
    cert = built.certificate
    assert cert is not None
    assert engine.check_certificate(built, cert) == "CrOk"
    combinations = [()] + [(one,) for one in OPTIONS] + list(itertools.combinations(OPTIONS, 2))
    for subject in SUBJECTS:
        bounds = {key: engine.bound(cert, which, len(subject)) for key, which in KINDS}
        for start in range(len(subject) + 1):
            for options in combinations:
                out = engine.bt_match_compiled(
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
    assert engine.bound(cert("over-claimed-to-both-ceilings"), "BkCost", 0) == CAP


def test_arithmetic_that_would_saturate_is_reported_rather_than_clamped(engine) -> None:
    assert engine.bound(cert("over-claimed-to-both-ceilings"), "BkCost", 1) is None
    assert engine.bound(cert("over-claimed-past-both-ceilings"), "BkCost", 0) is None


def test_a_bound_no_limit_could_accept_is_exceeds_budget(engine) -> None:
    # Section 2.4 asks for more than "it fits in a counter": any number these
    # accessors give back has to be one the caller can turn round and pass as a
    # limit, so the two projections with a ceiling of their own refuse at it.
    # The stack rows live on their own cases now that the checker holds that
    # bound to equality and the generous certificates keep it exact.
    assert engine.bound(cert("over-claimed-to-both-ceilings"), "BkMem", 4) == CEILING
    assert engine.bound(cert("over-claimed-past-both-ceilings"), "BkMem", 4) is None
    assert engine.bound(cert("a-stack-at-its-ceiling"), "BkStack", 4) == spec.MAX_STACK
    assert engine.bound(cert("a-stack-past-its-ceiling"), "BkStack", 4) is None


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
"""The verdicts that are about the tree rather than about the numbers in it.

Two tests read it, and they read it in opposite directions: a tree the compiler
emitted may never draw one of these, and a tree that draws one has to draw it
from the half of the checker that takes no certificate.

`CrShape` is in the list because a program the checker cannot read is one of
the things it means. The other is a certificate field naming no variant of its
enum, which is why a case records which half answered rather than deriving it
from the verdict.
"""


def _emitted(patterns):
    """Every one of these that compiles, and a failed test for one that cannot.

    A pattern outside wave 1 is skipped, because there is nothing to say about
    the tree or the bound of a program nobody generated. Our own internal error
    is not that: it is what compilation reports when the analyzer and the
    checker disagree about a program, and a sweep that skipped it would be
    blind to the one failure it is here to find.
    """
    for pattern in patterns:
        built = certificate_corpus.attempted(pattern)
        assert not isinstance(built, InternalError), (
            f"{pattern!r}: the analyzer and the checker disagree"
        )
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


# --- what the analyzer comes up with ---


def test_the_analyzer_agrees_with_the_reference_pricer_exactly() -> None:
    """Two statements of BOUNDS.md, compared coefficient by coefficient.

    `price` is the corpus's own reading of the same document, written in Python
    and never run in production; the analyzer is the one compilation runs. They
    share the rules and nothing else, so the interesting thing is not that both
    produce a certificate the checker accepts — the checker would say so about
    either — but that they produce the same one, down to the class claim and
    the last coefficient of every region.

    And where the rules have no answer they have to have no answer together.
    An analyzer that quietly found a bound the reference refuses would be
    claiming something the reference could not check.
    """
    for pattern, built in _emitted(PRICED + SHAPES):
        try:
            want = certificate_corpus.price(read(built))
        except ValueError:
            want = None
        assert built.certificate == want, pattern


def test_every_pattern_of_the_wave_one_corpus_is_priced_or_refused(engine) -> None:
    """The definition of done for the backtracking analyzer, over everything.

    Two outcomes and no third. `_emitted` fails on the third — an internal
    error, which is what compilation reports when the analyzer and the checker
    disagree about a program — so what running the checker again adds is the
    round trip: the certificate as it comes back out of a compiled pattern,
    which the compiler itself never makes.
    """
    priced = 0
    for pattern, built in _emitted(one.pattern for one in wave1.load().cases):
        if built.certificate is None:
            continue
        assert engine.check_certificate(built, built.certificate) == "CrOk", pattern
        priced += 1
    # Not an assertion about the number, only that the loop had something to
    # do: a bug that returned no certificate for anything would otherwise pass
    # this test by never entering it.
    assert priced > 50


def test_generated_patterns_are_priced_or_refused_too() -> None:
    """The same, on patterns nobody wrote down.

    The failure this is really about is the one no hand-written corpus can be
    relied on to find, and it is `_emitted` that catches it. The round trip is
    not repeated here — it is the same round trip, and this list is five times
    longer — so what is left is the count, which says the shapes below reached
    the analyzer at all rather than being skipped as outside wave 1.
    """
    generated = [text.encode("latin-1") for text in differential._patterns(seed=5, extra=200)]
    assert sum(built.certificate is not None for _, built in _emitted(generated)) > 150


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
