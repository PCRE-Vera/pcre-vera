"""The Pike VM against the backtracking matcher, and against pcre2's answers.

DESIGN.md section 4.3 makes cross-matcher agreement a standing obligation: on
a Pike-eligible pattern the two matchers must return the same answer whenever
both run under sufficient budgets. These tests hold the lockstep matcher to
that from three directions — the hand-written cases here, every eligible case
of the wave 1 conformance corpus (whose expectations pcre2 also satisfies),
and a sweep of generated subjects. Both matchers run through their internal
entry points: the public `match` routes an eligible pattern to the Pike VM,
so plain backtracking on one is exactly the test-only configuration DESIGN.md
section 4.3 says it is.
"""

from __future__ import annotations

import functools
import itertools

import pytest

from pcrevera.engine import Engine, Limits, ResourceExceeded, spec
from pcrevera.oracle import conformance
from pcrevera.oracle.client import Match, NoMatch

ENGINE = Engine()


@functools.lru_cache(maxsize=None)
def compiled(pattern: bytes, options=(), newline="LF", bsr="UNICODE"):
    built = ENGINE.compile_pattern(
        pattern, options=options, newline=newline, bsr=bsr
    )
    assert hasattr(built, "re"), f"{pattern!r} failed to compile: {built}"
    return built


def same(built, subject: bytes, **kwargs) -> None:
    """Both matchers through their internal entry points, one comparison."""
    want = ENGINE.bt_match_compiled(built, subject, **kwargs)
    got = ENGINE.pike_match_compiled(built, subject, **kwargs)
    assert type(want) is type(got), f"on {subject!r} with {kwargs}: {want} vs {got}"
    if isinstance(want, Match):
        assert want.ovector == got.ovector, f"on {subject!r} with {kwargs}"


def agree(pattern: bytes, subject: bytes) -> None:
    built = compiled(pattern)
    assert ENGINE.pike_eligible(built), f"{pattern!r} should be eligible"
    same(built, subject)
    assert ENGINE.last_usage is not None
    assert ENGINE.last_usage.stack == 0


ELIGIBLE = [
    (b"abc", [b"abc", b"xxabcx", b"ab", b""]),
    (b"", [b"", b"x"]),
    (b"a|b", [b"b", b"ab", b"x"]),
    (b"(a)|(b)", [b"b", b"a", b""]),
    (b"a?", [b"a", b"", b"b"]),
    (b"a??", [b"a", b""]),
    (b"a*", [b"aaa", b"", b"baa"]),
    (b"a*?", [b"aaa", b""]),
    (b"(a)*", [b"", b"a", b"aa"]),
    (b"(ab)*", [b"ababx", b"", b"aba"]),
    (b"(a|b)*c", [b"abbac", b"c", b"x"]),
    (b"(a|ab)(c|bcd)", [b"abcd", b"acx", b"abcdx"]),
    (b"(a*)(b*)", [b"aabb", b"b", b"", b"ba"]),
    (b"(a|ab)*c", [b"ababc", b"aabc"]),
    (b"^a", [b"a", b"ba"]),
    (b"a$", [b"a", b"ab"]),
    (rb"\ba", [b"a", b"ba", b" a"]),
    (rb"\Bb", [b"ab", b"b"]),
    (b"[a-c]*d", [b"abcd", b"d", b"x"]),
    (b"(x?)(y?)z", [b"z", b"xz", b"yz", b"xyz"]),
    (b"a*b", [b"aaab", b"b", b"aaa"]),
    (b".", [b"a", b"\n", b""]),
    (b"(?:ab|a)(?:b|c)", [b"abc", b"abb", b"ab"]),
]


@pytest.mark.parametrize(
    "pattern,subject",
    [(p, s) for p, subjects in ELIGIBLE for s in subjects],
    ids=lambda v: repr(v)[1:],
)
def test_the_two_matchers_agree(pattern: bytes, subject: bytes) -> None:
    agree(pattern, subject)


def test_agreement_holds_across_match_options_and_offsets() -> None:
    built = compiled(b"(a*)b?$")
    for start, opts in itertools.product(
        (0, 1, 3),
        ((), ("NOTBOL",), ("NOTEOL",), ("NOTEMPTY",), ("NOTEMPTY_ATSTART",), ("ANCHORED",)),
    ):
        for subject in (b"aab", b"", b"xxx"):
            if start > len(subject):
                continue
            same(built, subject, start=start, match_options=opts)


def test_agreement_holds_under_compile_options() -> None:
    for pattern, options, subjects in (
        (b"ABC", ("CASELESS",), (b"abc", b"xabc")),
        (b"^b", ("MULTILINE",), (b"a\nb", b"b")),
        (b"a$", ("MULTILINE",), (b"a\nb", b"ba")),
        (b"a.b", ("DOTALL",), (b"a\nb", b"axb")),
        (b"a*", ("UNGREEDY",), (b"aaa",)),
        (b"ab", ("ANCHORED",), (b"ab", b"xab")),
        (b"ab", ("ENDANCHORED",), (b"ab", b"abx")),
    ):
        built = compiled(pattern, options=options)
        if not ENGINE.pike_eligible(built):
            continue
        for subject in subjects:
            same(built, subject)


def test_the_crlf_bumpalong_rule_is_shared() -> None:
    built = compiled(b"[\\S\\s]", newline="CRLF")
    for subject in (b"\r\n", b"x\r\ny"):
        for start in range(len(subject) + 1):
            same(built, subject, start=start)


def test_every_eligible_conformance_case_answers_the_same() -> None:
    """The wave 1 corpus, whose expectations the pinned pcre2 also satisfies.

    Every eligible match or no-match case runs on the Pike VM and must land
    on the pinned ovector, which ties this matcher to pcre2 through the same
    file that ties the backtracking one.
    """
    corpus = conformance.read(conformance.PATH)
    ran = 0
    for case in corpus["cases"]:
        expect = case["expect"]
        if expect["kind"] not in ("match", "nomatch"):
            continue
        built = ENGINE.compile_pattern(
            bytes.fromhex(case["pattern"]),
            options=_flags(case.get("flags", 0)),
            newline=_newline(case.get("newline", 0)),
            bsr=_bsr(case.get("bsr", 0)),
        )
        if not hasattr(built, "re") or not ENGINE.pike_eligible(built):
            continue
        got = ENGINE.pike_match_compiled(
            built,
            bytes.fromhex(case.get("subject") or ""),
            start=case.get("start", 0),
            match_options=_match_flags(case.get("matchFlags", 0)),
        )
        ran += 1
        if expect["kind"] == "nomatch":
            assert isinstance(got, NoMatch), case["name"]
        else:
            assert isinstance(got, Match), case["name"]
            assert list(got.ovector) == expect["ovector"], case["name"]
    # A refactor that quietly made everything ineligible would leave this
    # test green and empty, so the coverage itself is asserted.
    assert ran > 50, f"only {ran} conformance cases were eligible"


def _flags(bits: int):
    return [name for name, bit in spec.COMPILE_OPTIONS.items() if bits & bit]


def _match_flags(bits: int):
    return [name for name, bit in spec.MATCH_OPTIONS.items() if bits & bit]


def _newline(value: int) -> str:
    return {v: k for k, v in spec.NEWLINE_CONVENTIONS.items()}[value]


def _bsr(value: int) -> str:
    return {v: k for k, v in spec.BSR_CONVENTIONS.items()}[value]


def test_eligibility_is_the_documented_predicate() -> None:
    """Pure stars with consuming bodies; nothing counted, nullable, or \\R."""
    for pattern, eligible in (
        (b"a*", True),
        (b"(a|b)*", True),
        (b"(ab)*", True),
        (b"a?", True),
        (b"", True),
        (b"a+", False),
        (b"a{2,3}", False),
        (b"a{0,2}", False),
        (b"(a?)*", False),
        (b"(?:a*)*", False),
        (b"(a|)*", False),
        (rb"\R", False),
        (rb"(\b)*", False),
    ):
        built = compiled(pattern)
        assert ENGINE.pike_eligible(built) == eligible, pattern


def test_an_ineligible_pattern_is_bad_input_not_a_wrong_answer() -> None:
    """The engine's own refusal, per DESIGN.md section 6's `Exec` on a
    configuration the pattern is not eligible for.

    `a+` is the case that showed why: read as a pure-star fork it admits the
    zero-iteration exit and matches empty, so a missing guard is not a crash
    but a silently wrong pcre2 answer.
    """
    from pcrevera.engine import BadInput

    for pattern in (b"a+", b"a{2,3}", b"(a?)*", rb"\R"):
        built = compiled(pattern)
        assert not ENGINE.pike_eligible(built)
        got = ENGINE.pike_match_compiled(built, b"")
        assert isinstance(got, BadInput), pattern


def test_the_pike_matcher_respects_the_cost_limit() -> None:
    built = compiled(b"(a|b)*c")
    subject = b"ab" * 20
    full = ENGINE.pike_match_compiled(built, subject)
    assert isinstance(full, NoMatch)
    used = ENGINE.last_usage
    assert used is not None and used.cost > 0
    at_cost = ENGINE.pike_match_compiled(built, subject, limits=Limits(cost=used.cost))
    assert isinstance(at_cost, NoMatch)
    below = ENGINE.pike_match_compiled(
        built, subject, limits=Limits(cost=used.cost - 1)
    )
    assert isinstance(below, ResourceExceeded)


def test_the_pike_matcher_respects_the_memory_limit() -> None:
    built = compiled(b"(a|b)*c")
    subject = b"ab" * 20
    ENGINE.pike_match_compiled(built, subject)
    used = ENGINE.last_usage
    assert used is not None and used.memory > 0
    at_mem = ENGINE.pike_match_compiled(
        built, subject, limits=Limits(memory=used.memory)
    )
    assert isinstance(at_mem, NoMatch)
    below = ENGINE.pike_match_compiled(
        built, subject, limits=Limits(memory=used.memory - 1)
    )
    assert isinstance(below, ResourceExceeded)


def test_a_zero_stack_limit_never_bothers_the_pike_matcher() -> None:
    """No backtrack stack exists on this path, so no limit on it can bite."""
    built = compiled(b"(a|b)*c")
    got = ENGINE.pike_match_compiled(built, b"abac", limits=Limits(stack=0))
    assert isinstance(got, Match)
    assert ENGINE.last_usage is not None and ENGINE.last_usage.stack == 0


def test_the_pike_certificate_bounds_every_run() -> None:
    """The section 9 claim, exercised: no run charges past its closed form.

    Every eligible pattern below, over subjects, start offsets and option
    pairs, with the reported usage held under the stored Pike certificate's
    three bounds. The small sibling of the fuzz assertion M5 finishes with,
    and the empirical check that the formula dominates the charging.
    """
    from pcrevera.engine.certificate_corpus import KINDS

    options = [(), ("NOTEMPTY",), ("NOTBOL", "NOTEOL"), ("ANCHORED",)]
    for pattern in (b"abc", b"a*", b"(a|b)*c", b"(a*)(b*)", b"(?:a|a)*", b"a*b*c*d*"):
        built = compiled(pattern)
        assert ENGINE.pike_eligible(built)
        cert = built.pike_certificate
        assert cert is not None and cert.complexity == "CcLinear"
        assert ENGINE.check_certificate(built, cert, "CfgPike") == "CrOk"
        for subject in (b"", b"a", b"ab" * 3, b"aaaa", b"xa"):
            bounds = {
                key: ENGINE.bound(cert, which, len(subject)) for key, which in KINDS
            }
            for start in range(len(subject) + 1):
                for opts in options:
                    out = ENGINE.pike_match_compiled(
                        built, subject, start=start, match_options=list(opts)
                    )
                    assert not isinstance(out, ResourceExceeded)
                    use = ENGINE.last_usage
                    where = f"{pattern!r} on {subject!r} from {start} with {opts}"
                    assert use is not None
                    for key, seen in (
                        ("cost", use.cost),
                        ("stack", use.stack),
                        ("mem", use.memory),
                    ):
                        limit = bounds[key]
                        assert limit is None or seen <= limit, (
                            f"{key}: {seen} over {limit}, {where}"
                        )


def test_the_public_match_runs_the_selected_path() -> None:
    """Routing, observed from outside: an eligible pattern reports zero stack
    through the public match, an ineligible one pushes like a backtracker."""
    eligible = compiled(b"(a|b)*c")
    got = ENGINE.match_compiled(eligible, b"abac")
    assert isinstance(got, Match)
    assert ENGINE.last_usage is not None and ENGINE.last_usage.stack == 0
    counted = compiled(b"a{2,5}")
    got = ENGINE.match_compiled(counted, b"aaa")
    assert isinstance(got, Match)
    assert ENGINE.last_usage is not None and ENGINE.last_usage.stack > 0


def test_a_generated_sweep_of_subjects_agrees() -> None:
    """Structure-aware subjects over a two-letter alphabet, both matchers."""
    patterns = [b"(a|ab)*b", b"(a*)(b)?", b"[ab]*a", b"(?:a|b)*abb", b"(a)(b)*"]
    subjects = [
        bytes(word)
        for length in range(0, 7)
        for word in itertools.product(b"ab", repeat=length)
    ]
    for pattern in patterns:
        built = compiled(pattern)
        assert ENGINE.pike_eligible(built), pattern
        for subject in subjects:
            same(built, subject)
