"""A generated differential sweep, small enough to run every time.

The hand-written corpus says what wave 1 is supposed to do; this says the same
thing about patterns nobody wrote down. It is deliberately modest — a seeded
generator, a few thousand comparisons — because DESIGN.md section 8's real
fuzzing infrastructure is M9's, and because a test that takes a minute stops
being run. The generators in `tmp/` are the same shapes at a much larger scale.

Cases our engine declines are skipped rather than compared, which is the oracle
policy of DESIGN.md section 1: a construct outside the claimed subset, a
pattern past a documented limit, and a run over budget are all outcomes pcre2
has no opinion about. Our own internal error is not one of them, and it is not
in `DECLINED` — it is a bug of ours, and a skip would hide it on exactly the
patterns nobody wrote down.
"""

from __future__ import annotations

import itertools
import random

import pytest

from pcrevera.engine import (
    BadInput,
    Engine,
    Limits,
    ResourceExceeded,
    TooLarge,
    Unsupported,
)
from pcrevera.oracle.client import Compiled, CompileError, Match, NoMatch

ATOMS = (
    "a", "b", ".", "[a-c]", "[^a-c]", r"\d", r"\D", r"\w", r"\s", r"\S",
    r"\h", r"\v", r"\R", "[[:alpha:]]", "[[:^digit:]]", "[]a]", "[a-]",
    "^", "$", r"\A", r"\z", r"\Z", r"\b", r"\B", r"\Qa.c\E", r"\x41", r"\cA",
    "(a)", "(?:ab)", "(?<n>a)", "(a|b)", "(a|)", "(|a)", "(?i)a", "(?i:ab)", "(?#x)a",
)

QUANTIFIERS = ("", "*", "+", "?", "??", "*?", "{2}", "{1,3}", "{0,2}", "{2,}", "{2,3}?")

SUBJECTS = (
    "", "a", "ab", "aaa", "aab", "\n", "a\n", "a\r\nb", "A", "aBc", " a ",
    "a_1", "\x0b", "\x85", "\xa0", "\xff", "a-c", "]a", "aaaaab",
)

OPTION_SETS = (
    (),
    ("CASELESS",),
    ("MULTILINE",),
    ("DOTALL",),
    ("EXTENDED",),
    ("UNGREEDY",),
    ("ANCHORED",),
    ("ENDANCHORED",),
    ("DOLLAR_ENDONLY",),
)

MATCH_OPTION_SETS = ((), ("NOTBOL",), ("NOTEOL",), ("NOTEMPTY",), ("NOTEMPTY_ATSTART",))

CONVENTIONS = (("LF", "UNICODE"), ("CR", "UNICODE"), ("CRLF", "UNICODE"),
               ("ANYCRLF", "ANYCRLF"), ("ANY", "UNICODE"))

DECLINED = (Unsupported, TooLarge, ResourceExceeded, BadInput)

BUDGET = Limits(cost=200_000, stack=1 << 16, memory=1 << 22)


def _piece(rng: random.Random, depth: int) -> str:
    if depth > 0 and rng.random() < 0.4:
        opener = rng.choice(["(", "(?:", "(?i:", "(?s:", "(?m:"])
        return opener + _sequence(rng, depth - 1) + ")"
    return rng.choice(ATOMS)


def _sequence(rng: random.Random, depth: int) -> str:
    branches = []
    for _ in range(rng.randint(1, 2)):
        parts = [_piece(rng, depth) + rng.choice(QUANTIFIERS) for _ in range(rng.randint(1, 3))]
        branches.append("".join(parts))
    return "|".join(branches)


def _patterns(seed: int, extra: int) -> list[str]:
    rng = random.Random(seed)
    out = [atom + quant for atom, quant in itertools.product(ATOMS, QUANTIFIERS)]
    out += [_sequence(rng, rng.randint(0, 2)) for _ in range(extra)]
    return out


def _same(ours, theirs) -> bool:
    if isinstance(theirs, Match):
        return isinstance(ours, Match) and ours.ovector == theirs.ovector
    if isinstance(theirs, NoMatch):
        return isinstance(ours, NoMatch)
    if isinstance(theirs, CompileError):
        return isinstance(ours, CompileError) and (ours.code, ours.offset) == (
            theirs.code,
            theirs.offset,
        )
    if isinstance(theirs, Compiled):
        return (
            isinstance(ours, Compiled)
            and ours.capture_count == theirs.capture_count
            and tuple(sorted(ours.names)) == tuple(sorted(theirs.names))
        )
    return False


def test_generated_patterns_agree_with_pcre2(oracle) -> None:
    engine = Engine()
    rng = random.Random(20260801)
    complaints = []
    compared = 0
    for text in _patterns(seed=1, extra=120):
        pattern = text.encode("latin-1")
        options = rng.choice(OPTION_SETS)
        newline, bsr = rng.choice(CONVENTIONS)
        ours = engine.compile(pattern, options=options, newline=newline, bsr=bsr)
        if isinstance(ours, DECLINED):
            continue
        theirs = oracle.compile(pattern, options=options, newline=newline, bsr=bsr)
        compared += 1
        if not _same(ours, theirs):
            complaints.append(f"compile {text!r} {options}: ours {ours!r}, pcre2 {theirs!r}")
            continue
        if isinstance(theirs, CompileError):
            continue
        for subject_text in SUBJECTS:
            subject = subject_text.encode("latin-1")
            match_options = rng.choice(MATCH_OPTION_SETS)
            start = rng.choice([0, 0, 0, min(1, len(subject)), len(subject)])
            ours = engine.match(
                pattern, subject, start=start, options=options,
                match_options=match_options, newline=newline, bsr=bsr, limits=BUDGET,
            )
            if isinstance(ours, DECLINED):
                continue
            theirs = oracle.match(
                pattern, subject, start=start, options=options,
                match_options=match_options, newline=newline, bsr=bsr,
            )
            compared += 1
            if not _same(ours, theirs):
                complaints.append(
                    f"match {text!r} on {subject_text!r} at {start} {options} "
                    f"{match_options} nl={newline}: ours {ours!r}, pcre2 {theirs!r}"
                )
    assert compared > 3000, f"only {compared} comparisons ran"
    assert not complaints, "\n".join(complaints[:20])


@pytest.mark.parametrize("size", [1, 2])
def test_every_short_pattern_agrees_with_pcre2(oracle, size: int) -> None:
    """Exhaustive over a hostile alphabet, which is where the offsets live."""
    alphabet = b"()[]{}|*+?.\\^$#:-<>=!'\"PianmsUxQERdDwWhvzZAbBcko128 \t\n"
    engine = Engine()
    complaints = []
    for combination in itertools.product(alphabet, repeat=size):
        pattern = bytes(combination)
        ours = engine.compile(pattern)
        if isinstance(ours, DECLINED):
            continue
        theirs = oracle.compile(pattern)
        if not _same(ours, theirs):
            complaints.append(f"{pattern!r}: ours {ours!r}, pcre2 {theirs!r}")
    assert not complaints, "\n".join(complaints[:20])


MATCHER_PATTERNS = [
    rb"(a|)+", rb"(a?)*", rb"(a*)*", rb"(a?){2,4}", rb"(|a){1,3}",
    rb"(?:(a)x|ab)", rb"((a|b)*)(b)", rb"^a*$", rb"\ba*\b", rb"^.*$",
    rb"[^a]+b", rb"\R+",
]

MATCHER_OPTIONS = [(), ("MULTILINE",), ("ENDANCHORED",)]
MATCHER_MATCH_OPTIONS = [(), ("NOTEOL",), ("NOTEMPTY",)]


def _subjects(alphabet: bytes, length: int) -> list[bytes]:
    out = [b""]
    for size in range(1, length + 1):
        out += [bytes(c) for c in itertools.product(alphabet, repeat=size)]
    return out


@pytest.mark.parametrize("newline", ["LF", "CRLF"])
def test_every_short_subject_agrees_with_pcre2(oracle, newline: str) -> None:
    """The other sweeps enumerate patterns and sample subjects; this reverses that.

    Backtracking order, capture restoration and the empty-iteration rule are
    decided by the subject, so the patterns that turn on them get every subject
    up to three bytes rather than a sample of them. The version in `tmp/` runs
    the same shape over a hundred times wider; this one is sized to be run.
    """
    engine = Engine()
    complaints = []
    subjects = _subjects(b"ab\n", 3)
    for pattern in MATCHER_PATTERNS:
        for options in MATCHER_OPTIONS:
            for match_options in MATCHER_MATCH_OPTIONS:
                for subject in subjects:
                    ours = engine.match(
                        pattern, subject, options=options,
                        match_options=match_options, newline=newline, limits=BUDGET,
                    )
                    if isinstance(ours, DECLINED):
                        continue
                    theirs = oracle.match(
                        pattern, subject, options=options,
                        match_options=match_options, newline=newline,
                    )
                    if not _same(ours, theirs):
                        complaints.append(
                            f"{pattern!r} on {subject!r} {options} {match_options} "
                            f"nl={newline}: ours {ours!r}, pcre2 {theirs!r}"
                        )
    assert not complaints, "\n".join(complaints[:20])
