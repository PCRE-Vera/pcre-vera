"""Exhaustive differential sweeps, small enough to run every time.

The hand-written corpus says what wave 1 is supposed to do; this says the same
thing about patterns nobody wrote down. What is here is the exhaustive half —
every pattern of one and two bytes over a hostile alphabet, and every subject
of up to three bytes for the patterns whose answers depend on the subject —
because at those sizes enumerating is cheaper than generating and misses
nothing.

The generated half moved to `pcrevera.sweep`, and `tests/test_sweep.py` is what
runs it on every commit. That is the point of the move: the campaign of
DESIGN.md section 8 and the smoke test that guards it now generate from one
place, so a shape only one of them knows about is not a thing that can happen.

Cases our engine declines are skipped rather than compared, which is the oracle
policy of DESIGN.md section 1: a construct outside the claimed subset, a
pattern past a documented limit, and a run over budget are all outcomes pcre2
has no opinion about. Our own internal error is not one of them, and it is not
in `DECLINED` — it is a bug of ours, and a skip would hide it on exactly the
patterns nobody wrote down.
"""

from __future__ import annotations

import itertools

import pytest

from pcrevera.engine import (
    BadInput,
    Engine,
    Limits,
    ResourceExceeded,
    TooLarge,
    Unsupported,
)
from pcrevera.sweep.checks import agrees
from pcrevera.sweep.manifest import DEFAULT_BUDGET

DECLINED = (Unsupported, TooLarge, ResourceExceeded, BadInput)

BUDGET = Limits(**DEFAULT_BUDGET)
"""The sweep's own, since the decline policy these tests apply is stated
relative to it: two budgets drifting apart would have the two halves of the
differential testing decline different sets of cases."""


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
        if not agrees(ours, theirs):
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
    """The sweep enumerates patterns and samples subjects; this reverses that.

    Backtracking order, capture restoration and the empty-iteration rule are
    decided by the subject, so the patterns that turn on them get every subject
    up to three bytes rather than a sample of them.
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
                    if not agrees(ours, theirs):
                        complaints.append(
                            f"{pattern!r} on {subject!r} {options} {match_options} "
                            f"nl={newline}: ours {ours!r}, pcre2 {theirs!r}"
                        )
    assert not complaints, "\n".join(complaints[:20])
