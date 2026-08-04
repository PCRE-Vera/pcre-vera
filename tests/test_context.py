"""The preallocated context, against the reference interpreter.

Three kinds of question. The corpus section, replayed through the public
driver the way the Go and JavaScript runners replay it through their
wrappers, so the frozen creation and reuse contract is what all three
languages answer. The physical claim, which only this file can ask exactly:
the capacities the context's arrays really hold, weighed at the IR sizes,
sum to the memory bound — the accessors' number made physical. And the
reuse edges the corpus keeps short, exercised at more length here.
"""

from __future__ import annotations

import pytest

from pcrevera.engine import spec
from pcrevera.engine.certificate_corpus import compiled, contexts, load_contexts
from pcrevera.engine.driver import (
    WEIGHED,
    BadInput,
    Engine,
    Limits,
    Match,
    NoMatch,
    ResourceExceeded,
)
from pcrevera.tir.interp import Seq, StructValue

ENGINE = Engine()

ENTRIES = load_contexts()


def test_the_context_corpus_says_the_same_thing_as_the_entries_it_came_from():
    assert ENTRIES == contexts()


def _limits(row: dict) -> Limits:
    return Limits(cost=row["cost"], stack=row["stack"], memory=row["memory"])


@pytest.mark.parametrize("entry", ENTRIES, ids=lambda e: e["name"])
def test_the_creation_ladder(entry):
    built = compiled(bytes.fromhex(entry["pattern"]))
    for row in entry["creations"]:
        status, held = ENGINE.create_context(
            built,
            max_subject_len=row["maxlen"],
            limits=_limits(row),
            match_config=row["config"],
        )
        where = f"{entry['name']}: {row}"
        assert status == row["status"], where
        if "memcap" in row:
            assert held is not None and held.memory == row["memcap"], where
        else:
            assert held is None, where


@pytest.mark.parametrize(
    "entry", [e for e in ENTRIES if e["calls"]], ids=lambda e: e["name"]
)
def test_one_context_answers_its_calls_in_order(entry):
    built = compiled(bytes.fromhex(entry["pattern"]))
    status, held = ENGINE.create_context(built, max_subject_len=entry["maxlen"])
    assert status == spec.OK and held is not None
    for row in entry["calls"]:
        got = ENGINE.context_match(
            held,
            bytes.fromhex(row["subject"]),
            start=row["start"],
            cost_limit=row["cost"],
            stack_limit=row["stack"],
        )
        where = f"{entry['name']}: {row}"
        if row["status"] == spec.MATCHED:
            assert isinstance(got, Match), where
            assert list(got.ovector) == row["ovector"], where
        elif row["status"] == spec.NO_MATCH:
            assert isinstance(got, NoMatch), where
        elif row["status"] == spec.RESOURCE_EXCEEDED:
            assert isinstance(got, ResourceExceeded), where
        else:
            assert isinstance(got, BadInput), where


def _arrays(value: StructValue) -> int:
    """The bytes a context struct's arrays hold, weighed at the IR sizes.

    The weights are the driver's, since the sum they are for is the contract
    rather than this test's opinion of it; what is here is the half of it that
    a context built without a wrapper has, for the recreation test below.
    """
    total = 0
    for name, esize in WEIGHED:
        array = value.fields[name]
        assert isinstance(array, Seq)
        total += array.cap * esize
    return total


@pytest.mark.parametrize(
    "pattern, maxlen",
    [
        (b"abc", 64),
        (b"(a)(b*)", 64),
        (b"a*", 0),
        (b"a{1,2}", 16),
        (b"a{0,2}b*", 32),
        (b"(ab)*c", 100),
        (b"(?:a|a){0,3}", 7),
    ],
    ids=lambda v: v if isinstance(v, int) else v.decode(),
)
def test_the_reservation_is_the_memory_bound_made_physical(pattern, maxlen):
    built = compiled(pattern)
    status, held = ENGINE.create_context(built, max_subject_len=maxlen)
    assert status == spec.OK and held is not None
    answered = ENGINE.worst_case(built, "mem", maxlen)
    assert answered == (spec.OK, held.memory)
    assert held.resident == held.memory


def test_recreating_over_a_larger_context_lets_its_arrays_go():
    """The generated entry point accepts any well-typed destination, and
    `reserve` never shrinks, so recreation has to replace the arrays rather
    than reserve into them — otherwise a small context built over a large
    one would keep the large one's capacity and break the equality."""
    from pcrevera.tir.interp import Cell
    from pcrevera.tir.types import StructType

    big = compiled(b"a{0,2}b*")
    small = compiled(b"abc")
    held = Cell(ENGINE._interp().zero(StructType("Ctx")))
    first = ENGINE._interp(10**9).call(
        "ctx_create", [big.re, 0, 32, 10**9, 100_000, 2**31 - 1, held]
    )
    assert first == spec.OK
    second = ENGINE._interp(10**9).call(
        "ctx_create", [small.re, 0, 0, 10**9, 100_000, 2**31 - 1, held]
    )
    assert second == spec.OK
    value = held.value
    assert isinstance(value, StructValue)
    arrays = _arrays(value)
    novec = 2 * (small.captures + 1)
    memcap = value.fields["memcap"]
    # No wrapper in this test, so the two result stores one would hold are
    # accounted at their model share.
    assert arrays + 2 * novec * spec.REG_SIZE == memcap
    assert (spec.OK, memcap) == ENGINE.worst_case(small, "mem", 0)


def test_capacities_hold_still_across_the_context_lifetime():
    """No call may grow anything: the reservation at creation is the story."""
    built = compiled(b"a{0,2}b*")
    status, held = ENGINE.create_context(built, max_subject_len=32)
    assert status == spec.OK and held is not None
    before = held.resident
    for subject in (b"aab", b"b" * 32, b"", b"x" * 33, b"aabbbb"):
        ENGINE.context_match(held, subject)
    ENGINE.context_match(held, b"aab", cost_limit=1)
    ENGINE.context_match(held, b"aab", stack_limit=0)
    assert held.resident == before


def test_a_context_call_reports_the_reservation_as_its_memory():
    """Not the transient peak a plain call would report: the reservation is
    resident for the call's whole life whatever the subject was, which is
    the constant DESIGN.md section 2.4 pins the context's memory component
    to. Cost and stack stay per-call."""
    built = compiled(b"a{0,2}b*")
    status, held = ENGINE.create_context(built, max_subject_len=32)
    assert status == spec.OK and held is not None
    for subject in (b"aab", b"zzz", b""):
        ENGINE.context_match(held, subject)
        assert ENGINE.last_usage is not None
        assert ENGINE.last_usage.memory == held.memory
    plain = ENGINE.match_compiled(built, b"aab")
    assert plain is not None and ENGINE.last_usage is not None
    assert ENGINE.last_usage.memory < held.memory


def test_the_ovector_is_overwritten_by_the_next_call():
    built = compiled(b"(a)(b*)")
    status, held = ENGINE.create_context(built, max_subject_len=8)
    assert status == spec.OK and held is not None
    first = ENGINE.context_match(held, b"abb")
    assert isinstance(first, Match) and first.ovector == (0, 3, 0, 1, 1, 3)
    second = ENGINE.context_match(held, b"xa")
    assert isinstance(second, Match) and second.ovector == (1, 2, 1, 2, 2, 2)


def test_the_context_agrees_with_the_plain_matcher():
    """Same pattern, same subjects, one context against fresh scratch."""
    for pattern in (b"abc", b"(a)(b*)", b"a{0,2}b*", b"a*b", b"(?:a|a){0,3}"):
        built = compiled(pattern)
        status, held = ENGINE.create_context(built, max_subject_len=16)
        assert status == spec.OK and held is not None
        for subject in (b"", b"a", b"ab", b"abb", b"xabc", b"b" * 16, b"aab"):
            again = ENGINE.context_match(held, subject)
            plain = ENGINE.match_compiled(built, subject)
            assert again == plain, (pattern, subject)


def test_a_context_outlives_the_interpreter_that_made_it():
    """Every call gets a fresh interpreter over the same cell, which is the
    same separation the wrappers have between the module and the context."""
    built = compiled(b"abc")
    status, held = ENGINE.create_context(built, max_subject_len=8)
    assert status == spec.OK and held is not None
    for _ in range(3):
        assert isinstance(ENGINE.context_match(held, b"abc"), Match)
