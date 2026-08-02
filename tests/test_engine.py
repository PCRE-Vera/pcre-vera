"""The engine's own contract: what it refuses, and what it charges.

Nothing here needs pcre2. These are the outcomes DESIGN.md section 2.4 defines
for us rather than the ones we reproduce: an unsupported construct, a pattern
past a documented limit, a run over budget, and bad input.
"""

from __future__ import annotations

import pytest

from pcretruste.engine import (
    BadInput,
    Engine,
    Limits,
    ResourceExceeded,
    TooLarge,
    Unsupported,
    spec,
)
from pcretruste.oracle.client import CompileError, Compiled, Match, NoMatch


@pytest.fixture(scope="module")
def engine() -> Engine:
    return Engine()


# --- what is out of the wave 1 subset ---


@pytest.mark.parametrize(
    "pattern",
    [
        rb"(a)\1",
        rb"(?<x>a)\k<x>",
        rb"a(?=b)",
        rb"a(?!b)",
        rb"(?<=a)b",
        rb"(?<!a)b",
        rb"(?>a+)",
        rb"a++",
        rb"a*+",
        rb"a{2,3}+",
        rb"\G a",
        rb"a\Kb",
        rb"\p{Lu}",
        rb"\X",
        rb"\N",
        rb"(?(1)a)",
        rb"(?R)",
        rb"(?1)",
        rb"(?&name)",
        rb"(a)\g1",
        rb"(a)\g{-1}",
        rb"(a)\g{ +1 }(b)",
        rb"\g<0>",
        rb"(a)\g<1>",
        rb"(?<a>x)\g'a'",
        rb"(?<a>x)\k{ a }",
        rb"\pL",
        rb"\p{^L}",
        rb"[\p{L}]",
    ],
)
def test_wave_two_and_three_constructs_are_refused_as_ours(engine: Engine, pattern: bytes) -> None:
    """Never a repurposed pcre2 code: our own, so a caller can tell them apart."""
    outcome = engine.compile(pattern)
    assert isinstance(outcome, Unsupported), outcome
    assert outcome.code == spec.E_UNSUPPORTED_FEATURE


@pytest.mark.parametrize("option", ["UTF", "UCP", "NO_AUTO_CAPTURE", "DUPNAMES"])
def test_unsupported_options_are_refused_as_ours(engine: Engine, option: str) -> None:
    outcome = engine.compile(b"a", options=[option])
    assert isinstance(outcome, Unsupported)
    assert outcome.code == spec.E_UNSUPPORTED_OPTION


@pytest.mark.parametrize("pattern", [rb"(?n)a", rb"(?J)a", rb"(?^)a"])
def test_inline_options_we_do_not_have_are_refused_as_ours(engine: Engine, pattern: bytes) -> None:
    outcome = engine.compile(pattern)
    assert isinstance(outcome, Unsupported)
    assert outcome.code == spec.E_UNSUPPORTED_OPTION


def test_a_genuine_syntax_error_keeps_pcre2s_code(engine: Engine) -> None:
    outcome = engine.compile(b"(a")
    assert isinstance(outcome, CompileError)
    assert (outcome.code, outcome.offset) == (114, 2)


def test_a_malformed_unsupported_escape_is_still_pcre2s_error(engine: Engine) -> None:
    """The corpus pins the whole table; this pins the principle without pcre2."""
    outcome = engine.compile(rb"\g")
    assert isinstance(outcome, CompileError)
    assert (outcome.code, outcome.offset) == (spec.E_BAD_G_ESCAPE, 2)


# --- the eight auto-possessification shapes ---


@pytest.mark.parametrize(
    "pattern",
    [rb"\s|\R*", rb"\s\R*", rb".\R*", rb"(\s)|(\R*)", rb"\R*", rb"\R*x"],
)
def test_a_repeat_whose_unsafe_partner_never_follows_compiles(engine: Engine, pattern: bytes) -> None:
    assert isinstance(engine.compile(pattern), Compiled)


@pytest.mark.parametrize(
    "pattern",
    [rb"\R*\s", rb"\R*.", rb"(?:\s\R*){2}", rb"(?:\s\R*)+", rb"(a)*\R*\s"],
)
def test_a_repeat_pcre2_would_mispossessify_is_refused(engine: Engine, pattern: bytes) -> None:
    outcome = engine.compile(pattern)
    assert isinstance(outcome, Unsupported)
    assert outcome.code == spec.E_UNSUPPORTED_FEATURE


# --- the documented portable limits ---


def test_an_oversized_pattern_is_refused(engine: Engine) -> None:
    assert isinstance(engine.compile(b"a" * (spec.MAX_PATTERN + 1)), TooLarge)


def test_a_pattern_at_the_length_limit_still_compiles(engine: Engine) -> None:
    assert isinstance(engine.compile(b"a" * spec.MAX_PATTERN), Compiled)


def test_nesting_past_the_parse_depth_is_a_pcre2_error(engine: Engine) -> None:
    outcome = engine.compile(b"(" * (spec.MAX_DEPTH + 1) + b"a")
    assert isinstance(outcome, CompileError)
    assert outcome.code == spec.E_TOO_DEEP


def test_nesting_at_the_parse_depth_compiles(engine: Engine) -> None:
    depth = spec.MAX_DEPTH
    outcome = engine.match(b"(" * depth + b"a" + b")" * depth, b"a")
    assert isinstance(outcome, Match)
    assert outcome.span == (0, 1)


def test_too_many_groups_is_refused(engine: Engine) -> None:
    assert isinstance(engine.compile(b"(a)" * (spec.MAX_GROUPS + 1)), TooLarge)


def test_the_arena_limits_sit_behind_the_length_limit(engine: Engine) -> None:
    """The three derived caps are safety nets, not something a caller trips."""
    assert spec.MAX_NODES >= 2 * spec.MAX_PATTERN
    assert spec.MAX_CODE >= 4 * spec.MAX_NODES
    assert spec.MAX_CLASSES >= spec.MAX_PATTERN
    assert spec.MAX_REPS >= spec.MAX_PATTERN // 2
    assert spec.MAX_REFS >= spec.MAX_PATTERN // 2


def test_the_scratch_arrays_have_no_limit_of_their_own(engine: Engine) -> None:
    """The caller's stack and memory budgets are the only bounds a run can hit:
    the declared maxima are exactly what the allocation ceiling admits, so the
    accepted stack limit reaches the declared maximum and every trail the
    memory limit allows fits under its own."""
    from pcretruste.engine.driver import MAX_MEMORY_LIMIT, MAX_STACK_LIMIT
    from pcretruste.tir.types import CEILING

    assert spec.MAX_STACK == CEILING // spec.BT_SIZE == MAX_STACK_LIMIT
    assert spec.MAX_TRAIL == CEILING // spec.UNDO_SIZE
    assert spec.MAX_TRAIL * spec.UNDO_SIZE >= MAX_MEMORY_LIMIT - spec.UNDO_SIZE


# --- runtime limits ---

PATHOLOGICAL = rb"(?:a+)+b"
SUBJECT = b"a" * 22


def test_a_pathological_pattern_runs_out_of_cost(engine: Engine) -> None:
    outcome = engine.match(
        PATHOLOGICAL, SUBJECT, limits=Limits(cost=50_000, stack=1 << 20, memory=1 << 26)
    )
    assert isinstance(outcome, ResourceExceeded)


def test_a_pathological_pattern_runs_out_of_stack(engine: Engine) -> None:
    outcome = engine.match(
        PATHOLOGICAL, SUBJECT, limits=Limits(cost=1 << 40, stack=8, memory=1 << 26)
    )
    assert isinstance(outcome, ResourceExceeded)


def test_a_match_runs_out_of_scratch_memory(engine: Engine) -> None:
    outcome = engine.match(
        PATHOLOGICAL, SUBJECT, limits=Limits(cost=1 << 40, stack=1 << 20, memory=64)
    )
    assert isinstance(outcome, ResourceExceeded)


def test_setup_alone_can_exceed_the_memory_limit(engine: Engine) -> None:
    assert isinstance(engine.match(b"a", b"a", limits=Limits(memory=1)), ResourceExceeded)


def test_handing_the_answer_back_is_charged_for(engine: Engine) -> None:
    """Every unit of an anchored run of `abc`, named.

    The register file and the ovector zeroed once is 16, clearing the registers
    for the one starting position is 8, the four instructions are 4, and
    copying the two ovector slots back out to the caller is 8. A subject that
    fails on the first character never reaches the copy, which is what makes
    the last of those visible rather than assumed.
    """
    roomy = Limits(cost=1 << 20, stack=1 << 10, memory=1 << 20)
    engine.match(b"abc", b"abc", match_options=["ANCHORED"], limits=roomy)
    assert engine.last_usage is not None and engine.last_usage.cost == 16 + 8 + 4 + 8
    engine.match(b"abc", b"xxx", match_options=["ANCHORED"], limits=roomy)
    assert engine.last_usage is not None and engine.last_usage.cost == 16 + 8 + 1

    # A call whose budget does not stretch to delivering its own result has
    # gone over it, and says so rather than copying for free.
    short = Limits(cost=16 + 8 + 4 + 7, stack=1 << 10, memory=1 << 20)
    outcome = engine.match(b"abc", b"abc", match_options=["ANCHORED"], limits=short)
    assert isinstance(outcome, ResourceExceeded)


def test_the_cost_limit_is_exact_at_the_edge(engine: Engine) -> None:
    """DESIGN.md section 8: at the observed actual it succeeds, one below it does not."""
    engine.match(b"a+b", b"aaab")
    used = engine.last_usage
    assert used is not None and used.cost > 0
    generous = Limits(cost=used.cost, stack=1 << 20, memory=1 << 26)
    assert isinstance(engine.match(b"a+b", b"aaab", limits=generous), Match)
    tight = Limits(cost=used.cost - 1, stack=1 << 20, memory=1 << 26)
    assert isinstance(engine.match(b"a+b", b"aaab", limits=tight), ResourceExceeded)


def test_the_stack_limit_is_exact_at_the_edge(engine: Engine) -> None:
    engine.match(b"a+b", b"aaab")
    used = engine.last_usage
    assert used is not None and used.stack > 0
    at = Limits(cost=1 << 40, stack=used.stack, memory=1 << 26)
    assert isinstance(engine.match(b"a+b", b"aaab", limits=at), Match)
    below = Limits(cost=1 << 40, stack=used.stack - 1, memory=1 << 26)
    assert isinstance(engine.match(b"a+b", b"aaab", limits=below), ResourceExceeded)


def test_a_pattern_with_no_choice_points_never_touches_the_stack(engine: Engine) -> None:
    engine.match(b"abc", b"xxabc")
    used = engine.last_usage
    assert used is not None
    assert used.stack == 0


def test_usage_is_reported_for_a_failed_match(engine: Engine) -> None:
    assert isinstance(engine.match(b"zzz", b"aaaaa"), NoMatch)
    used = engine.last_usage
    assert used is not None and used.cost > 0


# --- bad input ---


def test_a_start_offset_past_the_subject_is_bad_input(engine: Engine) -> None:
    assert isinstance(engine.match(b"a", b"abc", start=4), BadInput)


def test_a_start_offset_at_the_end_is_fine(engine: Engine) -> None:
    assert isinstance(engine.match(b"a", b"abc", start=3), NoMatch)


def test_a_negative_start_offset_is_bad_input(engine: Engine) -> None:
    assert isinstance(engine.match(b"a", b"abc", start=-1), BadInput)


@pytest.mark.parametrize("start", [False, True, 1.0, 2**32])
def test_a_start_offset_that_is_not_a_whole_number_is_bad_input(engine: Engine, start) -> None:
    """The same exact-integer reading as the limits: a bool is not an offset."""
    assert isinstance(engine.match(b"a", b"abc", start=start), BadInput)


def test_an_unknown_match_option_is_refused(engine: Engine) -> None:
    outcome = engine.match(b"a", b"a", match_options=["PARTIAL_HARD"])
    assert isinstance(outcome, Unsupported)


# --- compilation, reused ---


def test_one_compiled_pattern_serves_many_matches(engine: Engine) -> None:
    built = engine.compile_pattern(rb"(\w+)@(\w+)")
    assert not isinstance(built, (CompileError, Unsupported, TooLarge))
    first = engine.match_compiled(built, b"say hi@there now")
    second = engine.match_compiled(built, b"a@b")
    assert isinstance(first, Match) and isinstance(second, Match)
    assert first.ovector == (4, 12, 4, 6, 7, 12)
    assert second.ovector == (0, 3, 0, 1, 2, 3)


def test_group_names_come_back_with_their_numbers(engine: Engine) -> None:
    outcome = engine.compile(rb"(?<host>\w+):(?<port>\d+)")
    assert isinstance(outcome, Compiled)
    assert sorted(outcome.names) == [(b"host", 1), (b"port", 2)]


# --- limits a caller may not name at all ---


@pytest.mark.parametrize(
    "limits",
    [
        Limits(cost=-1),
        Limits(stack=-1),
        Limits(memory=-1),
        Limits(cost=2**53),
        Limits(stack=2**31),
        Limits(memory=2**31),
        Limits(cost=1.5),
        Limits(cost=True),
    ],
)
def test_an_impossible_limit_is_bad_input(engine: Engine, limits: Limits) -> None:
    """DESIGN.md section 2.4: rejected, never silently clamped."""
    assert isinstance(engine.match(b"a", b"a", limits=limits), BadInput)


def test_the_limits_at_their_ceilings_are_accepted(engine: Engine) -> None:
    from pcretruste.engine.driver import (
        MAX_COST_LIMIT,
        MAX_MEMORY_LIMIT,
        MAX_STACK_LIMIT,
    )

    generous = Limits(cost=MAX_COST_LIMIT, stack=MAX_STACK_LIMIT, memory=MAX_MEMORY_LIMIT)
    assert isinstance(engine.match(b"a", b"a", limits=generous), Match)


def test_a_zero_cost_limit_is_a_resource_failure_not_a_crash(engine: Engine) -> None:
    assert isinstance(engine.match(b"a", b"a", limits=Limits(cost=0)), ResourceExceeded)
