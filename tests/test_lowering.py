"""The quantifier lowering: what it rewrites, what it declines, and the edge.

DESIGN.md section 4.3 says a counted repetition is lowered to star form when
the lowered form fits, and PLAN-POST-M6.md says what the evidence for that has
to be. The differential half of it lives in the sweep, whose quantifier matrix
crosses fourteen bodies with thirty-six spellings and compares every answer to
pcre2; what is here is the half a differential run cannot see — which form was
emitted, why, and where the boundary between the two is.

The boundary is read off the compiler's own dry run rather than guessed. That
matters twice over: a guessed number would stop describing the engine the
moment a cap moved, and the dry run is exactly the thing under test, so asking
it where the edge is and then compiling either side is what makes the answer
falsifiable.
"""

from __future__ import annotations

import pytest

from pcrevera.engine import Engine, spec
from pcrevera.engine.driver import CompiledPattern

ENGINE = Engine()

EMAIL = rb"(?<user>\w+)@(?<host>[\w.]+)"
"""The pattern this whole change exists for."""


def compiled(pattern: bytes) -> CompiledPattern:
    built = ENGINE.compile_pattern(pattern)
    assert isinstance(built, CompiledPattern), (pattern, built)
    return built


def plan(pattern: bytes) -> tuple[int, int, bool]:
    return ENGINE.lowering_plan(pattern)


# --- what the pre-check decides, on the original tree ---


@pytest.mark.parametrize(
    "pattern,blockers,decision",
    [
        # Already canonical: nothing here has a counted form to rewrite.
        (rb"abc", 0, spec.LOW_NOT_NEEDED),
        (rb"a?", 0, spec.LOW_NOT_NEEDED),
        (rb"a??", 0, spec.LOW_NOT_NEEDED),
        (rb"a{0,1}", 0, spec.LOW_NOT_NEEDED),
        (rb"a{1}", 0, spec.LOW_NOT_NEEDED),
        (rb"a*", 0, spec.LOW_NOT_NEEDED),
        (rb"a{0,}", 0, spec.LOW_NOT_NEEDED),
        (rb"a{0}", 0, spec.LOW_NOT_NEEDED),
        # And what there is to rewrite.
        (rb"a+", 0, spec.LOW_LOWERED),
        (rb"a+?", 0, spec.LOW_LOWERED),
        (rb"a{2}", 0, spec.LOW_LOWERED),
        (rb"a{1,}", 0, spec.LOW_LOWERED),
        (rb"a{2,8}", 0, spec.LOW_LOWERED),
        (rb"a{0,2}", 0, spec.LOW_LOWERED),
        (EMAIL, 0, spec.LOW_LOWERED),
        # The two blockers, each on its own and both at once. A pattern can
        # hold both, and the column reports both rather than the first.
        (rb"(?:a?)*", spec.LB_NULLABLE, spec.LOW_NOT_NEEDED),
        (rb"(?:a?)+", spec.LB_NULLABLE, spec.LOW_BLOCKED),
        (rb"(?:a*)*", spec.LB_NULLABLE, spec.LOW_NOT_NEEDED),
        (rb"(?:a|)*", spec.LB_NULLABLE, spec.LOW_NOT_NEEDED),
        (rb"(?:^)*", spec.LB_NULLABLE, spec.LOW_NOT_NEEDED),
        (rb"\R", spec.LB_BSR, spec.LOW_NOT_NEEDED),
        (rb"a\Rb", spec.LB_BSR, spec.LOW_NOT_NEEDED),
        (rb"a+\R", spec.LB_BSR, spec.LOW_BLOCKED),
        (rb"(?:a?)+\R", spec.LB_NULLABLE | spec.LB_BSR, spec.LOW_BLOCKED),
        # A body nobody compiles holds nothing against the pattern: `{0}` emits
        # no instruction, so neither the \R nor the nullable star under it is
        # a blocker, and `pike_ok` never sees one either.
        (rb"(?:\R){0}a+", 0, spec.LOW_LOWERED),
        (rb"(?:(?:a?)*){0}a+", 0, spec.LOW_LOWERED),
        # A nullable body under a *finite* bound is not a blocker: the lowered
        # form has no star left for it to be the body of.
        (rb"(?:a?){1,3}", 0, spec.LOW_LOWERED),
    ],
)
def test_the_pre_check_finds_what_it_says_it_finds(
    pattern: bytes, blockers: int, decision: int
) -> None:
    found, decided, fits = plan(pattern)
    assert (found, decided) == (blockers, decision), pattern
    assert fits, pattern
    built = compiled(pattern)
    assert built.re.fields["blockers"] == blockers
    assert built.re.fields["lowdec"] == decision


def test_a_lowered_pattern_is_eligible_and_a_blocked_one_is_not() -> None:
    """The equivalence the census gates on, on the patterns that show it.

    The pre-check and `pike_ok` are two implementations of one judgment, at
    two levels, and they are never compared directly — they describe different
    programs. What is compared is this: a pattern the pre-check approved and
    the dry run cleared comes out eligible, and a pattern it refused does not.
    """
    for pattern in (rb"a+", rb"a{2,8}", rb"(?:a+){2}", rb"(?:a?){1,3}", EMAIL):
        assert ENGINE.pike_eligible(compiled(pattern)), pattern
    for pattern in (rb"(?:a?)+", rb"a+\R", rb"(?:a*)*", rb"\R"):
        assert not ENGINE.pike_eligible(compiled(pattern)), pattern


# --- the cap, and both sides of it ---


def _boundary(spelling: bytes) -> int:
    """The largest count whose lowered form still fits, per the dry run."""
    low, high = 1, spec.MAX_QUANT
    assert plan(spelling % low)[2]
    while low < high:
        mid = (low + high + 1) // 2
        if plan(spelling % mid)[2]:
            low = mid
        else:
            high = mid - 1
    return low


BOUNDARY_SPELLING = b"(?:a*){%d}"
"""What the repetition-table bisection walks: a copy carries a counter."""

FUEL_SPELLING = b"a{%d}"
"""And what the walk-fuel one walks.

A one-instruction body costs the code array one cell per copy and the code
generator two job visits — the copy and the repeat job's own — and the fuel is
twice the code array, so this reaches the fuel first. Which cap a family
reaches is a fact about the compiler rather than a choice; what the test does
is name it and then ask the dry run where it is."""


@pytest.mark.parametrize(
    "spelling,expected",
    [(BOUNDARY_SPELLING, spec.MAX_REPS), (FUEL_SPELLING, None)],
    ids=["repetition-table", "walk-fuel"],
)
def test_the_cap_boundary_is_where_the_dry_run_says_it_is(
    spelling: bytes, expected: int | None
) -> None:
    """Exactly at a cap is a fit, one past it is the fallback.

    Neither emitting side is compiled here. Laying out thousands of copies is
    tens of millions of steps of the reference interpreter, which is a Python
    limit rather than an engine one — the generated backends have no such
    budget — so what this asserts about the fitting side is the dry run's
    answer, and the pattern that is actually compiled below sits far enough
    inside the caps to be affordable.
    """
    edge = _boundary(spelling)
    if expected is not None:
        assert edge == expected, edge
    assert plan(spelling % edge) == (0, spec.LOW_LOWERED, True)
    assert plan(spelling % (edge + 1)) == (0, spec.LOW_CAPPED, False)


def test_the_two_families_stop_at_different_caps() -> None:
    """Which is what makes them two witnesses rather than one written twice."""
    assert _boundary(BOUNDARY_SPELLING) != _boundary(FUEL_SPELLING)


@pytest.mark.parametrize(
    "spelling,counters",
    [(BOUNDARY_SPELLING, 2), (FUEL_SPELLING, 1)],
    ids=["repetition-table", "walk-fuel"],
)
def test_a_candidate_over_the_cap_falls_back_rather_than_failing(
    spelling: bytes, counters: int
) -> None:
    """Oversize is a documented carve-out, never a compile error."""
    over = spelling % (_boundary(spelling) + 1)
    built = compiled(over)
    assert built.re.fields["lowdec"] == spec.LOW_CAPPED
    assert not built.re.fields["lowfits"]
    assert not built.re.fields["pike"]
    # One counter per quantifier the source spells and nothing copied: the
    # repetition-table family spells the count and a star, the fuel family
    # only the count.
    assert len(built.re.fields["reps"].inner.items) == counters


def test_two_quantifiers_that_fit_apart_and_not_together_stay_whole() -> None:
    """The witness for all-or-nothing.

    Either of these lowers on its own and both together overshoot MAX_REPS, so
    the pattern must come out whole in counter form — not half rewritten, and
    not PatternTooLarge.
    """
    half = spec.MAX_REPS * 3 // 4
    assert plan(BOUNDARY_SPELLING % half)[2]
    both = (BOUNDARY_SPELLING % half) * 2
    assert plan(both) == (0, spec.LOW_CAPPED, False)
    built = compiled(both)
    assert len(built.re.fields["reps"].inner.items) == 4
    assert not built.re.fields["pike"]


def test_a_lowering_well_inside_the_cap_is_emitted() -> None:
    """And the other side really does lay the copies out."""
    built = compiled(BOUNDARY_SPELLING % 400)
    assert built.re.fields["lowdec"] == spec.LOW_LOWERED
    assert built.re.fields["pike"]
    assert len(built.re.fields["reps"].inner.items) == 400


# --- the shape the lowering emits ---


def _ops(built: CompiledPattern) -> list[str]:
    from pcrevera.engine.driver import items, variant_of

    return [variant_of(one.fields["op"]) for one in items(built.re.fields["code"])]


def test_the_lowered_shapes_are_the_ones_the_design_names() -> None:
    """x+ -> x x*, x{m,} -> m copies then a star, x{m,n} -> m copies then
    nested optionals. Read off the opcodes rather than off a description."""
    assert _ops(compiled(rb"a+")) == [
        "OpChar", "OpRepZero", "OpRepLoop", "OpRepEnter", "OpChar",
        "OpRepNext", "OpAccept",
    ]
    assert _ops(compiled(rb"a{2,}")) == [
        "OpChar", "OpChar", "OpRepZero", "OpRepLoop", "OpRepEnter", "OpChar",
        "OpRepNext", "OpAccept",
    ]
    assert _ops(compiled(rb"a{2,4}")) == [
        "OpChar", "OpChar", "OpSplit", "OpChar", "OpSplit", "OpChar",
        "OpAccept",
    ]
    assert _ops(compiled(rb"a{3}")) == ["OpChar"] * 3 + ["OpAccept"]


def test_the_generated_optionals_nest_the_way_the_count_prefers() -> None:
    """Every optional exits at the same instruction, and the greedy arm order
    is the body first — which is what makes the k-th copy's presence decided
    before the (k+1)-th's."""
    from pcrevera.engine.driver import items

    for pattern, greedy in ((rb"a{1,3}", True), (rb"a{1,3}?", False)):
        code = list(items(compiled(pattern).re.fields["code"]))
        stop = len(code) - 1  # the trailing Accept
        for at, inst in enumerate(code):
            from pcrevera.engine.driver import variant_of

            if variant_of(inst.fields["op"]) != "OpSplit":
                continue
            arms = (inst.fields["arg"], inst.fields["alt"])
            assert arms == ((at + 1, stop) if greedy else (stop, at + 1)), pattern


def test_a_repeated_group_is_still_one_group() -> None:
    """Every copy saves into the original slots, so the ovector is unchanged in
    width and a later copy overwrites what an earlier one wrote."""
    built = compiled(rb"(a){3}")
    assert built.captures == 1
    got = ENGINE.match_compiled(built, b"aaa")
    assert got.ovector == (0, 3, 2, 3)


def test_a_skipped_copy_leaves_the_previous_capture_alone() -> None:
    built = compiled(rb"(a){1,3}b")
    got = ENGINE.match_compiled(built, b"aab")
    assert got.ovector == (0, 3, 1, 2)


def test_an_unselected_arm_of_a_copied_alternation_stays_unset() -> None:
    built = compiled(rb"(?:(a)|(b)){1,2}")
    got = ENGINE.match_compiled(built, b"a")
    assert got.ovector == (0, 1, 0, 1, -1, -1)


# --- the named regression ---


def test_the_motivating_pattern_classifies_linear() -> None:
    """PLAN-POST-M6.md exists because this pattern did not.

    The interval is the one the plan set from the hand-lowered measurement
    before the lowering existed — cost below a million, stack exactly zero,
    memory below a hundred thousand — and the exact numbers are what the
    frozen implementation answers inside it.
    """
    built = compiled(EMAIL)
    assert ENGINE.complexity_class(built) == (spec.OK, spec.CLASS_LINEAR)
    answers = {
        kind: ENGINE.worst_case(built, kind, 1000) for kind in ("cost", "stack", "mem")
    }
    assert answers["cost"][0] == spec.OK and answers["cost"][1] < 1_000_000
    assert answers["stack"] == (spec.OK, 0)
    assert answers["mem"][0] == spec.OK and answers["mem"][1] < 100_000
    assert answers == {
        "cost": (spec.OK, 201_330),
        "stack": (spec.OK, 0),
        "mem": (spec.OK, 12_115),
    }


def test_the_named_facts_the_census_says_must_survive() -> None:
    """Three patterns the plan says the fix must leave exactly where they are."""
    bare = compiled(rb"\R")
    assert ENGINE.complexity_class(bare) == (spec.OK, spec.CLASS_LINEAR)
    assert not ENGINE.pike_eligible(bare)

    reached = compiled(rb"a+\R")
    assert ENGINE.complexity_class(reached) == (
        spec.OK,
        spec.CLASS_NOT_PROVEN_LINEAR,
    )
    assert ENGINE.worst_case(reached, "cost", 1000) == (spec.OK, 16_253_893)

    nested = compiled(rb"(?:a*)*")
    assert ENGINE.complexity_class(nested)[0] == spec.EXCEEDS_BUDGET
