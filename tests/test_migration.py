"""The migration report, and the census PLAN-POST-M6.md reads off it.

Generating the report is most of the check: every row is written only after the
compiler's recorded decision has been reproduced from the parsed tree, after
`pike_ok` has agreed with a lowering, and after the counter form left behind by
a decline has been found to show the blockers the pre-check named. What is here
is the rest — the committed file is current, and the four statements the plan
makes about the whole population hold over it.
"""

from __future__ import annotations

import json

import pytest

from pcrevera.engine import migration, spec

COMMITTED = migration.load()
ROWS = COMMITTED["rows"]


def test_the_committed_report_is_what_the_generator_produces() -> None:
    assert json.loads(migration.corpus_text()) == COMMITTED


def test_every_backtracking_pattern_names_a_blocker_or_the_cap() -> None:
    """Which is the whole content of the carve-out list: a pattern is off the
    lockstep path for one of three reasons, and it says which."""
    unexplained = [
        row["pattern"]
        for row in ROWS
        if not row["pike"]
        and not row["blockers"]
        and row["lowering"] != "declined (cap)"
    ]
    assert not unexplained, unexplained[:10]


def test_nothing_was_lowered_and_then_refused() -> None:
    """The set the plan says must be empty. A lowering `pike_ok` went on to
    refuse would mean the pre-check approved something it should not have."""
    refused = [row["pattern"] for row in ROWS if row["lowering"] == "lowered" and not row["pike"]]
    assert not refused, refused[:10]


def test_no_pattern_makes_the_analyzer_answer_arshape() -> None:
    """ArShape is the two halves of BOUNDS.md disagreeing about one program,
    which no pattern can legitimately cause."""
    assert not [row["pattern"] for row in ROWS if row["analysis"] == "ArShape"]


def test_every_migration_to_the_lockstep_path_names_the_lowering() -> None:
    """A pattern that ended up eligible after a rewrite got there by being
    lowered, and the column says so rather than leaving it to be inferred."""
    for row in ROWS:
        if row["pike"] and row["lowering"] == "declined (cap)":
            pytest.fail(f"{row['pattern']}: eligible after declining to lower")


def test_every_lowered_pattern_is_a_migration_to_linear() -> None:
    """The census's first gate, from the side the report can see it.

    A migration to linear names `lowered` in its lowering column, and the
    report's own contribution to that is the converse: nothing was lowered and
    left behind. Every lowered pattern is on the lockstep path, carries the
    lockstep certificate and claims the linear class — so the lowering column
    and the class column say the same thing about the same patterns, and a
    migration that named anything else would show up as one of these three
    failing rather than as a number nobody recomputed.
    """
    for row in ROWS:
        if row["lowering"] != "lowered":
            continue
        assert row["pike"], row["pattern"]
        assert row["certificate"]["config"] == "CfgPike", row["pattern"]
        assert row["certificate"]["class"] == spec.CLASS_LINEAR, row["pattern"]


def test_every_pattern_short_of_linear_names_why() -> None:
    """The census's second gate, over the whole population.

    Every remaining notProvenLinear or ExceedsBudget names its blockers or its
    cap decision. Both refusals are here — a class of zero and a certificate
    the pattern does not carry at all — because the plan asks the same question
    of both and the accessors report them differently.
    """
    unexplained = [
        row["pattern"]
        for row in ROWS
        if row["certificate"]["class"] != spec.CLASS_LINEAR
        and not row["blockers"]
        and row["lowering"] != "declined (cap)"
    ]
    assert not unexplained, unexplained[:10]


def test_the_counts_are_the_rows_they_summarize() -> None:
    """The census is read off the columns, so it cannot be written beside
    them: a header that drifted from its own rows would be the one number a
    reader trusts and nobody checks."""
    counts = COMMITTED["counts"]
    assert counts["patterns"] == len(ROWS)
    assert counts["lockstep"] == sum(1 for row in ROWS if row["pike"])
    assert counts["linear"] == sum(
        1 for row in ROWS if row["certificate"]["class"] == spec.CLASS_LINEAR
    )
    assert counts["no-certificate"] == sum(
        1 for row in ROWS if row["certificate"]["config"] is None
    )
    for name in ("lowered", "not needed", "declined (blockers)", "declined (cap)"):
        assert counts[f"lowering: {name}"] == sum(
            1 for row in ROWS if row["lowering"] == name
        )


def test_the_report_carries_the_patterns_the_plan_names() -> None:
    """The three facts the census says must survive the fix, read off the
    report's own columns rather than measured again."""
    by_pattern = {
        (row["pattern"], tuple(row["options"])): row
        for row in ROWS
    }

    email = by_pattern[(rb"(?<user>\w+)@(?<host>[\w.]+)".hex(), ())]
    assert email["lowering"] == "lowered"
    assert email["pike"] and email["certificate"]["class"] == spec.CLASS_LINEAR

    bare = by_pattern[(rb"\R".hex(), ())]
    assert bare["blockers"] == ["bsr"] and not bare["pike"]
    assert bare["certificate"]["class"] == spec.CLASS_LINEAR

    reached = by_pattern[(rb"a+\R".hex(), ())]
    assert reached["blockers"] == ["bsr"]
    assert reached["lowering"] == "declined (blockers)"
    assert reached["certificate"]["class"] == spec.CLASS_NOT_PROVEN_LINEAR

    nested = by_pattern[(rb"(?:a*)*".hex(), ())]
    assert nested["blockers"] == ["nullable"]
    assert nested["certificate"]["config"] is None
    assert nested["accessors"]["cost"] is None
