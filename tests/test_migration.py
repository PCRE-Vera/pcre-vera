"""The migration report, and the census PLAN-POST-M6.md reads off it.

Generating the report is most of the check: every row is written only after the
compiler's recorded decision has been reproduced from the parsed tree, after
`pike_ok` has agreed with a lowering, and after the counter form left behind by
a decline has been found to show the blockers the pre-check named. What is here
is the rest — the committed file is current, and the statements the plan makes
about the whole population hold over it.

The other half of the census is a comparison between two versions of the
engine, and a report holds one. The engine without the lowering cannot be
rebuilt from this checkout, so what it said about the same 334 patterns was
measured once and committed as `oracle/corpus/pre-lowering.json`; the join
below is what turns "the class does not regress" from a sentence in the LOG
into something that fails a run. It is a recorded measurement and says so, but
the comparison over it is not: it is recomputed from the report every time,
and the report is generated.

A recording nobody can take again is worth saying something about. Most of
this one is not taken on trust: the lowering left 218 of the 334 patterns
alone, and for those the program has not changed a byte, so the engine here
answers what the recording says it answered and a test asks it to. What
remains unwitnessed is the 116 patterns that were rewritten, which is exactly
the set the census is about, and no arrangement of files can fix that — the
comparison is against an engine that is gone.
"""

from __future__ import annotations

import json
import subprocess

import pytest

from pcrevera.engine import migration, spec
from pcrevera.paths import REPO_ROOT

GENERATED = json.loads(migration.corpus_text())
"""Every pattern compiled again here rather than read out of the file.

The census is a statement about the engine, so the file is the thing that has
to keep up with it and not the other way round: everything below reads the
generated report, and one test holds the committed copy to it."""

COMMITTED = migration.load()
ROWS = GENERATED["rows"]

BEFORE = {migration.key(row): row for row in migration.before()["rows"]}
AFTER = {migration.key(row): row for row in ROWS}


def claimed(row: dict) -> int:
    return migration.CLASS_ORDER[row["certificate"]["class"]]


def test_the_committed_report_is_what_the_generator_produces() -> None:
    assert COMMITTED == GENERATED


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


def test_a_pattern_that_declined_for_size_is_not_eligible() -> None:
    """Because declining over a cap means the counted form was emitted, and
    `pike_ok` refuses a repetition that is not a pure star. An eligible pattern
    in that column would mean the fallback emitted something other than the
    fallback. What the counted form really looks like is two patterns' worth of
    opcodes in `tests/test_lowering.py`; what is here is the column."""
    for row in ROWS:
        if row["pike"] and row["lowering"] == "declined (cap)":
            pytest.fail(f"{row['pattern']}: eligible after declining to lower")


def test_every_migration_to_the_lockstep_path_names_the_lowering() -> None:
    """The claim the plan makes about migrations, which needs both engines.

    A pattern that runs in lockstep now and did not before got there by being
    rewritten, and so did every pattern whose class improved. Nothing else can
    move either one: the rest of the compiler did not change, and the report's
    own column says which patterns the rewrite touched.
    """
    for key, was in BEFORE.items():
        now = AFTER[key]
        moved = now["pike"] and not was["pike"]
        promoted = claimed(now) > claimed(was)
        if moved or promoted:
            assert now["lowering"] == "lowered", key[0]


def test_every_lowered_pattern_ended_up_linear_and_in_lockstep() -> None:
    """What the report alone can say about the lowered patterns.

    Not that each one migrated — `a{2}` was linear on the backtracking matcher
    before anything was rewritten, and the join below is what tells a migration
    from a pattern that was already there. What is here is the converse:
    nothing was lowered and left behind. Every lowered pattern is on the
    lockstep path, carries the lockstep certificate and claims the linear
    class, so those three columns say the same thing about the same patterns.
    """
    for row in ROWS:
        if row["lowering"] != "lowered":
            continue
        assert row["pike"], row["pattern"]
        assert row["certificate"]["config"] == "CfgPike", row["pattern"]
        assert row["certificate"]["class"] == spec.CLASS_LINEAR, row["pattern"]


def test_the_recorded_measurement_still_names_the_same_patterns() -> None:
    """The join is only worth what it covers.

    Every pattern measured before the lowering is still in the report, so no
    row slipped out of the comparison by being renamed or dropped. The other
    direction is left open on purpose: a pattern added later has no
    pre-lowering answer and never will, since the engine that would give one is
    two versions back.
    """
    missing = [key[0] for key in BEFORE if key not in AFTER]
    assert not missing, missing[:10]
    assert len(BEFORE) == 334, "the census is stated over this many patterns"


def test_the_recording_still_answers_for_what_the_lowering_left_alone() -> None:
    """The part of the fixture that is not taken on trust.

    A pattern the lowering did not rewrite — nothing to lower, a blocker, or a
    candidate over a cap — compiles to the program it always compiled to, so
    every column the recording carries about it is a column this engine still
    produces. Two hundred and eighteen of the three hundred and thirty-four
    rows are checked that way, against a live compile rather than against the
    file beside them, which is what keeps a doctored baseline from quietly
    weakening the non-regression gate.

    The program column is the one that makes this literal: every field of the
    compiled pattern a matcher reads, hashed by the same rendering on both
    sides, so what is compared is the program rather than the three
    conclusions drawn from it.
    """
    checked = 0
    for key, was in BEFORE.items():
        now = AFTER[key]
        if now["lowering"] == "lowered":
            continue
        checked += 1
        assert was["program"] == now["program"], key[0]
        assert was["pike"] == now["pike"], key[0]
        assert was["certificate"] == now["certificate"], key[0]
        assert was["accessors"] == now["accessors"], key[0]
    assert checked == 218


def test_the_recording_names_a_commit_this_history_has() -> None:
    """The provenance line, held to something.

    The file says which engine answered, and a commit that no longer exists in
    this history would make that unfollowable. It is the weakest of the checks
    here on purpose: what it establishes is that the recipe in the LOG can be
    run again, not that it was.
    """
    commit = migration.before()["commit"]
    try:
        done = subprocess.run(
            ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
            cwd=REPO_ROOT,
            capture_output=True,
        )
    except OSError:
        pytest.skip("no git here to resolve the commit with")
    if done.returncode != 0:
        pytest.skip("this checkout does not carry the history the recording names")
    assert (
        subprocess.run(
            ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
            cwd=REPO_ROOT,
            capture_output=True,
        ).returncode
        == 0
    ), f"{commit[:7]} is not behind HEAD, so it is not the engine that came before"


def test_no_pattern_lost_ground_to_the_lowering() -> None:
    """The census's non-regression gate, which is the whole of what the plan
    asks mechanically for patterns that were already linear.

    Two ways to lose ground and both are refused: a pattern that ran in
    lockstep before and does not now, and a certificate that claims less than
    it used to. A rewrite that made a program the Pike VM would not take, or
    one the analyzer could no longer price, would show up here as the pattern
    that did it rather than as a count.
    """
    for key, was in BEFORE.items():
        now = AFTER[key]
        assert not (was["pike"] and not now["pike"]), key[0]
        assert claimed(now) >= claimed(was), key[0]


def test_the_census_numbers_are_the_ones_the_join_produces() -> None:
    """And the movements the documents report, recomputed from the two files.

    116 patterns moved onto the lockstep path and 46 improved their class, 39
    of them from notProvenLinear and 7 from carrying no certificate at all.
    The gap between the two numbers is the point of keeping them apart: most
    lowered patterns were linear already and stayed linear, so a test that
    called every lowering a migration would be counting something else.
    """
    lockstep = [
        key for key, was in BEFORE.items() if AFTER[key]["pike"] and not was["pike"]
    ]
    better = [key for key, was in BEFORE.items() if claimed(AFTER[key]) > claimed(was)]
    assert len(lockstep) == 116
    assert len(better) == 46
    assert sum(1 for key in better if BEFORE[key]["certificate"]["class"] is None) == 7
    assert (
        sum(
            1
            for key in better
            if BEFORE[key]["certificate"]["class"] == spec.CLASS_NOT_PROVEN_LINEAR
        )
        == 39
    )


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
