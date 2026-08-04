"""The differential sweep harness, and the shard it commits.

Three kinds of question. The harness itself — a case is a function of its two
numbers, a manifest survives being written down, the reducer really reduces —
which needs neither pcre2 nor much time. The committed shard, replayed through
the Python interpreter and then through pcre2, which is the same file the Go
and JavaScript runners replay through their own generated engines. And a small
generated campaign against pcre2 on a population the shard does not contain, so
that the harness is exercised on cases nobody has ever recorded an answer for.

The campaign at the scale DESIGN.md section 8 asks for is not here and is not
meant to be: it is `python -m pcrevera.sweep run`, and what it found is in the
LOG. What is here is sized to be run on every commit.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from pcrevera.engine import spec
from pcrevera.engine.driver import (
    Compiled,
    CompileError,
    Engine,
    Match,
    NoMatch,
)
from pcrevera.oracle import corpus as wave1
from pcrevera.oracle.corpus import CompiledExpectation, MatchExpectation
from pcrevera.sweep import campaign, checks, draw, gate, manifest, promote, reduce, shard
from pcrevera.sweep.population import CONVENTIONS, CROSS, OPTION_SETS, Case, Trial
from pcrevera.sweep.population import case as one_case
from pcrevera.sweep.population import population

ENGINE = Engine()


class Contrary:
    """An oracle that answers something else, whatever it is asked.

    A working engine agrees with pcre2 everywhere, which is the difficulty in
    testing what happens when it does not: this is the disagreement, planted.
    """

    def compile(self, *args, **kwargs):
        return checks.NoMatch()

    def match(self, *args, **kwargs):
        return checks.NoMatch()


SHARD = shard.load()

SMOKE_SEED = shard.SEED + 1


@pytest.fixture(scope="module")
def replayed() -> campaign.Report:
    """The committed shard, run again through the Python interpreter."""
    return campaign.run(manifest.read(shard.document()), engine=ENGINE)


@pytest.mark.parametrize("bound", [1, 2, 3, 4, 5, 7, 8, 10, 32, 100, 12345, (1 << 32) + 1])
def test_a_draw_folds_every_residue_the_same_number_of_times(bound: int):
    """The rejection rule, as the equation rather than as a histogram.

    The tail a draw throws away has to be counted over the whole sample space,
    and an off-by-one there makes residue zero one draw more likely than the
    rest — a bias no sweep would ever notice and the docstring would still be
    claiming was not there.
    """
    limit = draw.accepted(bound)
    assert limit % bound == 0
    assert 0 <= draw.SPAN - limit < bound
    assert draw.Draw("a").below(bound) < bound


def test_a_case_is_a_function_of_the_four_numbers_that_name_it():
    """Seed, index, subject count and where the structured population ends.

    The last two are the ones easy to forget, and forgetting them is how a
    replay command comes to rebuild a different case than the one that failed.
    """
    assert one_case(11, 7) == one_case(11, 7)
    assert one_case(11, 7) != one_case(12, 7)
    assert one_case(11, 7) != one_case(11, 8)
    assert one_case(11, 7, subjects=8) != one_case(11, 7, subjects=9)
    assert one_case(11, 500, structured=600) != one_case(11, 500, structured=500)


def test_the_population_crosses_every_option_family_with_every_convention():
    """By construction rather than by luck, which is what the two moduli are
    for: the completion gate asks for every family and every pair, and a sweep
    that had to draw them would sometimes not.

    The prefix is the claim, not the total. Eleven option families by six
    convention pairs is sixty-six cases, each combination exactly once, so a
    population of that size already crosses them and every case after it is
    another pass over the same cycle.
    """
    wanted = [
        (options, convention) for convention in CONVENTIONS for options in OPTION_SETS
    ]
    opening = population(1, structured=len(CROSS), hostile=0, subjects=1)[: len(wanted)]
    assert [(one.options, (one.newline, one.bsr)) for one in opening] == wanted


def test_every_case_can_be_asked_about_the_subjects_it_carries():
    for one in population(3, structured=len(CROSS), hostile=20, subjects=8, stride=13):
        assert one.maxlen == max(len(trial.subject) for trial in one.trials)
        for trial in one.trials:
            assert 0 <= trial.start <= len(trial.subject)


def test_a_manifest_survives_being_written_down():
    built = manifest.build(5, structured=len(CROSS), hostile=4, subjects=4, stride=9)
    held = manifest.read(built)
    assert held.cases == population(
        5, structured=len(CROSS), hostile=4, subjects=4, stride=9
    )
    assert held.digest == manifest.digest(built)
    assert manifest.text(manifest.document(5, held.cases, **held.shape)) == manifest.text(built)


def test_the_committed_shard_names_the_manifest_it_came_from():
    assert SHARD["manifest"] == manifest.digest(shard.document())
    assert SHARD["seed"] == shard.SEED
    assert SHARD["stride"] == shard.STRIDE


def test_the_committed_shard_is_what_this_engine_answers(replayed: campaign.Report):
    """The Python runner of the shard, which is the Go and JavaScript runners'
    question asked in the language the file was written in."""
    assert not replayed.findings, "\n".join(str(one) for one in replayed.findings[:10])
    assert replayed.records == SHARD["cases"]


def test_the_committed_shard_covers_what_it_was_sliced_for(replayed: campaign.Report):
    """A shard is a smoke test rather than a campaign, so what it has to cover
    is the machinery: both matchers selected, certified and unpriced patterns,
    compiles and syntax errors, and every kind of check except the oracle's,
    which is the next test's."""
    for group, name in (
        ("selection", "pike"),
        ("selection", "backtrack"),
        ("certified", "backtrack:certified"),
        ("certified", "pike:unpriced"),
        ("cases", "compiled"),
        ("cases", "syntax"),
        ("checks", "bound"),
        ("checks", "edge"),
        ("checks", "cross-matcher"),
        ("checks", "context"),
        ("checks", "context-edge"),
    ):
        assert getattr(replayed.coverage, group)[name], f"{group}: {name}"


def test_the_committed_shard_agrees_with_pcre2(oracle):
    """The other half of the chain, asked of the file rather than of a rerun.

    The test above establishes that the file is what this engine answers; what
    is left is whether those answers are pcre2's. So this asks pcre2 about the
    recorded cases and compares with what the file recorded — which is exactly
    what the Go and JavaScript runners do, minus the engine, and costs the
    pcre2 calls rather than a third pass through the interpreter.
    """
    asked = 0
    for one in SHARD["cases"]:
        case = manifest.decode(one)
        shared = {
            "options": case.options,
            "newline": case.newline,
            "bsr": case.bsr,
        }
        compiled = one["compile"]
        if compiled["kind"] == "declined":
            # The oracle policy of DESIGN.md section 1: pcre2 has no opinion
            # about a construct outside the claimed subset.
            continue
        asked += 1
        assert checks.agrees(_recorded_compile(compiled), oracle.compile(case.pattern, **shared))
        for trial, row in zip(case.trials, one["trials"]):
            if row["outcome"] not in (spec.MATCHED, spec.NO_MATCH):
                continue
            asked += 1
            answered = oracle.match(
                case.pattern,
                trial.subject,
                start=trial.start,
                match_options=trial.match_options,
                **shared,
            )
            assert checks.agrees(_recorded_match(row), answered), one["index"]
    assert asked > 300


def _recorded_compile(compiled: dict):
    """The compile outcome the shard records, as the driver would answer it."""
    if compiled["kind"] == "compileError":
        return CompileError(compiled["code"], compiled["offset"], "")
    return Compiled(
        capture_count=compiled["captures"],
        names=tuple(
            sorted((bytes.fromhex(name), number) for name, number in compiled["names"].items())
        ),
    )


def _recorded_match(row: dict):
    """And the match outcome, the same way."""
    if row["outcome"] == spec.NO_MATCH:
        return NoMatch()
    return Match(ovector=tuple(row["ovector"]))


def test_a_generated_campaign_agrees_with_pcre2(oracle):
    """The smoke-sized campaign: the same generator, a population the committed
    shard does not hold, and every check the campaign runs."""
    built = manifest.read(
        manifest.build(SMOKE_SEED, structured=len(CROSS), hostile=40, subjects=8, stride=11)
    )
    report = campaign.run(built, engine=ENGINE, oracle=oracle)
    assert not report.findings, "\n".join(str(one) for one in report.findings[:10])
    assert report.coverage.checks["oracle"] > 300
    assert report.coverage.checks["bound"] > 300


def test_the_gate_asks_for_everything_the_sweep_can_count():
    """Every name the gate requires is a name some counter can hold, which a
    typo in either list would break."""
    coverage = checks.Coverage()
    assert set(gate.wanted()) <= set(vars(coverage))
    assert gate.missing(coverage) == [
        f"{group}: {name}" for group, names in gate.wanted().items() for name in names
    ]


def test_a_minimized_case_can_be_promoted_into_the_corpus(oracle, tmp_path):
    """The last step of the failure loop, run on cases that never failed: what
    lands in the corpus is pcre2's own answer, the file still loads, and
    everything that was already in it is still there."""
    path = tmp_path / "wave1.json"
    path.write_text(wave1.WAVE1_PATH.read_text())
    before = wave1.load(path).cases
    matching = Case(
        seed=1, index=2, family="grammar", pattern=b"a(b)*c", options=("CASELESS",),
        newline="CRLF", bsr="UNICODE",
        trials=(Trial(subject=b"xABBc", match_options=(), start=1),), maxlen=5,
    )
    compiling = Case(
        seed=1, index=3, family="grammar", pattern=b"(?<n>a)|b", options=(),
        newline="LF", bsr="UNICODE", trials=(), maxlen=0,
    )
    names = promote.promote(
        oracle,
        [
            (matching, "match", "sweep-1-2", "a match"),
            (compiling, "compile", "sweep-1-3", "a compile"),
        ],
        path=path,
    )
    assert names["wave1"] == ["sweep-1-2", "sweep-1-3"]
    after = wave1.load(path).cases
    assert after[: len(before)] == before
    assert after[-2].expect == MatchExpectation((1, 5, 3, 4))
    assert after[-2].options == ("CASELESS",) and after[-2].newline == "CRLF"
    assert after[-1].expect == CompiledExpectation(captures=1, names=((b"n", 1),))
    assert after[-1].subject is None


def test_a_kept_regression_is_replayed_under_the_limits_that_found_it():
    """Every runner takes a regression's budget from the regression, since the
    document it is riding in was run under a different one."""
    for one, entry in zip(SHARD["regressions"], promote.regressions()):
        assert one["budget"] == entry["budget"]


def test_the_committed_shard_replays_the_kept_regressions():
    """The cases the sweep really found, replayed through the same battery.

    They are kept rather than generated, so nothing about the population brings
    them back; what makes them a regression test is that the shard records
    their answers and all three runners replay them.
    """
    kept = promote.regressions()
    assert [one["name"] for one in SHARD["regressions"]] == [one["name"] for one in kept]
    assert shard.kept(ENGINE) == SHARD["regressions"]


def test_a_repository_with_no_regressions_yet_still_has_the_section(tmp_path):
    """Bootstrapping: before the sweep has found an invariant failure there is
    nothing to keep, and the shard has to be generatable and replayable all the
    same. The section is written empty rather than left out, since a runner has
    to be able to tell one it should have replayed from one nobody wrote."""
    assert shard.kept(ENGINE, tmp_path / "nothing.json") == []


def test_promotion_sends_each_class_to_the_corpus_that_checks_it(oracle, tmp_path):
    """A semantic disagreement is about the answer, so it goes where answers
    are pinned. Everything else is about an invariant no semantic corpus asks
    about, so it goes where the whole battery is replayed — putting a bound
    violation in wave 1 would be filing a regression that guards nothing."""
    first = tmp_path / "wave1.json"
    first.write_text(wave1.WAVE1_PATH.read_text())
    second = tmp_path / "kept.json"
    answered = Case(
        seed=1, index=2, family="grammar", pattern=b"a(b)*c", options=(), newline="LF",
        bsr="UNICODE", trials=(Trial(subject=b"xabbc", match_options=(), start=0),),
        maxlen=5,
    )
    priced = replace(answered, index=3, pattern=b"(a|b){2,}", maxlen=4)
    added = promote.promote(
        oracle,
        [
            (answered, "match", "sweep-1-2-match", "an answer"),
            (priced, "context", "sweep-1-3-context", "an invariant"),
        ],
        path=first,
        kept=second,
    )
    assert added == {"wave1": ["sweep-1-2-match"], "regressions": ["sweep-1-3-context"]}
    assert wave1.load(first).cases[-1].name == "sweep-1-2-match"
    held = promote.regressions(second)
    assert [one["name"] for one in held] == ["sweep-1-3-context"]
    assert manifest.decode(held[0]["case"]) == priced
    # The conditions are part of the regression: a case found only under a
    # custom limit stops guarding anything when it is replayed under another.
    assert held[0]["budget"] == manifest.DEFAULT_BUDGET
    assert held[0]["edges"] == checks.DEFAULT_EDGES


def test_a_compile_disagreement_reduces_to_a_case_with_no_subject(oracle):
    """The reducer's answer for a compile class has to be a compile case.

    One that kept a subject would be promoted as a match, and a match case says
    nothing about the compile the failure was about. What is left over is the
    smallest case the harness can still ask a question about: a shorter
    pattern, no options, and nothing else to shrink.
    """
    big = one_case(SMOKE_SEED, 300, subjects=8)
    small = reduce.minimize(
        big, "compile", engine=ENGINE, budget=manifest.DEFAULT_BUDGET,
        oracle=Contrary(), edges=0,
    )
    assert small.trials == ()
    assert len(small.pattern) <= len(big.pattern)
    assert not small.options
    written = promote.entry(oracle, small, "sweep-compile", "a compile")
    assert "subject_hex" not in written and "start" not in written


def test_a_name_the_corpus_already_has_is_refused(oracle, tmp_path):
    """A case can fail in more than one way, so two records can name the same
    case; the corpus refuses a duplicate name, and finding that out after the
    file has been rewritten would be finding it out too late."""
    path = tmp_path / "wave1.json"
    path.write_text(wave1.WAVE1_PATH.read_text())
    built = Case(
        seed=1, index=2, family="grammar", pattern=b"abc", options=(), newline="LF",
        bsr="UNICODE", trials=(Trial(subject=b"abc", match_options=(), start=0),),
        maxlen=3,
    )
    twice = [(built, "match", "sweep-1-2", "once"), (built, "match", "sweep-1-2", "twice")]
    with pytest.raises(ValueError, match="already has a case"):
        promote.promote(oracle, twice, path=path)
    assert path.read_text() == wave1.WAVE1_PATH.read_text()
    promote.promote(oracle, twice[:1], path=path)
    with pytest.raises(ValueError, match="already has a case"):
        promote.promote(oracle, twice[1:], path=path)


def test_a_case_whose_invariant_still_fails_is_not_promoted(oracle, tmp_path, monkeypatch):
    """The invariant classes are the reason promotion runs the whole battery:
    a bound violation or a context reservation survives any compile-and-match
    comparison, so a promotion that only asked pcre2 for the answer would file
    a red test as a green one.

    A working engine finds none of those, which is the difficulty in testing
    this at all — so the battery is made to report one, which is exactly the
    situation promotion has to refuse.
    """
    path = tmp_path / "kept.json"
    built = Case(
        seed=1, index=2, family="grammar", pattern=b"(a|b){2,}", options=(),
        newline="LF", bsr="UNICODE",
        trials=(Trial(subject=b"abab", match_options=(), start=0),), maxlen=4,
    )
    monkeypatch.setattr(
        promote,
        "run_case",
        lambda *args, **kwargs: checks.Outcome(
            None,
            (checks.Finding("bound", 2, "cost used 10, certified 9"),),
            checks.Coverage(),
        ),
    )
    with pytest.raises(ValueError, match="still fails"):
        promote.promote(
            oracle, [(built, "context", "sweep-1-2-context", "a note")], kept=path
        )
    assert not path.exists()


def test_a_case_that_still_disagrees_is_not_promoted(oracle, tmp_path):
    """A red case belongs in a failure record, not in the corpus. The oracle
    here is one that answers something else, which is what a case whose bug is
    not fixed yet looks like from the promoter's side."""

    path = tmp_path / "wave1.json"
    path.write_text(wave1.WAVE1_PATH.read_text())
    built = Case(
        seed=1, index=2, family="grammar", pattern=b"abc", options=(), newline="LF",
        bsr="UNICODE", trials=(Trial(subject=b"abc", match_options=(), start=0),),
        maxlen=3,
    )
    with pytest.raises(ValueError, match="still fails"):
        promote.promote(Contrary(), [(built, "match", "sweep-1-2", "a note")], path=path)
    assert path.read_text() == wave1.WAVE1_PATH.read_text()
