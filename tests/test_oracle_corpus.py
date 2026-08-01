"""The seed corpus, case by case, against the pinned build.

Until the engine exists these cases only say what pcre2 does. That is already
worth having: it is the shape every later differential test takes, and it turns
a pcre2 upgrade into a list of named behavior changes instead of a surprise.
"""

from __future__ import annotations

import json

import pytest

from pcretruste.oracle import corpus as corpus_module

CORPUS = corpus_module.load()


@pytest.mark.parametrize("case", CORPUS.cases, ids=lambda case: case.name)
def test_oracle_agrees_with_the_corpus(oracle, case):
    failures = corpus_module.check(oracle, corpus_module.Corpus(CORPUS.path, (case,)))
    assert not failures, failures[0][1]


def test_oracle_corpus_covers_the_wave_one_ground():
    """A corpus that quietly lost half its cases would still pass every case."""
    assert len(CORPUS.cases) >= 100
    names = {case.name for case in CORPUS.cases}
    for expected in (
        "literal-found",
        "quantifier-greedy-star",
        "capture-unset-group-is-minus-one",
        "tables-caseless-does-not-fold-high-bytes",
        "cerror-missing-closing-paren",
        "start-offset-past-end",
        "varlookbehind-over-the-build-limit",
    ):
        assert expected in names


def _write_corpus(tmp_path, case):
    path = tmp_path / "corpus.json"
    path.write_text(json.dumps({"schema": 1, "cases": [case]}))
    return path


def test_oracle_corpus_requires_a_subject_for_a_matching_case(tmp_path):
    """A missing subject would quietly become the empty one and test nothing."""
    path = _write_corpus(tmp_path, {"name": "x", "pattern": "a", "expect": {"match": [0, 1]}})
    with pytest.raises(ValueError, match="subject"):
        corpus_module.load(path)


def test_oracle_corpus_accepts_an_empty_subject_written_out(tmp_path):
    path = _write_corpus(
        tmp_path, {"name": "x", "pattern": "a", "subject": "", "expect": "nomatch"}
    )
    assert corpus_module.load(path).cases[0].subject == b""


def test_oracle_corpus_refuses_a_subject_on_a_compile_only_case(tmp_path):
    path = _write_corpus(
        tmp_path,
        {"name": "x", "pattern": "a", "subject": "a", "expect": {"compiled": {"captures": 0}}},
    )
    with pytest.raises(ValueError, match="no subject"):
        corpus_module.load(path)


def test_oracle_corpus_refuses_a_duplicate_case_name(tmp_path):
    path = tmp_path / "corpus.json"
    case = {"name": "x", "pattern": "a", "subject": "a", "expect": {"match": [0, 1]}}
    path.write_text(json.dumps({"schema": 1, "cases": [case, case]}))
    with pytest.raises(ValueError, match="duplicate"):
        corpus_module.load(path)


def test_oracle_corpus_refuses_a_pattern_written_twice(tmp_path):
    path = _write_corpus(
        tmp_path,
        {"name": "x", "pattern": "a", "pattern_hex": "61", "subject": "a", "expect": "nomatch"},
    )
    with pytest.raises(ValueError):
        corpus_module.load(path)


@pytest.mark.parametrize(
    "case",
    [
        {"name": "x", "pattern": 61, "subject": "a", "expect": "nomatch"},
        {"name": "x", "pattern_hex": 61, "subject": "a", "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": None, "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": "a", "options": "CASELESS", "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": "a", "options": [1], "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": "a", "newline": 2, "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": "a", "start": "1", "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": "a", "start": -1, "expect": "nomatch"},
    ],
)
def test_oracle_corpus_refuses_a_field_of_the_wrong_type(tmp_path, case):
    """`"pattern": 61` would otherwise become the two bytes "61" and test nothing."""
    with pytest.raises(ValueError):
        corpus_module.load(_write_corpus(tmp_path, case))


def test_oracle_corpus_refuses_a_field_nothing_reads(tmp_path):
    """A misspelled option list would otherwise be dropped without a word."""
    case = {
        "name": "x",
        "pattern": "a",
        "subject": "A",
        "match_option": ["NOTBOL"],
        "expect": "nomatch",
    }
    with pytest.raises(ValueError, match="match_option"):
        corpus_module.load(_write_corpus(tmp_path, case))


@pytest.mark.parametrize(
    "expect",
    [
        {"match": ["0", 1]},
        {"cerror": {"code": "114", "offset": 2}},
        {"merror": "-33"},
        {"compiled": {"captures": "1"}},
    ],
)
def test_oracle_corpus_refuses_an_expectation_of_the_wrong_type(tmp_path, expect):
    case = {"name": "x", "pattern": "a", "subject": "a", "expect": expect}
    if "compiled" in expect:
        del case["subject"]
    with pytest.raises(ValueError, match="must be a number"):
        corpus_module.load(_write_corpus(tmp_path, case))


@pytest.mark.parametrize("schema", [True, 1.0, "1", 2])
def test_oracle_corpus_schema_must_be_the_exact_number(tmp_path, schema):
    """`true` and `1.0` both equal 1 in Python, and neither is a schema."""
    path = tmp_path / "corpus.json"
    path.write_text(json.dumps({"schema": schema, "cases": []}))
    with pytest.raises(ValueError, match="schema"):
        corpus_module.load(path)


@pytest.mark.parametrize("document", [[], "cases", {"schema": 1}, {"schema": 1, "cases": {}}])
def test_oracle_corpus_must_be_a_document_of_cases(tmp_path, document):
    path = tmp_path / "corpus.json"
    path.write_text(json.dumps(document))
    with pytest.raises(ValueError):
        corpus_module.load(path)


@pytest.mark.parametrize(
    "expect",
    [
        {"cerror": 114},
        {"cerror": [114, 2]},
        {"cerror": {"code": 114}},
        {"cerror": {"code": 114, "offset": 2, "text": "boom"}},
        {"compiled": 1},
        {"compiled": {}},
        {"compiled": {"captures": 1, "names": []}},
        {"compiled": {"captures": 1, "groups": {}}},
        {"compiled": {"captures": 1, "names": {"x": "1"}}},
    ],
)
def test_oracle_corpus_refuses_a_malformed_expectation(tmp_path, expect):
    """A malformed expectation must be a ValueError, not a TypeError from inside."""
    case = {"name": "x", "pattern": "a", "expect": expect}
    if "compiled" not in expect:
        case["subject"] = "a"
    with pytest.raises(ValueError):
        corpus_module.load(_write_corpus(tmp_path, case))


@pytest.mark.parametrize(
    "case",
    [
        {"pattern": "a", "subject": "a", "expect": "nomatch"},
        {"name": "x", "pattern": "a", "subject": "a"},
        {},
    ],
    ids=["no-name", "no-expect", "empty"],
)
def test_oracle_corpus_refuses_a_case_missing_what_it_needs(tmp_path, case):
    """A missing field must name itself, not surface as a KeyError traceback."""
    with pytest.raises(ValueError, match="missing"):
        corpus_module.load(_write_corpus(tmp_path, case))


def test_oracle_corpus_names_the_case_it_is_complaining_about(tmp_path):
    case = {"name": "the-one-with-the-typo", "pattern": "a", "subject": "a", "expect": "nomatch"}
    case["match_option"] = ["NOTBOL"]
    with pytest.raises(ValueError, match="the-one-with-the-typo"):
        corpus_module.load(_write_corpus(tmp_path, case))
