"""The differential corpus: cases in, agreement or a complaint out.

A case says what pcre2 is expected to do, and the runner says whether it did.
The expectations are hand-written from what PCRE is supposed to mean, not
recorded from a run, so a case that disagrees with the pinned build is either
a mistake of ours or a change in pcre2, and both are worth being told about.

Patterns and subjects are byte sequences. In JSON they are written as Latin-1
text, which keeps ASCII readable while still reaching every byte from 0 to 255;
``pattern_hex`` and ``subject_hex`` are there for cases where hex is clearer.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol

from ..paths import CORPUS_DIR
from .client import (
    CompileOutcome,
    Compiled,
    CompileError,
    Match,
    MatchError,
    MatchOutcome,
    NoMatch,
)

SCHEMA = 1

SEED_PATH = CORPUS_DIR / "seed.json"


@dataclass(frozen=True)
class MatchExpectation:
    ovector: tuple[int, ...]


@dataclass(frozen=True)
class NoMatchExpectation:
    pass


@dataclass(frozen=True)
class CompileErrorExpectation:
    code: int
    offset: int


@dataclass(frozen=True)
class MatchErrorExpectation:
    code: int


@dataclass(frozen=True)
class CompiledExpectation:
    captures: int
    names: tuple[tuple[bytes, int], ...] = ()


Expectation = (
    MatchExpectation
    | NoMatchExpectation
    | CompileErrorExpectation
    | MatchErrorExpectation
    | CompiledExpectation
)


@dataclass(frozen=True)
class Case:
    name: str
    pattern: bytes
    expect: Expectation
    subject: bytes | None = None
    options: tuple[str, ...] = ()
    match_options: tuple[str, ...] = ()
    newline: str | None = "LF"
    bsr: str | None = "UNICODE"
    start: int = 0
    note: str = ""

    @property
    def is_compile_only(self) -> bool:
        """A case with no subject asks the oracle to compile and stop there.

        Only the two outcomes that are settled before matching begins may leave
        the subject out: a successful compile, and a compile error. A compile
        error may also be written with a subject, which sends the case through
        the match path instead and checks that the error surfaces there too.
        """
        return self.subject is None


@dataclass(frozen=True)
class Corpus:
    path: Path
    cases: tuple[Case, ...] = ()


# A case says at least who it is and what it expects; everything else has a
# default. Closed in both directions, like every other schema here.
CASE_REQUIRED = frozenset({"name", "expect"})

CASE_OPTIONAL = frozenset(
    {
        "pattern",
        "pattern_hex",
        "subject",
        "subject_hex",
        "options",
        "match_options",
        "newline",
        "bsr",
        "start",
        "note",
    }
)

CASE_FIELDS = CASE_REQUIRED | CASE_OPTIONAL


def _label(entry: object, index: int) -> str:
    """How to refer to a case in a complaint, whether or not it has a name yet."""
    if isinstance(entry, dict) and isinstance(entry.get("name"), str):
        return f"case {entry['name']!r}"
    return f"case {index}"


def _text(entry: dict[str, object], key: str) -> str:
    """A JSON string, and only that: `61` must not quietly become `"61"`."""
    value = entry[key]
    if not isinstance(value, str):
        raise ValueError(f"{key} must be a string, got {value!r}")
    return value


def _int(value: object, what: str) -> int:
    """A JSON number, and only that: `"114"` is not an error code."""
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{what} must be a number, got {value!r}")
    return value


def _table(
    value: object, what: str, required: frozenset[str], optional: frozenset[str] = frozenset()
) -> dict[str, object]:
    """A JSON object with a closed set of keys, and nothing else.

    Without this a malformed expectation raises TypeError or AttributeError from
    somewhere inside the loader, which the CLI does not handle and which tells a
    corpus author nothing.
    """
    if not isinstance(value, dict):
        raise ValueError(f"{what} must be an object, got {value!r}")
    missing = [key for key in required if key not in value]
    if missing:
        raise ValueError(f"{what} is missing: {', '.join(missing)}")
    unknown = set(value) - required - optional
    if unknown:
        raise ValueError(f"{what} has fields nothing reads: {', '.join(sorted(unknown))}")
    return value


def _to_bytes(entry: dict[str, object], text_key: str, hex_key: str) -> bytes | None:
    if hex_key in entry:
        if text_key in entry:
            raise ValueError(f"case gives both {text_key} and {hex_key}")
        return bytes.fromhex(_text(entry, hex_key))
    if text_key in entry:
        return _text(entry, text_key).encode("latin-1")
    return None


def _names(entry: dict[str, object], key: str) -> tuple[str, ...]:
    value = entry.get(key, ())
    if isinstance(value, str) or not isinstance(value, (list, tuple)):
        raise ValueError(f"{key} must be a list of option names, got {value!r}")
    for name in value:
        if not isinstance(name, str):
            raise ValueError(f"{key} must hold option names, got {name!r}")
    return tuple(value)


def _start(entry: dict[str, object]) -> int:
    value = _int(entry.get("start", 0), "start")
    if value < 0:
        raise ValueError(f"start must be a byte index, got {value!r}")
    return value


def _convention(entry: dict[str, object], key: str, default: str) -> str | None:
    value = entry.get(key, default)
    if value is not None and not isinstance(value, str):
        raise ValueError(f"{key} must be a convention name or null, got {value!r}")
    return value


def _parse_expectation(raw: object) -> Expectation:
    if raw == "nomatch":
        return NoMatchExpectation()
    if not isinstance(raw, dict) or len(raw) != 1:
        raise ValueError(f"an expectation is 'nomatch' or a one-key object, got {raw!r}")

    (kind, value), = raw.items()
    if kind == "match":
        if not isinstance(value, list) or len(value) % 2 != 0 or not value:
            raise ValueError("a match expectation is a non-empty even list of offsets")
        return MatchExpectation(tuple(_int(offset, "an offset") for offset in value))
    if kind == "cerror":
        table = _table(value, "a cerror expectation", frozenset({"code", "offset"}))
        return CompileErrorExpectation(
            code=_int(table["code"], "an error code"),
            offset=_int(table["offset"], "an error offset"),
        )
    if kind == "merror":
        return MatchErrorExpectation(code=_int(value, "an error code"))
    if kind == "compiled":
        table = _table(
            value, "a compiled expectation", frozenset({"captures"}), frozenset({"names"})
        )
        # Group names are an open map from name to number, so only the shape
        # and the values can be checked, not the keys.
        names = table.get("names", {})
        if not isinstance(names, dict):
            raise ValueError(f"group names must be an object, got {names!r}")
        return CompiledExpectation(
            captures=_int(table["captures"], "a capture count"),
            names=tuple(
                sorted(
                    (name.encode("latin-1"), _int(number, "a group number"))
                    for name, number in names.items()
                )
            ),
        )
    raise ValueError(f"unknown expectation kind: {kind!r}")


def load(path: Path = SEED_PATH) -> Corpus:
    document = json.loads(path.read_text())
    if not isinstance(document, dict):
        raise ValueError(f"a corpus is an object, got {document!r}")
    # Not `!= SCHEMA`: in Python `True` and `1.0` both equal 1, and neither is
    # a schema number. Same trap as the pin, same answer.
    schema = document.get("schema")
    if type(schema) is not int or schema != SCHEMA:
        raise ValueError(f"corpus schema {schema!r} is not {SCHEMA}")
    if not isinstance(document.get("cases"), list):
        raise ValueError("a corpus has a list of cases")

    cases = []
    seen: set[str] = set()
    for index, entry in enumerate(document["cases"]):
        # A misspelled field would otherwise be dropped in silence, and the case
        # would go on passing while testing something else entirely.
        _table(entry, _label(entry, index), CASE_REQUIRED, CASE_OPTIONAL)
        name = _text(entry, "name")
        if name in seen:
            raise ValueError(f"duplicate case name: {name!r}")
        seen.add(name)

        pattern = _to_bytes(entry, "pattern", "pattern_hex")
        if pattern is None:
            raise ValueError(f"case {name!r} has no pattern")

        expect = _parse_expectation(entry["expect"])
        subject = _to_bytes(entry, "subject", "subject_hex")
        # An empty subject is written out, so that forgetting one is an error
        # rather than a case that quietly tests something else.
        if isinstance(expect, CompiledExpectation):
            if subject is not None:
                raise ValueError(f"case {name!r} only compiles, so it takes no subject")
        elif subject is None and not isinstance(expect, CompileErrorExpectation):
            raise ValueError(f"case {name!r} matches but has no subject")

        cases.append(
            Case(
                name=name,
                pattern=pattern,
                subject=subject,
                expect=expect,
                options=_names(entry, "options"),
                match_options=_names(entry, "match_options"),
                newline=_convention(entry, "newline", "LF"),
                bsr=_convention(entry, "bsr", "UNICODE"),
                start=_start(entry),
                note=str(entry.get("note", "")),
            )
        )
    return Corpus(path=path, cases=tuple(cases))


class Engine(Protocol):
    """What running the corpus needs of an implementation.

    pcre2 through the shim is the only one today; from M3 our own engine answers
    the same two questions, and the corpus runs against it unchanged.
    """

    def compile(self, pattern: bytes, **options: object) -> CompileOutcome: ...

    def match(self, pattern: bytes, subject: bytes, **options: object) -> MatchOutcome: ...


def run(engine: Engine, case: Case) -> CompileOutcome | MatchOutcome:
    """Ask an engine what it makes of one case."""
    if case.is_compile_only:
        return engine.compile(
            case.pattern,
            options=case.options,
            newline=case.newline,
            bsr=case.bsr,
        )
    assert case.subject is not None
    return engine.match(
        case.pattern,
        case.subject,
        start=case.start,
        options=case.options,
        match_options=case.match_options,
        newline=case.newline,
        bsr=case.bsr,
    )


def check(engine: Engine, corpus: Corpus) -> list[tuple[Case, str]]:
    """Run a whole corpus, and report every case the engine got wrong.

    A case's note travels with its complaint: it is usually the sentence that
    says what the case was pinning, which is exactly what a reader of the
    failure wants.
    """
    failures = []
    for case in corpus.cases:
        complaint = disagreement(case, run(engine, case))
        if complaint is not None:
            failures.append((case, f"{complaint} ({case.note})" if case.note else complaint))
    return failures


def disagreement(case: Case, outcome: CompileOutcome | MatchOutcome) -> str | None:
    """Describe how the outcome differs from the expectation, or None if it does not."""
    expect = case.expect

    if isinstance(expect, MatchExpectation):
        if not isinstance(outcome, Match):
            return f"expected a match at {list(expect.ovector)}, got {outcome!r}"
        if outcome.ovector != expect.ovector:
            return f"expected ovector {list(expect.ovector)}, got {list(outcome.ovector)}"
        return None

    if isinstance(expect, NoMatchExpectation):
        if not isinstance(outcome, NoMatch):
            return f"expected no match, got {outcome!r}"
        return None

    if isinstance(expect, CompileErrorExpectation):
        if not isinstance(outcome, CompileError):
            return f"expected compile error {expect.code}, got {outcome!r}"
        if (outcome.code, outcome.offset) != (expect.code, expect.offset):
            return (
                f"expected compile error {expect.code} at offset {expect.offset}, "
                f"got {outcome.code} at offset {outcome.offset} ({outcome.message})"
            )
        return None

    if isinstance(expect, MatchErrorExpectation):
        if not isinstance(outcome, MatchError):
            return f"expected match error {expect.code}, got {outcome!r}"
        if outcome.code != expect.code:
            return (
                f"expected match error {expect.code}, "
                f"got {outcome.code} ({outcome.message})"
            )
        return None

    if isinstance(expect, CompiledExpectation):
        if not isinstance(outcome, Compiled):
            return f"expected a successful compile, got {outcome!r}"
        if outcome.capture_count != expect.captures:
            return f"expected {expect.captures} capture groups, got {outcome.capture_count}"
        if tuple(sorted(outcome.names)) != expect.names:
            return f"expected group names {expect.names!r}, got {outcome.names!r}"
        return None

    raise AssertionError(f"unhandled expectation: {expect!r}")
