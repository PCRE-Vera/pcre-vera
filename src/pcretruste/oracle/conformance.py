"""The language-neutral conformance corpus.

DESIGN.md section 8 asks for a JSON corpus checked into the repo with a tiny
runner per backend, so that "the Python interpreter, the generated Go, and the
generated JavaScript agree bit for bit" is something that gets checked rather
than hoped for.

The cases are the wave 1 differential corpus, which is already three
statements of the same thing — the hand-written expectation, the pinned pcre2,
and our own engine. This module restates them in a form a runner in any
language can read without reimplementing the loader: every byte string is
lowercase hex, every option is the number the engine actually takes, and every
expectation is one tagged object. Nothing is recorded from a run, so a backend
that agrees with the file agrees with pcre2 for the same reason the Python
engine does.

Bounds are the other half of what section 8 asks for, and they live in
`conformance/certificates.json` rather than here: what they are about is the
program a pattern compiles to, not the answer it gives.

The document envelope — the schema number, the note, the exact bytes a
committed corpus is written as — lives here rather than in either corpus,
because the runners check one schema against both files and would otherwise
have to be told which is which.
"""

from __future__ import annotations

import json
from typing import Any

from ..engine import spec
from ..paths import CONFORMANCE_DIR
from . import corpus as wave1

SCHEMA = 1
"""The version of the envelope, shared by every conformance corpus."""

PATH = CONFORMANCE_DIR / "corpus.json"

NOTE = (
    "Generated from oracle/corpus/wave1.json by pcretruste.oracle.conformance. "
    "Every implementation of the engine must give exactly these answers, so a "
    "disagreement between two of them is a disagreement with this file first."
)


def _expectation(case: wave1.Case) -> dict[str, Any]:
    match case.expect:
        case wave1.MatchExpectation(ovector=ovector):
            return {"kind": "match", "ovector": list(ovector)}
        case wave1.NoMatchExpectation():
            return {"kind": "nomatch"}
        case wave1.CompileErrorExpectation(code=code, offset=offset):
            return {"kind": "compileError", "code": code, "offset": offset}
        case wave1.CompiledExpectation(captures=captures, names=names):
            # Keyed by the hex of the name's bytes, because a group name is a
            # byte string and only the corpus author knows how to read it.
            return {
                "kind": "compiled",
                "captures": captures,
                "names": {name.hex(): number for name, number in names},
            }
    raise ValueError(f"the conformance corpus has no form for {case.expect!r}")


def _flags(names: tuple[str, ...], table: dict[str, int]) -> int:
    bits = 0
    for name in names:
        bits |= table[name]
    return bits


def _case(case: wave1.Case) -> dict[str, Any]:
    entry: dict[str, Any] = {
        "name": case.name,
        "pattern": case.pattern.hex(),
        "flags": _flags(case.options, spec.COMPILE_OPTIONS),
        "newline": spec.NEWLINE_CONVENTIONS[case.newline or "LF"],
        "bsr": spec.BSR_CONVENTIONS[case.bsr or "UNICODE"],
        "expect": _expectation(case),
    }
    if case.subject is not None:
        entry["subject"] = case.subject.hex()
        entry["matchFlags"] = _flags(case.match_options, spec.MATCH_OPTIONS)
        entry["start"] = case.start
    if case.note:
        # The sentence saying what the case pins, which is what a reader of a
        # failure in any of the three runners wants first.
        entry["note"] = case.note
    return entry


def document(note: str, cases: list[dict[str, Any]], **extra: Any) -> dict[str, Any]:
    """One conformance corpus as plain JSON data."""
    return {"schema": SCHEMA, "note": note, "cases": cases, **extra}


def text(built: dict[str, Any]) -> str:
    """A corpus as the committed file spells it, ending in one newline."""
    return json.dumps(built, indent=2, sort_keys=True) + "\n"


def read(path) -> dict[str, Any]:
    """A committed corpus, with its envelope checked."""
    built = json.loads(path.read_text())
    if built.get("schema") != SCHEMA:
        raise ValueError(f"{path.name} has schema {built.get('schema')!r}, not {SCHEMA}")
    section(built, "cases", path)
    return built


def section(built: dict[str, Any], name: str, path) -> list[Any]:
    """One named array of a corpus, which may carry more than one.

    The certificate corpus holds the checker's cases and the analyzer's
    patterns separately, because the two halves of DESIGN.md section 5 are
    reached differently. Asking for a section by name is what keeps the "is
    this a corpus at all" rule here rather than at every place that reads a
    second one.

    A section is a list with something in it. Truthiness is not the same
    question — an object and a string are both true — and the other two
    runners do not ask it: JavaScript wants an array and Go decodes into a
    slice or fails. A corpus is one thing in three languages, so a malformed
    one has to be refused in three.
    """
    held = built.get(name)
    if not isinstance(held, list) or not held:
        raise ValueError(f"{path.name} holds no {name}")
    return held


def corpus() -> dict[str, Any]:
    """The wave 1 corpus, restated."""
    loaded = wave1.load(wave1.WAVE1_PATH)
    return document(NOTE, [_case(case) for case in loaded.cases])


def corpus_text() -> str:
    return text(corpus())


def load(path=PATH) -> wave1.Corpus:
    """The committed corpus, decoded back into the cases the runner takes.

    The Python runner then asks `corpus.check` the same question the wave 1
    tests ask, rather than carrying a second opinion about what agreement is.
    """
    cases = []
    for entry in read(path)["cases"]:
        expect = entry["expect"]
        cases.append(
            wave1.Case(
                name=entry["name"],
                pattern=bytes.fromhex(entry["pattern"]),
                subject=None if "subject" not in entry else bytes.fromhex(entry["subject"]),
                expect=_decode(expect),
                options=_names(entry["flags"], spec.COMPILE_OPTIONS),
                match_options=_names(entry.get("matchFlags", 0), spec.MATCH_OPTIONS),
                newline=_convention(entry["newline"], spec.NEWLINE_CONVENTIONS),
                bsr=_convention(entry["bsr"], spec.BSR_CONVENTIONS),
                start=entry.get("start", 0),
                note=entry.get("note", ""),
            )
        )
    return wave1.Corpus(path=path, cases=tuple(cases))


def _decode(expect: dict[str, Any]) -> wave1.Expectation:
    match expect["kind"]:
        case "match":
            return wave1.MatchExpectation(tuple(expect["ovector"]))
        case "nomatch":
            return wave1.NoMatchExpectation()
        case "compileError":
            return wave1.CompileErrorExpectation(
                code=expect["code"], offset=expect["offset"]
            )
        case "compiled":
            return wave1.CompiledExpectation(
                captures=expect["captures"],
                names=tuple(
                    sorted(
                        (bytes.fromhex(name), number)
                        for name, number in expect["names"].items()
                    )
                ),
            )
    raise ValueError(f"unknown expectation kind: {expect['kind']!r}")


def _names(bits: int, table: dict[str, int]) -> tuple[str, ...]:
    return tuple(name for name, bit in table.items() if bits & bit)


def _convention(value: int, table: dict[str, int]) -> str:
    for name, number in table.items():
        if number == value:
            return name
    raise ValueError(f"no convention numbered {value}")


__all__ = [
    "NOTE",
    "PATH",
    "SCHEMA",
    "corpus",
    "corpus_text",
    "document",
    "load",
    "read",
    "text",
]
