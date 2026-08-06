"""What the quantifier lowering did to every pattern this repository pins.

PLAN-POST-M6.md asks for a machine-checked migration report beside the
regenerated certificate corpus, and for its columns to stay orthogonal: one
answer per question, each naming the program and the analysis it describes,
never recombined. So a row here carries seven of them.

    blockers      what the pre-check found on the *original* AST, all of it
    lowering      lowered, not needed, declined (blockers), declined (cap)
    pike          `pike_ok` on the *emitted* program, whichever form it is
    program       the compiled pattern, every field of it, hashed
    analysis      the backtracking analyzer's verdict, recorded even where
                  the lockstep path is the one selected
    certificate   which configuration's certificate the pattern carries,
                  and the class that certificate claims
    accessors     cost, stack and memory at one length, each finite or
                  refused, separately

The two independent columns are the point. `a*b*c*d*` is Pike-selected,
carries an accepted Pike certificate and classifies linear, while the
backtracking analyzer answers `ArOverflow` for the same program; a schema with
one certificate column would record that as a contradiction rather than as the
two analyses honestly disagreeing about two different things. And the blocker
column is about the original tree on purpose: a lowerable `a+` has a non-pure
repetition before the lowering and none after, so a column read off the
emitted bytecode would say something else entirely.

Nothing here is the report's own invention. The compiler exports its decision,
its blockers and whether the candidate fitted, and `engine/lowered.py`
recomputes all three from the parsed tree — a second reading of the same
object, written against DESIGN.md section 4.3 rather than against
`compiler.py` — and this module refuses to write a row where the two
disagree. A decision the derivation cannot reproduce is a finding about the
compiler, never a formatting difference to smooth over.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any

from ..leanexport import bridge
from ..paths import CONFORMANCE_DIR, CORPUS_DIR
from . import lowered, spec
from .driver import Engine, InternalError, items, variant_of

PATH = CONFORMANCE_DIR / "migration.json"

SCHEMA = "pcrevera-migration-1"

BEFORE = CORPUS_DIR / "pre-lowering.json"
"""The same patterns as the engine classified them before the lowering.

Half of the census PLAN-POST-M6.md asks for is a statement about one engine and
this module computes it. The other half — that no pattern's class regressed —
compares two, and the earlier one cannot be rebuilt from this checkout, so its
answers are recorded there and joined to the report by
`tests/test_migration.py`. A measurement rather than a contract, kept for the
same reason `oracle/corpus/sweep-regressions.json` is: nothing generates it
twice."""

BEFORE_SCHEMA = "pcrevera-pre-lowering-1"

CLASS_ORDER = {None: 0, spec.CLASS_NOT_PROVEN_LINEAR: 1, spec.CLASS_LINEAR: 2}
"""How much a certificate claims, as an order. No certificate at all says
least, and the class column is the census's subject, so a comparison of two
engines needs the three answers on one scale."""

AT = 1000
"""Where the accessors are read.

One length, because the column is about which of the three answers is finite
rather than about the shape of a curve, and a thousand bytes is the scale
PLAN-POST-M6.md states its numbers at."""

DECISIONS = {
    spec.LOW_NOT_NEEDED: "not needed",
    spec.LOW_LOWERED: "lowered",
    spec.LOW_BLOCKED: "declined (blockers)",
    spec.LOW_CAPPED: "declined (cap)",
}

BLOCKERS = ((spec.LB_NULLABLE, "nullable"), (spec.LB_BSR, "bsr"))


class MigrationError(RuntimeError):
    """The compiler and this reading of the same tree disagree."""


# --- what the emitted program says about the same two questions ---


def emitted_blockers(engine: Engine, built) -> int:
    """The blockers of a program still in counter form, read off the bytecode.

    The lowering copies bodies verbatim and turns `x{m,}` into a star over the
    same body, so these two properties of the counter form are the two
    properties of the lowered candidate: a `\\R` is still a `\\R`, and a
    repetition whose body can finish an iteration emptily still can. Which
    makes this the other half of the equivalence gate — on a pattern the
    compiler kept in counter form, `pike_ok` would have refused the candidate
    exactly when this is nonzero.
    """
    found = 0
    code = items(built.re.fields["code"])
    if any(variant_of(inst.fields["op"]) == "OpBsr" for inst in code):
        found |= spec.LB_BSR
    for index, rep in enumerate(items(built.re.fields["reps"])):
        if rep.fields["hi"] != spec.NONE:
            continue
        if engine.pike_hollow(built, index):
            found |= spec.LB_NULLABLE
    return found


def names(mask: int) -> list[str]:
    return [name for bit, name in BLOCKERS if mask & bit]


def digest(built) -> str:
    """The compiled pattern as one hash. Every field of it, and no other.

    What the census's non-regression half needs from a pattern the lowering
    left alone is that it still compiles to the same thing, and "the same
    thing" is worth being literal about. A row that agreed about the class and
    disagreed about a jump target would say nothing about the lowering and
    everything about something else, so the comparison is over the program
    rather than over what was concluded from it.

    Which means every field a matcher reads has to be in here, not just the
    interesting ones: an instruction naming a character class carries an index
    into a table this would otherwise not hash, so `[a]` and `[b]` would come
    out the same. The two decisions the lowering itself writes down are left
    out on purpose — they are separate columns of the report, and one of them
    is what selects the rows this is compared over.

    Rendered as text and hashed because the recording is a JSON file somebody
    reads: three hundred programs spelled out would bury the columns that are
    the point of it.
    """
    re = built.re.fields
    scalars = ("ncap", "nname", "nregs", "opts", "nltype", "bsr", "hascrlf", "crfirst")
    lines = [" ".join(f"{name} {re[name]}" for name in scalars)]
    lines.append(f"pike {int(re['pike'])}")
    for inst in items(re["code"]):
        lines.append(
            f"i {variant_of(inst.fields['op'])} {inst.fields['arg']} "
            f"{inst.fields['alt']}"
        )
    lines.append("c " + bytes(items(re["classes"])).hex())
    for region in items(re["regions"]):
        lines.append(
            f"g {variant_of(region.fields['kind'])} {region.fields['parent']} "
            f"{region.fields['lo']} {region.fields['hi']}"
        )
    for rep in items(re["reps"]):
        lines.append(
            f"r {rep.fields['lo']} {rep.fields['hi']} {int(rep.fields['greedy'])} "
            f"{rep.fields['head']} {rep.fields['body']} {rep.fields['after']}"
        )
    lines.append("n " + bytes(items(re["names"])).hex())
    for ent in items(re["nameents"]):
        lines.append(
            f"e {ent.fields['off']} {ent.fields['nlen']} {ent.fields['grp']}"
        )
    return hashlib.sha256("\n".join(lines).encode()).hexdigest()


# --- the report ---


@dataclass(frozen=True)
class Subject:
    """One pattern as the corpora spell it, and where it was pinned."""

    pattern: bytes
    options: tuple[str, ...] = ()
    newline: str = "LF"
    bsr: str = "UNICODE"

    def key(self) -> tuple:
        return (self.pattern, self.options, self.newline, self.bsr)


def row(engine: Engine, subject: Subject) -> dict[str, Any] | None:
    """One pattern's row, or None where the engine declines to compile it.

    A decline is a syntax error, an unsupported construct or a documented
    limit, and none of those has anything to say about the lowering. An
    internal error is not one of them: it is the dry run and the emitter
    disagreeing, or the two halves of BOUNDS.md disagreeing, and a report that
    let it fall into the same bucket would count a compiler bug as an expected
    outcome.
    """
    built = engine.compile_pattern(
        subject.pattern,
        options=subject.options,
        newline=subject.newline,
        bsr=subject.bsr,
    )
    if isinstance(built, InternalError):
        raise MigrationError(
            f"{subject.pattern!r} {subject.options}: compilation reported an "
            "internal error, which is a bug of ours rather than a decline"
        )
    if not hasattr(built, "re"):
        return None

    flags = 0
    for name in subject.options:
        flags |= spec.COMPILE_OPTIONS[name]
    work = bridge._parse_work(
        subject.pattern, flags, spec.NEWLINE_CONVENTIONS[subject.newline]
    )
    tree = bridge._tree(
        items(work.fields["nodes"]),
        bytes(items(work.fields["classes"])),
        work.fields["root"],
    )
    mine = lowered.decide(
        tree, built.re.fields["ncap"], "ENDANCHORED" in subject.options
    )
    theirs = (
        built.re.fields["blockers"],
        built.re.fields["lowdec"],
        bool(built.re.fields["lowfits"]),
    )
    if mine != theirs:
        raise MigrationError(
            f"{subject.pattern!r} {subject.options}: the compiler recorded "
            f"{theirs}, reading the tree again gives {mine}"
        )

    pike = bool(built.re.fields["pike"])
    decision = built.re.fields["lowdec"]
    if decision == spec.LOW_LOWERED and not pike:
        raise MigrationError(
            f"{subject.pattern!r} {subject.options}: lowered and then refused "
            "by pike_ok, which is the empty set this report exists to keep empty"
        )
    if decision != spec.LOW_LOWERED:
        shown = emitted_blockers(engine, built)
        if shown != built.re.fields["blockers"]:
            raise MigrationError(
                f"{subject.pattern!r} {subject.options}: the pre-check found "
                f"{names(built.re.fields['blockers'])} and the counter form it "
                f"left behind shows {names(shown)}"
            )
    if not pike and not built.re.fields["blockers"] and decision != spec.LOW_CAPPED:
        raise MigrationError(
            f"{subject.pattern!r} {subject.options}: on the backtracking "
            "matcher with no blocker and no cap decision to name"
        )

    verdict, _ = engine.analyze(built)
    if verdict == "ArShape":
        raise MigrationError(
            f"{subject.pattern!r} {subject.options}: ArShape, which is the two "
            "halves of BOUNDS.md disagreeing about one program"
        )

    config = "CfgPike" if pike else "CfgBacktrack"
    flag, slot = {"CfgPike": ("haspikecert", "pikecert"),
                  "CfgBacktrack": ("hascert", "cert")}[config]
    carried = bool(built.re.fields[flag])
    status, value = engine.complexity_class(built)
    return {
        "pattern": subject.pattern.hex(),
        "options": list(subject.options),
        "newline": subject.newline,
        "bsr": subject.bsr,
        "blockers": names(built.re.fields["blockers"]),
        "lowering": DECISIONS[decision],
        "fits": bool(built.re.fields["lowfits"]),
        "pike": pike,
        "program": digest(built),
        "analysis": "accepted" if verdict == "ArOk" else verdict,
        "certificate": {
            "config": config if carried else None,
            "class": value if status == spec.OK else None,
        },
        "accessors": {
            "n": AT,
            **{
                kind: (None if status else number)
                for kind in ("cost", "stack", "mem")
                for status, number in (engine.worst_case(built, kind, AT),)
            },
        },
    }


def subjects() -> list[Subject]:
    """Every pattern the committed corpora pin, in one list without repeats."""
    from ..oracle import conformance
    from ..sweep import population, shard
    from . import certificate_corpus

    seen: dict[tuple, Subject] = {}

    def add(one: Subject) -> None:
        seen.setdefault(one.key(), one)

    for case in conformance.load().cases:
        add(
            Subject(
                case.pattern,
                tuple(case.options),
                case.newline or "LF",
                case.bsr or "UNICODE",
            )
        )
    for pattern in certificate_corpus.patterns():
        add(Subject(pattern))
    for case in population.population(
        shard.SEED,
        structured=shard.STRUCTURED,
        hostile=shard.HOSTILE,
        subjects=shard.SUBJECTS,
        stride=shard.STRIDE,
    ):
        add(Subject(case.pattern, case.options, case.newline, case.bsr))
    return [seen[key] for key in sorted(seen)]


def corpus() -> dict[str, Any]:
    engine = Engine()
    rows = [row(engine, one) for one in subjects()]
    kept = [one for one in rows if one is not None]
    counts: dict[str, int] = {}
    for one in kept:
        counts[one["lowering"]] = counts.get(one["lowering"], 0) + 1
    return {
        "schema": SCHEMA,
        "note": (
            "Generated by pcrevera.engine.migration from the committed corpora. "
            "Every row is the compiler's own record of what it decided, checked "
            "against a second reading of the same parsed tree; the counts are a "
            "census of the columns and nothing this file does not already say."
        ),
        "at": AT,
        "counts": {
            "patterns": len(kept),
            "declined-to-compile": len(rows) - len(kept),
            "lockstep": sum(1 for one in kept if one["pike"]),
            "linear": sum(
                1 for one in kept if one["certificate"]["class"] == spec.CLASS_LINEAR
            ),
            "no-certificate": sum(
                1 for one in kept if one["certificate"]["config"] is None
            ),
            **{f"lowering: {name}": counts.get(name, 0) for name in DECISIONS.values()},
        },
        "rows": kept,
    }


def corpus_text() -> str:
    return json.dumps(corpus(), indent=2, sort_keys=True) + "\n"


def load(path=PATH) -> dict[str, Any]:
    built = json.loads(path.read_text())
    if built.get("schema") != SCHEMA:
        raise ValueError(f"{path.name} has schema {built.get('schema')!r}, not {SCHEMA}")
    return built


def before(path=BEFORE) -> dict[str, Any]:
    built = json.loads(path.read_text())
    if built.get("schema") != BEFORE_SCHEMA:
        raise ValueError(
            f"{path.name} has schema {built.get('schema')!r}, not {BEFORE_SCHEMA}"
        )
    return built


def key(row: dict[str, Any]) -> tuple:
    """What identifies a pattern in either file. The two are generated by
    different engines and joined by this, so it is spelled once."""
    return (row["pattern"], tuple(row["options"]), row["newline"], row["bsr"])
