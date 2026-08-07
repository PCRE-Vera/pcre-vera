"""The feature ledger: the one editable source of admission state.

`conformance/features.json` has a row per syntax family saying whether it is
implemented, how far its S, R and I chains have got, which claims of the
theorem inventory carry it, whether the default surface admits it, whether
`allowGatedFeatures` does, and which opcodes it may make the compiler emit.
Everything else — the three feature sets a manifest repeats, both
compile-capability masks, and eventually the generated admission function — is
derived from those rows rather than written down a second time.

The rule that makes the file worth having is the one in `admits`: a wave 2 row
is in the default surface only as the conclusion of its four status columns.
Wave 1 keeps its default surface through an explicitly named
`m7-foundation-fallback` basis instead, which is the documented DESIGN.md
section 10 contract rather than a proof it does not have. No wave 2 row may
borrow that basis.
"""

from __future__ import annotations

import json
from pathlib import Path

from ..paths import CONFORMANCE_DIR
from ..tir import ir
from . import canonical

PATH = CONFORMANCE_DIR / "features.json"

SCHEMA = "pcrevera/features@1"

FALLBACK = "m7-foundation-fallback"
"""The admission basis wave 1 rows carry: the default surface is theirs because
DESIGN.md section 10 says an artifact whose layers S and R are proved and whose
layer I is pinned may ship, not because their I chain is complete."""

STATUS = ("complete", "incomplete", "absent")
IMPLEMENTATION = ("complete", "absent")

WAVES = (1, 2, 3, None)
"""DESIGN.md section 2.1 stages features in three waves, and everything else is
out of scope with no wave at all. An unclassified number would slip past the
rule that separates wave 1's named fallback from wave 2's complete chain."""

FIELDS = {
    "key": str,
    "wave": (int, type(None)),
    "title": str,
    "spellings": list,
    "implementation": str,
    "artifactVersion": (int, type(None)),
    "s": str,
    "r": str,
    "i": str,
    "claims": list,
    "admissionBasis": (str, type(None)),
    "default": bool,
    "gated": bool,
    "dependsOn": list,
    "capabilities": dict,
}
OPTIONAL_FIELDS = {"note": str}

NUMERIC_FIELDS = ("wave", "artifactVersion")
"""Where a Boolean would otherwise pass for a number. Python makes `bool` a
subclass of `int`, so `wave = true` compares equal to 1 and would let a wave 2
row claim wave 1's admission basis."""

RESERVED_PREFIX = "test."
"""Feature keys the admission fixtures use. A production ledger may not carry
one, so a mock row cannot reach a shipped capsule by being copied."""


class LedgerError(ValueError):
    """A ledger that is not a ledger, with the row that broke it named."""


def load(path: Path = PATH) -> dict:
    text = path.read_text(encoding="utf-8")
    ledger = json.loads(text)
    if canonical(ledger) != text:
        raise LedgerError(f"{path} is not in canonical form")
    validate(ledger)
    return ledger


def _rowerr(row: object, message: str) -> LedgerError:
    key = row.get("key", "<unkeyed>") if isinstance(row, dict) else "<not an object>"
    return LedgerError(f"feature {key}: {message}")


def validate(ledger: object, *, allow_reserved: bool = False) -> None:
    """Every rule the file has to obey before anything derives from it."""
    if not isinstance(ledger, dict):
        raise LedgerError("the ledger is not an object")
    if ledger.get("schema") != SCHEMA:
        raise LedgerError(f"the ledger is not {SCHEMA}")
    extra = set(ledger) - {"schema", "note", "features"}
    if extra:
        raise LedgerError(f"unknown top-level fields: {', '.join(sorted(extra))}")
    rows = ledger.get("features")
    if not isinstance(rows, list) or not rows:
        raise LedgerError("the ledger has no features")

    keys: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            raise LedgerError("a feature row is not an object")
        missing = set(FIELDS) - set(row)
        if missing:
            raise _rowerr(row, f"missing {', '.join(sorted(missing))}")
        unknown = set(row) - set(FIELDS) - set(OPTIONAL_FIELDS)
        if unknown:
            raise _rowerr(row, f"unknown fields {', '.join(sorted(unknown))}")
        for name, want in {**FIELDS, **OPTIONAL_FIELDS}.items():
            if name in row and not isinstance(row[name], want):
                raise _rowerr(row, f"{name} has the wrong type")
        key = row["key"]
        if not key or key in keys:
            raise _rowerr(row, "the key is empty or repeated")
        if key.startswith(RESERVED_PREFIX) and not allow_reserved:
            raise _rowerr(row, f"{RESERVED_PREFIX}* is reserved for fixtures")
        keys.add(key)
        _validate_row(row)

    for row in rows:
        for needed in row["dependsOn"]:
            if needed not in keys:
                raise _rowerr(row, f"depends on {needed}, which no row declares")
            if row["default"] and not _by_key(rows, needed)["default"]:
                raise _rowerr(row, f"is default but depends on gated {needed}")
            if row["gated"] and not _by_key(rows, needed)["gated"]:
                raise _rowerr(row, f"is gated but depends on unsupported {needed}")
    _no_cycles(rows)


def _by_key(rows: list[dict], key: str) -> dict:
    for row in rows:
        if row["key"] == key:
            return row
    raise LedgerError(f"no row for {key}")


def _no_cycles(rows: list[dict]) -> None:
    """Dependency order has to be an order; a cycle would make admission
    depend on which row the deriver happened to visit first."""
    edges = {row["key"]: list(row["dependsOn"]) for row in rows}
    state: dict[str, int] = {}

    def walk(key: str) -> None:
        if state.get(key) == 2:
            return
        if state.get(key) == 1:
            raise LedgerError(f"feature {key}: dependencies form a cycle")
        state[key] = 1
        for needed in edges[key]:
            walk(needed)
        state[key] = 2

    for key in edges:
        walk(key)


def _validate_row(row: dict) -> None:
    for name in NUMERIC_FIELDS:
        if isinstance(row[name], bool):
            raise _rowerr(row, f"{name} is a Boolean where a number belongs")
    if row["wave"] not in WAVES:
        raise _rowerr(row, "wave is not one of the three, nor out of scope")
    if row["implementation"] not in IMPLEMENTATION:
        raise _rowerr(row, "implementation is not complete or absent")
    for layer in ("s", "r", "i"):
        if row[layer] not in STATUS:
            raise _rowerr(row, f"{layer} is not one of {', '.join(STATUS)}")
    if row["admissionBasis"] not in (None, FALLBACK, "proof-chain"):
        raise _rowerr(row, "admissionBasis is not a basis this project knows")
    if row["admissionBasis"] == FALLBACK and row["wave"] != 1:
        raise _rowerr(row, f"claims the {FALLBACK} basis, which is wave 1's alone")

    for name in ("spellings", "claims", "dependsOn"):
        values = row[name]
        if any(not isinstance(v, str) for v in values):
            raise _rowerr(row, f"{name} holds something that is not a string")
        if len(set(values)) != len(values):
            raise _rowerr(row, f"{name} repeats an entry")

    caps = row["capabilities"]
    if set(caps) != {"default", "gated"}:
        raise _rowerr(row, "capabilities needs exactly default and gated")
    for mode, values in caps.items():
        if not isinstance(values, list) or any(not isinstance(v, str) for v in values):
            raise _rowerr(row, f"capabilities.{mode} is not a list of names")
        if sorted(set(values)) != values:
            raise _rowerr(row, f"capabilities.{mode} is unsorted or repeats")
    if set(caps["default"]) & set(caps["gated"]):
        raise _rowerr(row, "a capability is in both modes; gated is the addition")

    # A capability is what the compiler may emit for an admitted feature, so a
    # mode that does not admit the row cannot have one. Without this a ledger
    # can hold an opcode declaration nothing will ever reach, which is a policy
    # about nothing and, worse, counts as ownership when the artifact's opcodes
    # are checked for a claimant.
    if not row["default"] and caps["default"]:
        raise _rowerr(row, "is not in the default surface but declares default opcodes")
    if not row["gated"] and caps["gated"]:
        raise _rowerr(row, "is not admitted under gating but declares gated opcodes")

    if row["implementation"] == "absent":
        if row["claims"] or caps["default"] or caps["gated"]:
            raise _rowerr(row, "is unimplemented but claims proofs or opcodes")
        if row["artifactVersion"] is not None:
            raise _rowerr(row, "is unimplemented but names an artifact version")
        if row["gated"] or row["default"]:
            raise _rowerr(row, "is unimplemented but admitted")
        if (row["s"], row["r"], row["i"]) != ("absent", "absent", "absent"):
            raise _rowerr(row, "is unimplemented but carries a proof status")
    else:
        if row["artifactVersion"] is None:
            raise _rowerr(row, "is implemented but names no artifact version")
        # An implemented row with no claim would satisfy every status column
        # vacuously, and the join against the inventory would have nothing to
        # refuse. The plan's rule ends with "every named proof belongs to the
        # shipped capsule"; a row that names none has not met it.
        if not row["claims"]:
            raise _rowerr(row, "is implemented but names no proof")

    if row["default"] and not row["gated"]:
        raise _rowerr(row, "is default but not gated; gated admits at least as much")
    if row["default"] != admits(row):
        raise _rowerr(row, "the default flag is not what its status columns say")


def admits(row: dict) -> bool:
    """Whether the default surface takes this row, from its columns alone.

    A wave 2 row needs the whole chain. A wave 1 row needs everything but I,
    and has to say out loud that the M7 foundation fallback is what stands in
    for it.
    """
    if row["implementation"] != "complete":
        return False
    if row["s"] != "complete" or row["r"] != "complete":
        return False
    if row["i"] == "complete":
        return True
    return row["admissionBasis"] == FALLBACK


def sets(ledger: dict) -> dict[str, list[str]]:
    """The three feature sets, an exact partition of the ledger's keys."""
    rows = ledger["features"]
    return {
        "default": sorted(r["key"] for r in rows if r["default"]),
        "gated": sorted(r["key"] for r in rows if r["gated"] and not r["default"]),
        "unsupported": sorted(
            r["key"] for r in rows if not r["gated"] and not r["default"]
        ),
    }


def capability_masks(ledger: dict) -> dict[str, list[str]]:
    """Both compile-capability masks, derived from the admitted rows.

    Default mode may emit what the default rows declare. Gated mode may emit
    that plus whatever a gated row adds, which is how a gated optimization
    reaches an opcode the default artifact never writes. Validation has already
    made an unadmitted row's lists empty, so the union is over what is
    reachable rather than over what is written down.
    """
    default: set[str] = set()
    gated: set[str] = set()
    for row in ledger["features"]:
        default |= set(row["capabilities"]["default"])
        gated |= set(row["capabilities"]["default"]) | set(row["capabilities"]["gated"])
    return {"default": sorted(default), "gated": sorted(gated)}


COLUMNS = (("s", "S"), ("r", "R"), ("i", "I"))
"""Which status column each layer of the inventory answers for."""


def check_against_inventory(ledger: dict, built: dict) -> None:
    """Every proof a row spends, joined to the capsule's own inventory.

    This is the last conjunct of the plan's admission rule, and the only one
    that cannot be decided inside the ledger: a status column is a word, and
    what makes it worth anything is the theorem behind it.

    Three things are checked, and the third is the one that stops the join from
    being decorative. The claim has to exist in this capsule; it has to be
    complete; and it has to cover this feature — a row cannot spend S-1, the
    AST definition, as evidence for atomic groups. On top of that, a column
    that says `complete` has to have a proof of that layer behind it, so a
    definition alone never closes a row.
    """
    known = {claim["id"]: claim for claim in built["claims"]}
    for row in ledger["features"]:
        proved: dict[str, int] = {}
        for name in row["claims"]:
            claim = known.get(name)
            if claim is None:
                raise _rowerr(row, f"names {name}, which this capsule has no claim for")
            if claim["status"] != "complete":
                raise _rowerr(row, f"names {name}, which is {claim['status']}")
            if row["key"] not in claim.get("features", ()):
                raise _rowerr(row, f"names {name}, which does not cover it")
            if claim["kind"] == "proof":
                proved[claim["layer"]] = proved.get(claim["layer"], 0) + 1
        for column, layer in COLUMNS:
            if row[column] == "complete" and not proved.get(layer):
                raise _rowerr(row, f"says layer {layer} is complete with no proof of it")


def opcodes(program: ir.Program) -> list[str]:
    """The artifact's own opcode names, which the capability names have to be."""
    for enum in program.enums:
        if enum.name == "Op":
            return list(enum.variants)
    raise LedgerError("the artifact declares no Op enum")


def check_against_artifact(ledger: dict, program: ir.Program) -> None:
    """The capability vocabulary, held to the artifact rather than to itself.

    Two directions, and both matter: a capability naming an opcode the engine
    does not have is a policy about nothing, and an opcode no row claims is an
    opcode the ledger cannot gate.
    """
    known = set(opcodes(program))
    claimed: set[str] = set()
    for row in ledger["features"]:
        for mode in ("default", "gated"):
            for name in row["capabilities"][mode]:
                if name not in known:
                    raise _rowerr(row, f"{name} is not an opcode of this artifact")
                claimed.add(name)
    orphans = sorted(known - claimed)
    if orphans:
        raise LedgerError(
            f"the artifact has opcodes no feature claims: {', '.join(orphans)}"
        )


__all__ = [
    "FALLBACK",
    "IMPLEMENTATION",
    "PATH",
    "RESERVED_PREFIX",
    "SCHEMA",
    "STATUS",
    "WAVES",
    "LedgerError",
    "admits",
    "capability_masks",
    "check_against_artifact",
    "check_against_inventory",
    "load",
    "opcodes",
    "sets",
    "validate",
]
