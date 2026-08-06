"""The gate 5 stratification: every owed function, measured before priced.

The coverage ledger says who owes a simulation lemma; it says nothing about
what each lemma will cost. Gate 4 priced one shape — straight loops over
mutable stores, no calls — and left the call-composition shapes unmeasured.
Before gate 5 is scheduled, the 80 owed functions get stratified by the
features that drive proof volume, and the next sample gets chosen by a rule
written here rather than by feel.

Everything in the report is computed from the artifact except two recorded
tables: the name-family map, which is a mechanical grouping by name and not
a claim about ownership, and the selection rule's constants. A test
regenerates the report and compares it byte for byte, the same discipline
as the coverage ledger.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from ..paths import CONFORMANCE_DIR
from . import coverage, ir

PATH = CONFORMANCE_DIR / "layer-i-strata.json"

# Name families, mechanically: exact names first, then prefixes. This is a
# grouping of like-named (and in practice like-shaped) functions for
# stratified sampling, not a statement of which subsystem owns what —
# `newline_at` is as much the matcher's as the parser's, and stays so.
FAMILY_EXACT = {
    "match": "dispatch",
    "bt_match": "dispatch",
    "pike_match": "dispatch",
    "compile": "compiler",
    "generate": "compiler",
    "emit": "compiler",
    "region_kids": "compiler",
    "check_fit": "compiler",
    "count_regs": "compiler",
    "size_node": "compiler",
    "new_rep": "compiler",
    "open_region": "compiler",
    "close_region": "compiler",
    "drop_empty_region": "compiler",
    "plan_lowering": "compiler",
    "scan_first": "compiler",
    "mark_seen": "compiler",
    "push_job": "compiler",
    "push_patch": "compiler",
    "push_bt": "backtracker",
    "write_reg": "backtracker",
    "charge_grow": "meter",
    "sat_add": "arithmetic",
    "sat_mul": "arithmetic",
    "ct": "tables",
    "newline_at": "tables",
    "newline_before": "tables",
    "at_line_end": "tables",
    "bsr_at": "tables",
    "word_edge": "tables",
    "class_has": "tables",
}

FAMILY_PREFIX = (
    ("bt_", "backtracker"),
    ("pike_", "pike"),
    ("ctx_", "context"),
    ("cert_", "certificate"),
    ("price_", "certificate"),
    ("scan_", "certificate"),
    ("shape_", "certificate"),
    ("charge_", "certificate"),
    ("walk_", "compiler"),
    ("poly_", "arithmetic"),
    ("bound_", "arithmetic"),
    ("re_", "accessors"),
)


def family(name: str) -> str:
    if name in FAMILY_EXACT:
        return FAMILY_EXACT[name]
    for prefix, fam in FAMILY_PREFIX:
        if name.startswith(prefix):
            return fam
    raise ValueError(f"no family for {name}")


def shape(func: ir.Func) -> dict:
    """The control-flow features that drive proof volume, walked off the
    body. A call's arguments are expressions and contribute no statements;
    a loop's body is walked under the in-loop flag because a call there is
    the fuel-through-iteration pattern gate 4 did not price."""
    out = {
        "statements": 0,
        "loops": 0,
        "ifs": 0,
        "switches": 0,
        "call_sites": 0,
        "calls_in_loops": 0,
    }

    def walk(node: object, inloop: bool) -> None:
        if isinstance(node, tuple):
            for item in node:
                walk(item, inloop)
            return
        if isinstance(node, ir.While):
            out["loops"] += 1
            out["statements"] += 1
            walk(node.body, True)
            return
        kind = type(node).__name__
        if kind in (
            "Let", "Assign", "Take", "Swap", "Copy", "Freeze", "Push",
            "Pop", "Truncate", "Reserve", "If", "Switch", "Break",
            "Continue", "Return", "Call",
        ):
            out["statements"] += 1
        if isinstance(node, ir.Call):
            out["call_sites"] += 1
            if inloop:
                out["calls_in_loops"] += 1
            return
        if kind == "If":
            out["ifs"] += 1
        if kind == "Switch":
            out["switches"] += 1
        for slot in getattr(node, "__dataclass_fields__", ()):
            value = getattr(node, slot)
            if isinstance(value, tuple) or hasattr(value, "__dataclass_fields__"):
                walk(value, inloop)

    walk(func.body, False)
    return out


def modes(func: ir.Func) -> dict:
    return {
        "in": sum(1 for p in func.params if p.mode == "in"),
        "inout": sum(1 for p in func.params if p.mode == "inout"),
    }


# The selection rule for the call-composition sample, applied to the rows
# rather than to anyone's intuition. Universe: unproved owed functions with
# at least one call inside a loop — the pattern gate 4 could not price, a
# callee's budget threaded through iteration — and at least two call sites,
# so composition is exercised more than once. Score: statements plus
# LOOP_WEIGHT per loop, because invariants are the expensive part. The
# sample is the minimum score; ties break toward more distinct callees,
# then fewer ifs, then the name.
LOOP_WEIGHT = 10

RULE = (
    "among unproved owed functions with calls_in_loops >= 1 and "
    "call_sites >= 2, minimize statements + 10*loops; tie-break by more "
    "distinct callees, then fewer ifs, then name"
)


def choose(rows: list[dict]) -> dict:
    universe = [
        r for r in rows
        if not r["theorem"] and r["shape"]["calls_in_loops"] >= 1
        and r["shape"]["call_sites"] >= 2
    ]
    scored = sorted(
        universe,
        key=lambda r: (
            r["shape"]["statements"] + LOOP_WEIGHT * r["shape"]["loops"],
            -len(r["callees"]),
            r["shape"]["ifs"],
            r["name"],
        ),
    )
    return {
        "rule": RULE,
        "selected": scored[0]["name"] if scored else None,
        "universe": [
            {
                "name": r["name"],
                "score": r["shape"]["statements"]
                + LOOP_WEIGHT * r["shape"]["loops"],
            }
            for r in scored
        ],
    }


def strata(program: ir.Program, artifact_sha256: str) -> dict:
    graph = coverage.call_graph(program)
    manifest = coverage.ledger(program, artifact_sha256)
    owed = [entry["name"] for entry in manifest["post_parse"]]
    owed_set = set(owed)
    funcs = {f.name: f for f in program.funcs}

    depths: dict[str, int] = {}

    def depth(name: str) -> int:
        if name in depths:
            return depths[name]
        callees = [c for c in graph[name] if c in owed_set]
        depths[name] = 0 if not callees else 1 + max(depth(c) for c in callees)
        return depths[name]

    def closure(name: str) -> list[str]:
        seen: set[str] = set()
        stack = [name]
        while stack:
            for callee in graph[stack.pop()]:
                if callee in owed_set and callee not in seen:
                    seen.add(callee)
                    stack.append(callee)
        return sorted(seen)

    rows = []
    for name in owed:
        func = funcs[name]
        rows.append({
            "name": name,
            "theorem": coverage.THEOREMS.get(name, ""),
            "family": family(name),
            "shape": shape(func),
            "modes": modes(func),
            "callees": sorted(c for c in graph[name] if c in owed_set),
            "depth": depth(name),
            "closure": closure(name),
        })

    families: dict[str, int] = {}
    for row in rows:
        families[row["family"]] = families.get(row["family"], 0) + 1

    return {
        "artifact": artifact_sha256,
        "counts": {
            "owed": len(rows),
            "proved": sum(1 for r in rows if r["theorem"]),
            "families": dict(sorted(families.items())),
        },
        "functions": rows,
        "sample": choose(rows),
    }


def render(report: dict) -> str:
    return json.dumps(report, indent=2, sort_keys=True) + "\n"


def build(artifact: Path) -> str:
    from . import serialize

    program = serialize.loads(artifact.read_text())
    digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
    return render(strata(program, digest))


__all__ = ["PATH", "RULE", "build", "choose", "family", "render", "shape", "strata"]
