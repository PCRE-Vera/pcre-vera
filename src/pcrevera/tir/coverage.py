"""The layer I coverage ledger: what the refinement proof still owes.

M7's gate 5 has to prove a simulation lemma for every function the public API
reaches after the parse. "Every function" is not a condition anyone can check
by reading — the artifact holds 122 of them — so it is computed here instead,
from the artifact's own call graph, and written down as a manifest that a test
regenerates and compares. A new callee cannot appear without failing the
build, and completion becomes arithmetic: no entry left without a theorem.

The parse is the one boundary, and it is drawn where the exclusion is honest:
a function is excluded when the public API cannot reach it except by way of
`parse`. That is deliberately narrower than "everything `parse` calls" —
`newline_at` and `ct` are the parser's as well as the matcher's, and a lemma
for them is owed by the side that is not excluded. Everything not
parser-exclusive is owed a lemma.

Nothing here reads the Lean sources; the theorem column is a table this module
carries, and it is gate 5's job to fill it in as the lemmas land.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from ..paths import CONFORMANCE_DIR
from . import ir

PATH = CONFORMANCE_DIR / "layer-i.json"

# What the hand-written wrappers call. Go spells them with the façade's `Tir_`
# prefix and JavaScript through the module's exports, but they are these
# functions, and they are the whole surface the public API reaches.
ENTRIES = (
    "compile",
    "match",
    "ctx_create",
    "ctx_match",
    "re_class",
    "re_cost",
    "re_mem",
    "re_stack",
)

PARSER_ROOT = "parse"

PARSER_REASON = (
    "the pattern-text-to-AST step is a tested link until M10, so the parser "
    "and what the public API cannot reach except through it carry no "
    "simulation lemma in M7; a function the parser shares with anything after "
    "it is owed one anyway and stays in post_parse"
)

# name -> the simulation theorem that discharges it, once it exists. Gate 5
# fills this in; an empty value is work still owed.
THEOREMS: dict[str, str] = {}


def callees(func: ir.Func) -> set[str]:
    """Every function this one names, in any statement it holds."""
    out: set[str] = set()

    def walk(node: object) -> None:
        if isinstance(node, ir.Call):
            out.add(node.fn)
        if isinstance(node, tuple):
            for item in node:
                walk(item)
            return
        for slot in getattr(node, "__dataclass_fields__", ()):
            walk(getattr(node, slot))

    walk(func.body)
    return out


def call_graph(program: ir.Program) -> dict[str, set[str]]:
    return {f.name: callees(f) for f in program.funcs}


def reach(graph: dict[str, set[str]], roots: tuple[str, ...], cut: frozenset[str]) -> set[str]:
    """What the roots reach, never entering a name in `cut`."""
    seen: set[str] = set()
    stack = [r for r in roots if r not in cut]
    while stack:
        name = stack.pop()
        if name in seen or name in cut:
            continue
        seen.add(name)
        stack.extend(graph.get(name, ()))
    return seen


def ledger(program: ir.Program, artifact_sha256: str) -> dict:
    graph = call_graph(program)
    everything = {f.name for f in program.funcs}
    live = reach(graph, ENTRIES, frozenset())
    after_parse = reach(graph, ENTRIES, frozenset({PARSER_ROOT}))
    parser_only = sorted((live - after_parse) | {PARSER_ROOT})
    owed = sorted(after_parse)
    return {
        "artifact": artifact_sha256,
        "entries": list(ENTRIES),
        "counts": {
            "declared": len(everything),
            "reachable": len(live),
            "post_parse": len(owed),
            "parser": len(parser_only),
            "unreachable": len(everything - live),
            "proved": sum(1 for name in owed if THEOREMS.get(name)),
        },
        "post_parse": [
            {"name": name, "theorem": THEOREMS.get(name, "")} for name in owed
        ],
        "parser": {
            "reason": PARSER_REASON,
            "functions": parser_only,
            "shared_with_post_parse": sorted(
                reach(graph, (PARSER_ROOT,), frozenset()) & set(owed)
            ),
        },
        "unreachable": sorted(everything - live),
    }


def complete(manifest: dict) -> bool:
    """Has gate 5 closed? Every post-parse function named by a theorem."""
    return all(entry["theorem"] for entry in manifest["post_parse"])


def render(manifest: dict) -> str:
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def build(artifact: Path) -> str:
    """The manifest for an artifact on disk, read back rather than built.

    The generator has the program and the hash already and calls `ledger`
    directly; this is for the test, which wants to start from the bytes.
    """
    from . import serialize

    program = serialize.loads(artifact.read_text())
    digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
    return render(ledger(program, digest))


__all__ = [
    "ENTRIES",
    "PATH",
    "PARSER_REASON",
    "PARSER_ROOT",
    "THEOREMS",
    "build",
    "call_graph",
    "callees",
    "complete",
    "ledger",
    "reach",
    "render",
]
