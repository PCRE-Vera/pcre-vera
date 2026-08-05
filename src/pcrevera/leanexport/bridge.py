"""The AST bridge the Lean reference engine replays the corpora through.

M6's R-10 wires `R.compile` and `R.run` to the conformance corpora, and the
Lean side has no parser until M10: every theorem quantifies over spec ASTs,
and the step from pattern text to AST is a tested link. This is that link,
written down. For every case of `conformance/corpus.json` and
`conformance/sweep.json` it exports the parsed tree plus the compiled
pattern the engine produced — bytecode, tables, region tree, certificates —
so the Lean executable can compile the same tree, compare the program it
built against the engine's, run both matchers, and hold every recorded
outcome, ovector and usage to its own numbers.

A case the engine refuses at compile time is exported as a skip with the
reason: a compile error is the parser's territory, and the Lean side has
nothing to replay it through.

The tree exported is the one the code generator really walked, which for a
pattern the quantifier lowering of DESIGN.md section 4.3 rewrote is the
lowered one. That is deliberate and it is where the lowering sits in the
trust boundary: `Ref.compile` is the *emission* half of the compiler
restated, and the rewrite ahead of it belongs to the pattern-text-to-AST link
THEOREMS.md section 4 already declares tested rather than proved. The test is
not a weak one — the replay compiles this tree and holds the bytecode, the
region tree, the outcome, the ovector and the usage to the engine's, case by
case — but it is a test, and section 6 of that document prices what proving
it instead would cost.

`hascrlf` is parser output rather than a fact about the tree — the parser
records an explicitly written CR or LF, with pcre2's `[^x]` exception, and
no walk over the AST can recover that. It therefore travels with the tree
as part of the same tested link, and the replay uses it as input rather
than checking it. Everything else here the replay holds the Lean compiler
to.

The output is deterministic — sorted keys, no floats — so its freshness is
checkable the same way the generated backends are.
"""

from __future__ import annotations

import json

from ..engine import lowered, spec
from ..engine.driver import SETUP_STEPS, _blob, items, variant_of
from ..engine.program import program
from ..paths import CONFORMANCE_DIR, GEN_DIR
from ..tir.interp import Cell, Interpreter
from ..tir.types import StructType

BRIDGE_PATH = GEN_DIR / "lean" / "bridge.json"

# The layout-order ordinals the Lean enums mirror; an op or a kind exported
# by number means the two sides can never disagree about a name's spelling.
OPS = (
    "OpChar", "OpCharCI", "OpClass", "OpAny", "OpAnyNoNL", "OpBsr",
    "OpSplit", "OpJump", "OpSave",
    "OpCirc", "OpCircM", "OpDoll", "OpDollE", "OpDollM",
    "OpSod", "OpEod", "OpEodn", "OpWordB", "OpNotWordB",
    "OpRepZero", "OpRepLoop", "OpRepEnter", "OpRepNext",
    "OpAccept",
)
OP_INDEX = {name: index for index, name in enumerate(OPS)}

RKS = ("RkRoot", "RkGroup", "RkBranch", "RkAlt", "RkRepeat")
RK_INDEX = {name: index for index, name in enumerate(RKS)}

LEAVES = {
    "NdChar": "chr",
    "NdCharCI": "chrCI",
    "NdAny": "any",
    "NdAnyNoNL": "anyNoNL",
    "NdBsr": "bsr",
    "NdCirc": "circ",
    "NdCircM": "circM",
    "NdDoll": "doll",
    "NdDollE": "dollE",
    "NdDollM": "dollM",
    "NdSod": "sod",
    "NdEod": "eod",
    "NdEodn": "eodn",
    "NdWordB": "wordB",
    "NdNotWordB": "notWordB",
}


class BridgeError(RuntimeError):
    """The engine handed back a shape this exporter cannot write down."""


def _interp() -> Interpreter:
    return Interpreter(program(), fuel=SETUP_STEPS)


def _compile_bits(pattern: bytes, flags: int, nltype: int, bsr: int):
    """The generated `compile`, called the way the backends call it: raw
    option bits rather than the driver's named options."""
    interp = _interp()
    out = Cell(interp.zero(StructType("Out")))
    interp.call("compile", [_blob(pattern), flags, nltype, bsr, out])
    return out.value


def _parse_work(pattern: bytes, flags: int, nltype: int):
    interp = _interp()
    work = Cell(interp.zero(StructType("Work")))
    interp.call("parse", [_blob(pattern), flags, nltype, work])
    return work.value


def _children(nodes, idx: int) -> list[int]:
    out = []
    child = nodes[idx].fields["first"]
    while child != 0:
        out.append(child)
        child = nodes[child].fields["nxt"]
    return out


def _tree(nodes, classes: bytes, idx: int):
    """One arena node as the Lean AST constructor it stands for.

    Groups and repetitions take exactly one child, because the compiler only
    ever walks their `first`; a parser that attached more would have the
    engine and this export reading different trees, so that is an error
    here rather than a silent truncation.
    """
    nd = nodes[idx]
    kind = variant_of(nd.fields["kind"])
    if kind in LEAVES:
        name = LEAVES[kind]
        if name in ("chr", "chrCI"):
            return [name, nd.fields["val"]]
        return [name]
    if kind == "NdNil":
        return ["nul"]
    if kind == "NdClass":
        base = nd.fields["val"] * 32
        return ["cls", classes[base : base + 32].hex()]
    if kind == "NdConcat":
        return ["cat", [_tree(nodes, classes, c) for c in _children(nodes, idx)]]
    if kind == "NdAlt":
        return ["alt", [_tree(nodes, classes, c) for c in _children(nodes, idx)]]
    if kind in ("NdGroup", "NdRepeat"):
        kids = _children(nodes, idx)
        if len(kids) > 1:
            raise BridgeError(f"{kind} node {idx} has {len(kids)} children")
        body = _tree(nodes, classes, kids[0]) if kids else ["nul"]
        if kind == "NdGroup":
            return ["grp", nd.fields["val"], body]
        return [
            "rep",
            nd.fields["val"],
            nd.fields["aux"],
            1 if nd.fields["opts"] != 0 else 0,
            body,
        ]
    raise BridgeError(f"node kind {kind} has no Lean constructor")


def _poly(value) -> dict:
    return {
        "base": value.fields["base"],
        "coefs": [value.fields[f"c{d}"] for d in spec.DEGREES],
    }


def _cert(value) -> dict:
    return {
        "config": variant_of(value.fields["config"]),
        "complexity": variant_of(value.fields["complexity"]),
        "cost": _poly(value.fields["cost"]),
        "stack": _poly(value.fields["stack"]),
        "trail": _poly(value.fields["trail"]),
        "mem": _poly(value.fields["mem"]),
        "prices": [
            {
                "work": _poly(p.fields["work"]),
                "outs": _poly(p.fields["outs"]),
                "stack": _poly(p.fields["stack"]),
                "trail": _poly(p.fields["trail"]),
            }
            for p in items(value.fields["prices"])
        ],
    }


def _re(value) -> dict:
    return {
        "code": [
            [OP_INDEX[variant_of(i.fields["op"])], i.fields["arg"], i.fields["alt"]]
            for i in items(value.fields["code"])
        ],
        "classes": bytes(items(value.fields["classes"])).hex(),
        "reps": [
            [
                r.fields["lo"],
                r.fields["hi"],
                1 if r.fields["greedy"] else 0,
                r.fields["head"],
                r.fields["body"],
                r.fields["after"],
            ]
            for r in items(value.fields["reps"])
        ],
        "regions": [
            [
                RK_INDEX[variant_of(r.fields["kind"])],
                r.fields["parent"],
                r.fields["lo"],
                r.fields["hi"],
            ]
            for r in items(value.fields["regions"])
        ],
        "ncap": value.fields["ncap"],
        "nregs": value.fields["nregs"],
        # The compile-time options the engine actually compiled with, so the
        # replay can hold the tree it is handed to them rather than assume
        # the case record and the engine read the record the same way.
        "opts": value.fields["opts"],
        "nltype": value.fields["nltype"],
        "bsr": value.fields["bsr"],
        "hascrlf": value.fields["hascrlf"],
        "crfirst": value.fields["crfirst"],
        "pike": bool(value.fields["pike"]),
        "hascert": bool(value.fields["hascert"]),
        "cert": _cert(value.fields["cert"]) if value.fields["hascert"] else None,
        "haspikecert": bool(value.fields["haspikecert"]),
        "pikecert": (
            _cert(value.fields["pikecert"]) if value.fields["haspikecert"] else None
        ),
    }


def _entry(pattern_hex: str, flags: int, nltype: int, bsr: int) -> dict:
    pattern = bytes.fromhex(pattern_hex)
    out = _compile_bits(pattern, flags, nltype, bsr)
    err = out.fields["err"]
    if err != 0:
        return {"skip": err}
    work = _parse_work(pattern, flags, nltype)
    if work.fields["err"] != 0:
        raise BridgeError(
            f"compile accepted what parse refuses: {pattern_hex} -> "
            f"{work.fields['err']}"
        )
    nodes = items(work.fields["nodes"])
    classes = bytes(items(work.fields["classes"]))
    parsed = _tree(nodes, classes, work.fields["root"])
    re = out.fields["re"]
    return {
        "ast": lowered.tree_for(
            parsed, re.fields["ncap"], bool(flags & spec.ENDANCHORED)
        ),
        "re": _re(re),
    }


def build(corpus: dict, sweep: dict) -> dict:
    def keyed(case: dict) -> dict:
        return _entry(
            case["pattern"],
            case.get("flags", 0),
            case.get("newline", 0),
            case.get("bsr", 0),
        )

    return {
        "schema": 1,
        "corpus": {c["name"]: keyed(c) for c in corpus["cases"]},
        "sweep": {
            f"{c['family']}-{c['index']}": keyed(c) for c in sweep["cases"]
        },
        "regressions": {c["name"]: keyed(c) for c in sweep["regressions"]},
    }


def text(corpus: dict, sweep: dict) -> str:
    return json.dumps(build(corpus, sweep), indent=1, sort_keys=True) + "\n"


def main() -> None:
    corpus = json.loads((CONFORMANCE_DIR / "corpus.json").read_text())
    sweep = json.loads((CONFORMANCE_DIR / "sweep.json").read_text())
    BRIDGE_PATH.parent.mkdir(parents=True, exist_ok=True)
    BRIDGE_PATH.write_text(text(corpus, sweep))
    print(f"wrote {BRIDGE_PATH}")


if __name__ == "__main__":
    main()
