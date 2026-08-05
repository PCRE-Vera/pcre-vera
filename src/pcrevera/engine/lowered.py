"""The quantifier lowering, restated in Python over the exported AST.

DESIGN.md section 4.3 is implemented in TIR, inside the code generator, which
emits a body's job several times rather than growing the parser's arena. Two
tools need the same rewrite written down as a function on trees instead.

The migration report needs the *decision* — the blockers, the fit and what
they came to — computed a second time from the parsed tree, so that what the
compiler recorded is reproduced rather than believed.

The Lean bridge needs the *tree*. `Ref.compile` is the emission half of the
compiler restated, and it compiles the tree it is handed; the lowering happens
before that, so the tree the bridge exports is the tree the code generator
really walked. That puts the rewrite inside the pattern-text-to-AST link
THEOREMS.md section 4 already declares tested rather than proved — and the
test is not weak: `lake exe corpuscheck` compiles the exported tree and
compares the bytecode, the region tree, the outcome, the ovector and the usage
against the engine's, case by case, so a rewrite that disagreed with the
compiler by one instruction fails the build.

Both readings are of the arena the engine's own parser produced, and neither
reads `compiler.py`.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..tir.types import CAP
from . import spec
from .compiler import WALK_FUEL

CONSUMING = {"chr", "chrCI", "cls", "any", "anyNoNL"}
ASSERTIONS = {
    "circ", "circM", "doll", "dollE", "dollM",
    "sod", "eod", "eodn", "wordB", "notWordB",
}


class LoweringError(RuntimeError):
    """A tree shape this reading of the lowering has no rule for."""


# --- the pre-check and the dry run ---


@dataclass(frozen=True)
class Size:
    """One subtree's lowered form, and what the pre-check found under it."""

    code: int = 0
    regions: int = 0
    reps: int = 0
    visits: int = 1
    depth: int = 1
    patches: int = 0
    nullable: bool = False
    blockers: int = 0
    needs: bool = False


def _cap(value: int) -> int:
    """The compiler's counters saturate; a saturated count is past every cap,
    which is the answer that keeps the pattern in counter form."""
    return min(value, CAP)


def size(node: list) -> Size:
    kind = node[0]
    if kind == "nul":
        return Size(nullable=True)
    if kind in CONSUMING:
        return Size(code=1)
    if kind == "bsr":
        return Size(code=1, blockers=spec.LB_BSR)
    if kind in ASSERTIONS:
        return Size(code=1, nullable=True)
    if kind == "cat":
        return _kids(node[1], alt=False)
    if kind == "alt":
        return _kids(node[1], alt=True)
    if kind == "grp":
        return _group(node[1], node[2])
    if kind == "rep":
        return _rep(node[1], node[2], size(node[4]))
    raise LoweringError(f"no size rule for a {kind!r} node")


def _kids(kids: list, *, alt: bool) -> Size:
    code = regions = reps = 0
    visits = 1
    depth = patches = 0
    nullable = not alt
    blockers = 0
    needs = False
    for held, kid in enumerate(kids):
        one = size(kid)
        code = _cap(code + one.code)
        regions = _cap(regions + one.regions)
        reps = _cap(reps + one.reps)
        visits = _cap(visits + one.visits)
        depth = max(depth, one.depth)
        # For an alternation, `held` is also how many closing jumps are waiting
        # to be patched while this branch compiles.
        patches = max(patches, (held if alt else 0) + one.patches)
        nullable = nullable or one.nullable if alt else nullable and one.nullable
        blockers |= one.blockers
        needs = needs or one.needs
    visits = _cap(visits + len(kids))
    if alt and len(kids) > 1:
        # Every branch but the last is guarded by a split and leaves by a jump,
        # and the alternation and each of its branches open a region.
        code = _cap(code + 2 * (len(kids) - 1))
        regions = _cap(regions + len(kids) + 1)
    return Size(code, regions, reps, visits, depth + 1, patches,
                nullable, blockers, needs)


def _group(cap: int, body: list) -> Size:
    # A group the parser left empty pushes no job of its own; the exported
    # tree spells that `nul`, since the nil node is index zero and never a
    # child.
    if body == ["nul"]:
        inner, visits, depth = Size(nullable=True), 2, 1
    else:
        inner = size(body)
        visits, depth = _cap(2 + inner.visits), inner.depth + 1
    code = _cap(inner.code + (2 if cap else 0))
    # A group that compiled to nothing has its region taken back off.
    regions = _cap(inner.regions + (1 if code else 0))
    return Size(code, regions, inner.reps, visits, depth, inner.patches,
                inner.nullable, inner.blockers, inner.needs)


def _rep(lo: int, hi: int, body: Size) -> Size:
    if hi == 0:
        # Repeated zero times, nothing under it is compiled or reachable.
        return Size(nullable=True)
    blockers = body.blockers
    if hi == spec.NONE and body.nullable:
        # The star this lowers to would keep the nullable body, which is the
        # one thing lowering cannot fix.
        blockers |= spec.LB_NULLABLE
    exact = lo == 1 and hi == 1
    option = lo == 0 and hi == 1
    star = lo == 0 and hi == spec.NONE
    copies, extra, opened, counters, own = 1, 0, 0, 0, 2
    needs = body.needs
    if option:
        extra, opened = 1, 1
    elif star:
        extra, opened, counters = 4, 1, 1
    elif not exact:
        needs = True
        if hi == spec.NONE:
            copies, extra, opened, counters = lo + 1, 4, 1, 1
            own = lo + 3
        else:
            copies, extra, opened = hi, hi - lo, hi - lo
            own = hi + 2
    return Size(
        code=_cap(copies * body.code + extra),
        regions=_cap(copies * body.regions + opened),
        reps=_cap(copies * body.reps + counters),
        visits=_cap(own + copies * body.visits),
        depth=body.depth + 1,
        patches=body.patches,
        nullable=lo == 0 or body.nullable,
        blockers=blockers,
        needs=needs,
    )


def decide(tree: list, ncap: int, endanchored: bool) -> tuple[int, int, bool]:
    """The blockers, the decision and the fit, read off the tree alone.

    Exactly at a cap is a fit and one past it is the fallback, because every
    array refuses the entry that would take it past its declared maximum, so
    the maximum itself is a length the emitter reaches.
    """
    root = size(tree)
    code = root.code + 1 + (1 if endanchored else 0)
    regs = (ncap + 1) * 2 + root.reps * 2
    fits = (
        code <= spec.MAX_CODE
        and root.regions + 1 <= spec.MAX_REGIONS
        and root.reps <= spec.MAX_REPS
        and regs <= spec.MAX_REGS
        and root.visits <= WALK_FUEL
        and root.depth <= spec.MAX_JOBS
        and root.patches <= spec.MAX_PATCHES
    )
    if not root.needs:
        decision = spec.LOW_NOT_NEEDED
    elif root.blockers:
        decision = spec.LOW_BLOCKED
    elif fits:
        decision = spec.LOW_LOWERED
    else:
        decision = spec.LOW_CAPPED
    return root.blockers, decision, fits


# --- the rewrite ---


def _optionals(body: list, greedy: int, count: int) -> list:
    """The nested optionals a finite bound ends in.

    They nest so that the k-th copy's presence is decided before the
    (k+1)-th's, which is what makes the count preference pcre2's, and they all
    exit at the same place.
    """
    out: list = ["nul"]
    for _ in range(count):
        out = ["rep", 0, 1, greedy, ["cat", [body, out]]]
    return out


def _copies(body: list, tail: list, count: int) -> list:
    """The copies the minimum demands, then whatever the quantifier ends in.

    A concatenation, which opens no region of its own, so the region tree is
    the one the copied constructs and the tail bring with them.
    """
    out = tail
    for _ in range(count):
        out = ["cat", [body, out]]
    return out


def rewrite(node: list) -> list:
    """One subtree in star form, bottom up.

    Recursive because a copied body that still held a counted repetition would
    still hold a counter, and one retained counter makes the whole program
    ineligible.
    """
    kind = node[0]
    if kind == "cat":
        return ["cat", [rewrite(kid) for kid in node[1]]]
    if kind == "alt":
        return ["alt", [rewrite(arm) for arm in node[1]]]
    if kind == "grp":
        return ["grp", node[1], rewrite(node[2])]
    if kind != "rep":
        return node
    lo, hi, greedy = node[1], node[2], node[3]
    body = rewrite(node[4])
    # The spellings that are already in star form keep their own emission:
    # nothing at all, the singleton, the one-split optional, the pure star.
    if hi == 0 or hi == 1 or (lo == 0 and hi == spec.NONE):
        return ["rep", lo, hi, greedy, body]
    if hi == spec.NONE:
        return _copies(body, ["rep", 0, spec.NONE, greedy, body], lo)
    return _copies(body, _optionals(body, greedy, hi - lo), lo)


def tree_for(tree: list, ncap: int, endanchored: bool) -> list:
    """The tree the code generator really walked for this pattern."""
    _, decision, _ = decide(tree, ncap, endanchored)
    return rewrite(tree) if decision == spec.LOW_LOWERED else tree
