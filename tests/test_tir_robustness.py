"""The validator is the boundary, checked by breaking the artifact in every way.

Every module downstream of `validate` is written for programs that passed it,
and says so. That claim is only worth something if a program that did not pass
cannot reach them, and if a program that did pass cannot make them fall over in
some way that is neither a rule violation nor a trap.

So: take the golden artifact, mutate it one piece at a time — every string,
every number, every list element, every object member, and, in the tree sweep
below, every node swapped for one of another kind — and insist that each mutant
either fails to decode, fails to validate with a numbered rule, or runs to a
TIR outcome. Anything else is a hole in the boundary. The mutations are
enumerated rather than random, so a failure is reproducible by index.
"""

from __future__ import annotations

import json
from dataclasses import fields, is_dataclass, replace

import pytest
import toy

from pcretruste.tir import (
    Cell,
    TirSyntaxError,
    Trap,
    ValidationError,
    dumps,
    ir,
    loads,
    run,
    validate,
)
from pcretruste.tir.interp import OutOfFuel, VariantViolation
from pcretruste.tir.types import (
    BOOL,
    BYTES,
    COUNTER,
    I32,
    U8,
    U32,
    PRIMS,
    EnumDecl,
    EnumType,
    FrozenType,
    Prim,
    StructType,
    VecType,
)

TYPE_KINDS = (Prim, VecType, FrozenType, EnumType, StructType)

TYPES = (
    BOOL,
    U8,
    I32,
    U32,
    COUNTER,
    BYTES,
    VecType(U8, 4),
    FrozenType(BYTES),
    StructType("Task"),
    EnumType("Phase"),
)

DOCUMENT = json.loads(toy.GOLDEN.read_text())

# A mutant that validates still has to be run to be interesting, and a fuel
# bound is what keeps a mutant loop from being the end of the test session.
FUEL = 5_000

TIR_OUTCOMES = (Trap, VariantViolation, OutOfFuel)


def replacements(value: object) -> list[object]:
    """What to put in place of one leaf, chosen to be wrong in different ways."""
    if isinstance(value, bool):
        return [not value, 0]
    if isinstance(value, int):
        return [-1, 0, 2**40]
    if isinstance(value, str):
        return ["wat", ""]
    return []


def mutants(node: object, path: tuple = ()):
    """Every one-leaf mutation of the document, as (path, replacement) pairs."""
    if isinstance(node, dict):
        for key, value in node.items():
            yield from mutants(value, (*path, key))
            yield (path, key)  # dropping the member outright
    elif isinstance(node, list):
        for index, value in enumerate(node):
            yield from mutants(value, (*path, index))
        if node:
            yield (path, 0)
    else:
        for replacement in replacements(node):
            yield (path, replacement)


def apply(document: object, path: tuple, change: object) -> object:
    """A copy of the document with one leaf replaced, or one member dropped."""
    document = json.loads(json.dumps(document))
    target = document
    for step in path:
        target = target[step]
    if isinstance(target, dict) and isinstance(change, str) and change in target:
        del target[change]
    elif isinstance(target, list) and isinstance(change, int) and change < len(target):
        del target[change]
    else:
        parent = document
        for step in path[:-1]:
            parent = parent[step]
        parent[path[-1]] = change
    return document


MUTANTS = list(mutants(DOCUMENT))


def test_the_sweep_is_worth_running():
    assert len(MUTANTS) > 500


@pytest.mark.parametrize("index", range(len(MUTANTS)))
def test_a_mutated_artifact_never_escapes_the_boundary(index):
    path, change = MUTANTS[index]
    document = apply(DOCUMENT, path, change)
    try:
        program = loads(json.dumps(document))
    except TirSyntaxError:
        return
    try:
        validate(program)
    except ValidationError:
        return

    # It validated, so it is a TIR program and running it must reach a TIR
    # outcome. A signature the caller no longer matches is the caller's
    # problem, not the program's.
    if "fib" not in program.func_map:
        return
    try:
        run(program, "fib", [7, Cell(0)], fuel=FUEL)
    except (*TIR_OUTCOMES, TypeError):
        return


# --- the same sweep, one level lower ---
#
# Mutating the text exercises the reader hardest: most of what it produces is
# never a program at all. Mutating the tree goes straight past the reader, which
# is where the interesting failures live, since every module downstream of
# `validate` is written for programs that got through it.


# Nodes to drop into a slot that wants something else: a place where an
# expression belongs, an enum among the structs, an integer among the
# statements. Swapping leaves is not enough on its own, because the leaf swaps
# never change what *kind* of thing sits in a field, which is exactly what a
# program built straight from `ir` is free to get wrong.
FOREIGN = (
    ir.VarPlace("v"),
    ir.Lit(U32, 0),
    ir.Arm("A", ()),
    ir.InArg(ir.Lit(U32, 0)),
    ir.EnumConst("A"),
    EnumDecl("Wat", ("A",)),
    Prim("word"),
    17,
)


def swaps(value: object) -> list[object]:
    if isinstance(value, bool):
        return [not value]
    if isinstance(value, int):
        # The float matters: three slots take a number that no rule requires to
        # be an integer until it looks, and every other slot takes none at all.
        return [-1, 0, 2**40, 1.5]
    if isinstance(value, str):
        return ["wat", "n", 1.5]
    if isinstance(value, TYPE_KINDS):
        return [t for t in TYPES if t != value][:3]
    if value is None:
        return [ir.Lit(U32, 0)]
    return []


def tree_mutants(node: object):
    yield from swaps(node)
    if is_dataclass(node) and not isinstance(node, type):
        yield from (other for other in FOREIGN if type(other) is not type(node))
        for f in fields(node):
            for mutant in tree_mutants(getattr(node, f.name)):
                try:
                    yield replace(node, **{f.name: mutant})
                except Exception:
                    pass  # a __post_init__ that refuses is a rejection too
    elif isinstance(node, tuple):
        yield list(node)  # a list where the canonical form wants a tuple
        for index, item in enumerate(node):
            for mutant in tree_mutants(item):
                yield node[:index] + (mutant,) + node[index + 1 :]
            yield node[:index] + node[index + 1 :]


TREE_MUTANTS = list(tree_mutants(toy.build()))


@pytest.mark.parametrize("index", range(len(TREE_MUTANTS)))
def test_a_mutated_program_never_escapes_the_boundary(index):
    program = TREE_MUTANTS[index]
    if not isinstance(program, ir.Program):
        return
    try:
        validate(program)
    except ValidationError:
        return

    # It validated, so two things must hold: it survives a round trip through
    # the canonical text, and running it reaches a TIR outcome.
    assert loads(dumps(program)) == program
    if "fib" not in program.func_map:
        return
    try:
        run(program, "fib", [7, Cell(0)], fuel=FUEL)
    except (*TIR_OUTCOMES, TypeError):
        return


def rebuilt(node: object) -> object:
    """The same tree with every primitive type freshly built rather than shared."""
    if isinstance(node, Prim):
        return Prim(str(node.name))
    if is_dataclass(node) and not isinstance(node, type):
        return replace(node, **{f.name: rebuilt(getattr(node, f.name)) for f in fields(node)})
    if isinstance(node, tuple):
        return tuple(rebuilt(item) for item in node)
    return node


def every_prim(node: object):
    if isinstance(node, Prim):
        yield node
    elif is_dataclass(node) and not isinstance(node, type):
        for f in fields(node):
            yield from every_prim(getattr(node, f.name))
    elif isinstance(node, tuple):
        for item in node:
            yield from every_prim(item)


def test_a_program_whose_primitives_are_all_rebuilt_behaves_identically():
    """Nothing anywhere may compare a type by identity.

    The reader hands out the six constants, but the DSL and any caller of `ir`
    can spell one out, and a `Prim("bytes")` that answered "not linear" would
    walk past every rule linearity is made of. One narrow test per helper would
    cover the helpers somebody remembered; a whole program covers the twenty or
    so places that ask a type anything.
    """
    program = toy.build()
    twin = rebuilt(program)
    assert twin == program

    primitives = list(every_prim(twin))
    assert primitives, "the toy program names no primitive type, so this proves nothing"
    assert all(t is not PRIMS[t.name] for t in primitives)

    validate(twin)
    assert dumps(twin) == dumps(program)
    out = Cell(0)
    assert run(twin, "fib", [7, out], fuel=FUEL) is True
    assert out.value == toy.fibonacci(7)


def test_the_unmutated_artifact_still_passes_the_same_gauntlet():
    program = loads(json.dumps(DOCUMENT))
    validate(program)
    out = Cell(0)
    assert run(program, "fib", [7, out], fuel=FUEL) is True
    assert out.value == toy.fibonacci(7)
