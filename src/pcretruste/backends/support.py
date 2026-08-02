"""What both printers need to know before they can print anything.

Everything here is a question about the program rather than about a language,
which is exactly the test for belonging here: what type does this expression
have, which locals are never read, does this body end in a return, which
arguments have to be hoisted, what does the deep-copy helper for this type get
called, what names does the program declare. A printer keeps only the answers
that differ between Go and JavaScript.

The type walk mirrors the reference interpreter's rather than the validator's.
The validator answers "is this well typed", which is a much larger question;
a printer only ever asks "what type is this", of a program that has already
been through the validator, and the interpreter's version of that walk is the
short one.
"""

from __future__ import annotations

import textwrap

from ..tir import ir
from ..tir.types import (
    BOOL,
    U32,
    BYTES,
    EnumType,
    FrozenType,
    Prim,
    StructType,
    Type,
    VecType,
    element_type,
    unfrozen,
)


class Types:
    """The static type of every expression and place inside one function.

    Names do not shadow (TIR-SPEC.md section 2), so one flat table of
    parameters and locals says what every variable in the function means, with
    no scope stack to carry around.
    """

    def __init__(self, program: ir.Program, func: ir.Func) -> None:
        self.p = program
        self.names: dict[str, Type] = {param.name: param.type for param in func.params}
        _locals(func.body, self.names)

    def field(self, base: Type, name: str) -> Type:
        struct = unfrozen(base)
        assert isinstance(struct, StructType)
        decl = self.p.struct_map[struct.name].field(name)
        assert decl is not None, f"{struct.name} has no field {name}"
        return decl.type

    def of(self, e: ir.Expr) -> Type:
        match e:
            case ir.Lit(type=t) | ir.Cast(type=t):
                return t
            case ir.Len() | ir.Cap():
                return U32
            case ir.Compare() | ir.Logical():
                return BOOL
            case ir.Unary(op=op, arg=arg):
                return BOOL if op == "not" else self.of(arg)
            case ir.Shift(arg=arg):
                return self.of(arg)
            case ir.Binary(left=left) | ir.DivRem(left=left):
                return self.of(left)
            case ir.Var(name=name):
                return self.names[name]
            case ir.ConstRef(name=name):
                return self.p.const_map[name].type
            case ir.FieldRead(base=base, name=name):
                container = self.of(base)
                return _through_frozen(self.p, container, self.field(container, name))
            case ir.IndexRead(base=base):
                return element_type(self.of(base))
            case ir.StructVal(type=name):
                return StructType(name)
            case ir.EnumVal(type=name):
                return EnumType(name)
        raise AssertionError(f"unhandled expression: {e!r}")

    def place(self, p: ir.Place) -> Type:
        match p:
            case ir.VarPlace(name=name):
                return self.names[name]
            case ir.FieldPlace(base=base, name=name):
                return self.field(self.place(base), name)
            case ir.IndexPlace(base=base):
                return element_type(self.place(base))
        raise AssertionError(f"unhandled place: {p!r}")


def _through_frozen(program: ir.Program, base: Type, field: Type) -> Type:
    """Reading a field of a frozen struct freezes what would otherwise be linear."""
    if isinstance(base, FrozenType) and program.types.is_linear(field):
        return FrozenType(field)
    return field


def _locals(body: tuple[ir.Stmt, ...], out: dict[str, Type]) -> None:
    for stmt in body:
        match stmt:
            case ir.Let(name=name, type=t):
                out[name] = t
            case ir.If(then=then, otherwise=otherwise):
                _locals(then, out)
                _locals(otherwise, out)
            case ir.While(body=inner):
                _locals(inner, out)
            case ir.Switch(arms=arms, default=default):
                for arm in arms:
                    _locals(arm.body, out)
                if default is not None:
                    _locals(default, out)


def type_tag(t: Type) -> str:
    """A type as an identifier, for naming the deep-copy helpers.

    The name is part of the generated output in both languages, so it is one
    function rather than two that agree by inspection.
    """
    if isinstance(t, (Prim, EnumType, StructType)):
        return t.name
    if isinstance(t, VecType):
        return f"vec_{type_tag(t.elem)}_{t.max}"
    if isinstance(t, FrozenType):
        return f"frozen_{type_tag(t.inner)}"
    raise ValueError(f"not a TIR type: {t!r}")


def declared_names(program: ir.Program) -> list[str]:
    """Every name the program puts in a scope a printer emits into.

    Not only the top-level ones: a parameter, a local or a field is printed
    verbatim too, so a printer's collision guard has to see them all.
    """
    names = [d.name for d in program.enums]
    names += [v for d in program.enums for v in d.variants]
    names += [d.name for d in program.structs]
    names += [f.name for d in program.structs for f in d.fields]
    names += [d.name for d in program.consts]
    for func in program.funcs:
        names.append(func.name)
        names += [p.name for p in func.params]
        names += Types(program, func).names
    return names


def plan_copies(program: ir.Program, t: Type, into: dict[str, Type]) -> str:
    """Register the deep-copy helper for a type, and every one it needs.

    Registering is closed under reachability — a type's elements or fields go
    in before it returns — so the caller can emit `into` as it stands.
    """
    tag = type_tag(t)
    if tag in into:
        return "tir_copy_" + tag
    into[tag] = t
    if not isinstance(t, FrozenType):
        if t == BYTES or isinstance(t, VecType):
            plan_copies(program, element_type(t), into)
        elif isinstance(t, StructType):
            for field in program.struct_map[t.name].fields:
                plan_copies(program, field.type, into)
    return "tir_copy_" + tag


def banner(origin: str, sha256: str, summary: str, scope: str, trap: str) -> list[str]:
    """The header every generated file carries, as comment lines without the //.

    TIR-SPEC.md section 16 asks for the artifact's SHA-256 in a header comment
    and in a constant, so the wording is a shared obligation rather than each
    printer's taste.
    """
    lines = [
        f"Code generated from {origin}. DO NOT EDIT.",
        "",
        "Artifact SHA-256:",
        f"  {sha256}",
        "",
    ]
    lines += textwrap.wrap(summary, 74)
    lines += [
        "",
        f"The {scope} holds the program and the printer's own tir_ helpers and",
        "nothing else, which is what lets TIR names be printed verbatim.",
        "",
    ]
    lines += textwrap.wrap(trap, 76)
    return lines


def resolving_traps(arg: ir.Arg) -> bool:
    """Whether resolving a call argument can trap before the call happens.

    Only an indexed `inout` place can: its bounds check runs while the argument
    is being resolved, which is before an argument written after it.
    """
    if not isinstance(arg, ir.InoutArg):
        return False
    place = arg.place
    while True:
        match place:
            case ir.IndexPlace():
                return True
            case ir.FieldPlace(base=base):
                place = base
            case _:
                return False


def hoisted(args: tuple[ir.Arg, ...]) -> list[bool]:
    """Which call arguments have to be evaluated into a temporary first.

    Section 13 resolves arguments left to right. An `in` argument left inline
    would be evaluated inside the call, which is after the bounds check any
    later indexed `inout` place performs, so one with such a neighbour is
    hoisted. The scan runs right to left so it costs one pass rather than one
    per argument.
    """
    out = [False] * len(args)
    waiting = False
    for index in range(len(args) - 1, -1, -1):
        out[index] = waiting and isinstance(args[index], ir.InArg)
        waiting = waiting or resolving_traps(args[index])
    return out


def reads(func: ir.Func) -> set[str]:
    """The names that appear as a value somewhere in the function.

    Deliberately the narrow reading: only `{"var": ...}` counts. A name this
    misses is one the Go printer will declare and then blank-assign, which is
    always legal; a name it wrongly included would be a compile error, so the
    error stays on the harmless side.
    """
    found: set[str] = set()

    def walk(node: object) -> None:
        if isinstance(node, ir.Var):
            found.add(node.name)
        if isinstance(node, tuple):
            for item in node:
                walk(item)
            return
        if not hasattr(node, "__dataclass_fields__"):
            return
        for name in type(node).__dataclass_fields__:
            walk(getattr(node, name))

    walk(func.body)
    return found


def terminates(body: tuple[ir.Stmt, ...]) -> bool:
    """Whether a body ends in a statement Go calls terminating.

    Go's own list is what this transcribes, restricted to the shapes a printer
    emits: a return, an if with both arms terminating, and a switch with a
    default whose every arm terminates. A `while` is never one of them, because
    the printer always emits a loop condition and Go's rule wants a loop
    without one.
    """
    if not body:
        return False
    match body[-1]:
        case ir.Return():
            return True
        case ir.If(then=then, otherwise=otherwise):
            return bool(otherwise) and terminates(then) and terminates(otherwise)
        case ir.Switch(arms=arms, default=default):
            if default is None:
                return False
            return terminates(default) and all(terminates(arm.body) for arm in arms)
    return False


def has_jump(body: tuple[ir.Stmt, ...]) -> bool:
    """Whether a loop body breaks or continues out of itself.

    Nested loops own their own jumps, so the walk stops at one.
    """
    for stmt in body:
        match stmt:
            case ir.Break() | ir.Continue():
                return True
            case ir.If(then=then, otherwise=otherwise):
                if has_jump(then) or has_jump(otherwise):
                    return True
            case ir.Switch(arms=arms, default=default):
                if any(has_jump(arm.body) for arm in arms):
                    return True
                if default is not None and has_jump(default):
                    return True
    return False


__all__ = [
    "Types",
    "banner",
    "declared_names",
    "has_jump",
    "hoisted",
    "plan_copies",
    "reads",
    "resolving_traps",
    "terminates",
    "type_tag",
]
