"""The TIR validator: rules V-002 to V-043 of TIR-SPEC.md section 15.

V-001, the schema version, is checked when the artifact is read, because a
decoded program no longer carries a version to check.

The validator stops at the first problem and names the rule it broke. That is
a deliberate choice over collecting everything: once one expression has no
type, every check downstream of it reports damage rather than causes, and a
list of eleven consequences is worse reading than the one cause.

`_check_shapes` owns rule V-042 and runs first. Every other pass here is
written for a tree it has already been through, and so may read a body as a
list of statements, a name as a string, and a type as one of the five the
document defines.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass, fields, is_dataclass
from typing import NoReturn

from . import ir
from .types import (
    BOOL,
    BYTES,
    CEILING,
    COUNTER,
    I32,
    PRIMS,
    INT_RANGE,
    INT_WIDTH,
    U8,
    U32,
    EnumDecl,
    EnumType,
    Field,
    FrozenType,
    Prim,
    StructDecl,
    StructType,
    Type,
    TypeEnv,
    VecType,
    element_type,
    is_sequence,
    unfrozen,
)

CASTABLE_TO = (U8, I32, U32, COUNTER)
CASTABLE_FROM = (BOOL, U8, I32, U32, COUNTER)

# What each operator family accepts. The comparison split is the one worth
# reading twice: ordering enum variants would make an ordinal load-bearing in
# every program that used one.
ARITH_TYPES = (U8, I32, U32, COUNTER)
BITWISE_TYPES = (U8, I32, U32)
SHIFT_TYPES = {"shl": (U8, I32, U32), "shr": (U8, U32), "sar": (I32,)}
ORDER_TYPES = (U8, I32, U32, COUNTER)

# The three slots where a number that is not an integer gets past the shape
# pass, because saying so is the job of the rule that owns the payload.
NUMERIC_PAYLOADS = {("Lit", "value"), ("Shift", "count"), ("VecType", "max")}


class ValidationError(ValueError):
    def __init__(self, rule: str, message: str) -> None:
        super().__init__(f"{rule}: {message}")
        self.rule = rule
        self.message = message


def validate(program: ir.Program) -> None:
    """Raise ValidationError unless the program satisfies every rule."""
    _Validator(program).run()


# --- access paths, for the disjointness rules ---

Projection = tuple[str, object]
Path = tuple[str, tuple[Projection, ...]]


def provably_disjoint(a: Path, b: Path) -> bool:
    """TIR-SPEC.md section 9.2.

    "Provably" is the operative word: two index projections settle nothing
    unless both are literals, whatever the runtime values would have been.
    """
    if a[0] != b[0]:
        return True
    for left, right in zip(a[1], b[1]):
        if left[0] != right[0]:
            # A field against an index cannot arise from two well-typed paths
            # with the same root; report an overlap rather than invent a
            # disjointness the types do not support.
            return False
        if left[0] == "index" and (left[1] is None or right[1] is None):
            return False
        if left[1] != right[1]:
            return True
        # They agree so far, which settles nothing on its own.
    # One path ran out: a container and something inside it.
    return False


def _literal_index(e: ir.Expr) -> int | None:
    return e.value if isinstance(e, ir.Lit) and e.type == U32 else None


def _chain(e: ir.Expr) -> Path | None:
    """The access path of an expression, when it is one, and None when it is not.

    A field of a struct literal, or an index into a constant, is a perfectly
    good expression and no path at all.
    """
    match e:
        case ir.Var(name=name):
            return (name, ())
        case ir.FieldRead(base=base, name=name):
            inner = _chain(base)
            return None if inner is None else (inner[0], inner[1] + (("field", name),))
        case ir.IndexRead(base=base, index=index):
            inner = _chain(base)
            if inner is None:
                return None
            return (inner[0], inner[1] + (("index", _literal_index(index)),))
    return None


def place_path(p: ir.Place) -> Path:
    match p:
        case ir.VarPlace(name=name):
            return (name, ())
        case ir.FieldPlace(base=base, name=name):
            inner = place_path(base)
            return (inner[0], inner[1] + (("field", name),))
        case ir.IndexPlace(base=base, index=index):
            inner = place_path(base)
            return (inner[0], inner[1] + (("index", _literal_index(index)),))
    raise AssertionError(f"not a place: {p!r}")


def _subexpressions(e: ir.Expr) -> Iterator[ir.Expr]:
    match e:
        case ir.FieldRead(base=base):
            yield base
        case ir.IndexRead(base=base, index=index):
            yield base
            yield index
        case ir.Len(arg=arg) | ir.Cap(arg=arg) | ir.Unary(arg=arg) | ir.Cast(arg=arg):
            yield arg
        case ir.Shift(arg=arg):
            yield arg
        case (
            ir.Binary(left=left, right=right)
            | ir.Compare(left=left, right=right)
            | ir.Logical(left=left, right=right)
        ):
            yield left
            yield right
        case ir.DivRem(left=left, right=right, fallback=fallback):
            yield left
            yield right
            yield fallback
        case ir.StructVal(fields=fields):
            for _, value in fields:
                yield value


def read_paths(e: ir.Expr) -> list[Path]:
    """Every access path an expression reads, chains and index expressions alike."""
    out: list[Path] = []
    _collect_reads(e, out)
    return out


def _collect_reads(e: ir.Expr, out: list[Path]) -> None:
    path = _chain(e)
    if path is None:
        for sub in _subexpressions(e):
            _collect_reads(sub, out)
        return
    out.append(path)
    # The chain is one path; the indices along it are reads of their own, which
    # is what catches f(inout i, in v[i]).
    node: ir.Expr = e
    while True:
        if isinstance(node, ir.IndexRead):
            _collect_reads(node.index, out)
            node = node.base
        elif isinstance(node, ir.FieldRead):
            node = node.base
        else:
            return


def place_read_paths(p: ir.Place) -> list[Path]:
    """The paths a place reads while resolving itself, which is its indices."""
    out: list[Path] = []
    node: ir.Place = p
    while True:
        if isinstance(node, ir.IndexPlace):
            _collect_reads(node.index, out)
            node = node.base
        elif isinstance(node, ir.FieldPlace):
            node = node.base
        else:
            return out


def _structs_in(t: Type) -> Iterator[str]:
    """Every struct a type reaches, through frozen and through vec elements too.

    A cycle closed by a frozen field is still a cycle: `frozen<T>`'s zero value
    is built from T's, so a struct that reaches itself that way has no zero
    value even though its storage size is finite.
    """
    match t:
        case StructType(name=name):
            yield name
        case FrozenType(inner=inner):
            yield from _structs_in(inner)
        case VecType(elem=elem):
            yield from _structs_in(elem)


def _show(path: Path) -> str:
    out = path[0]
    for kind, value in path[1]:
        out += f".{value}" if kind == "field" else f"[{'?' if value is None else value}]"
    return out


# --- scopes ---


@dataclass(frozen=True)
class Binding:
    type: Type
    writable: bool


class Scope:
    """Every name in a function, plus which of them are currently live.

    Names never shadow, so one flat dictionary answers "what is this name" and
    a separate live set answers "does it exist yet".
    """

    def __init__(self) -> None:
        self.bindings: dict[str, Binding] = {}
        self.live: set[str] = set()

    def declare(self, name: str, binding: Binding) -> None:
        self.bindings[name] = binding
        self.live.add(name)

    def lookup(self, name: str) -> Binding | None:
        return self.bindings.get(name) if name in self.live else None


# How a body ends: falling out of it, returning, or jumping out of a loop.
FALLS_THROUGH = "falls"
RETURNS = "returns"
JUMPS = "jumps"


def _combine(a: str, b: str) -> str:
    if a == FALLS_THROUGH or b == FALLS_THROUGH:
        return FALLS_THROUGH
    return RETURNS if a == RETURNS and b == RETURNS else JUMPS


class _Validator:
    def __init__(self, program: ir.Program) -> None:
        self.p = program
        self.types: TypeEnv = program.types
        self.top_level: set[str] = set()

    def run(self) -> None:
        self._check_shapes()
        self._check_names()
        self._check_enums()
        self._check_top_level_names()
        self._check_structs()
        self._check_constants()
        self._check_signatures()
        self._check_call_graph()
        for func in self.p.funcs:
            self._check_function(func)

    def fail(self, rule: str, message: str) -> NoReturn:
        raise ValidationError(rule, message)

    # --- shapes ---

    def _check_shapes(self) -> None:
        """Rule V-042, and the first pass, because everything after it assumes a tree.

        Every later pass reads a field expecting a TIR node there — a statement
        in a body, a place under an assignment, one of section 3.1's types
        beside a name. The reader can only build such a tree, but a program
        assembled straight from `ir` can hold anything anywhere, and a pass that
        met a surprise would raise whatever Python raises rather than name a
        rule. So the shapes are settled before the type environment, the name
        maps, or any of the rules below are consulted.

        What a payload *means* is not this pass's business: whether a literal's
        value fits its type is V-014, a shift count V-015, a vec maximum V-007,
        a constant's value V-012.

        Nesting depth (rule V-044) is checked here too, and has to be: past a
        few hundred levels this walk is what runs out of stack, so the answer
        has to be given on the way down rather than after.
        """
        self._members(self.p.enums, EnumDecl, "the enum list")
        self._members(self.p.structs, StructDecl, "the struct list")
        self._members(self.p.consts, ir.Const, "the constant list")
        self._members(self.p.funcs, ir.Func, "the function list")

        for decl in self.p.enums:
            self._tuple(decl.variants, f"the variants of enum {decl.name}")
        for decl in self.p.structs:
            self._members(decl.fields, Field, f"the fields of struct {decl.name}")
            for f in decl.fields:
                self._shape_type(f.type, f"field {decl.name}.{f.name}")
        for const in self.p.consts:
            what = f"constant {const.name}"
            self._shape_type(const.type, what)
            self._shape_const(const.value, what, 1)
        for func in self.p.funcs:
            what = f"function {func.name}"
            self._members(func.params, ir.Param, f"the parameters of {what}")
            for p in func.params:
                self._shape_type(p.type, f"parameter {func.name}.{p.name}")
            if func.ret is not None:
                self._shape_type(func.ret, f"the return type of {func.name}")
            self._shape_body(func.body, f"in {func.name!r}", 1)

        self._check_leaves()

    def _check_leaves(self) -> None:
        """Every leaf of a program tree is a name, a number, a byte string or nothing.

        Names are resolved by dictionary lookup and operators by membership in
        a tuple, and both will cheerfully match an object that merely claims to
        equal a string. That object then reaches the serializer, which has
        nothing to write, and the failure lands well past the boundary. The
        reader cannot build such a thing; this is what says so for a tree that
        never went through it.

        Whether a number is the *right* number belongs to the rule that governs
        the payload — which is why the three slots below are the only ones where
        something other than an integer gets that far.
        """
        for owner, field, leaf in _leaves(self.p):
            if leaf is None or isinstance(leaf, (str, int, bytes)):
                continue
            if isinstance(leaf, float) and (owner, field) in NUMERIC_PAYLOADS:
                continue
            self.fail(
                "V-042", f"{owner}.{field} holds {leaf!r}, which is no kind of TIR payload"
            )

    def _tuple(self, value: object, what: str) -> tuple:
        if not isinstance(value, tuple):
            self.fail("V-042", f"{what} is {value!r}, which is not a list")
        return value

    def _members(self, value: object, wanted: type | tuple[type, ...], what: str) -> None:
        for item in self._tuple(value, what):
            if not isinstance(item, wanted):
                self.fail("V-042", f"{what} holds {item!r}, which does not belong there")

    def _shape_type(self, t: object, what: str) -> None:
        match t:
            case Prim(name=name):
                if name not in PRIMS:
                    self.fail("V-042", f"{what} names the type {name!r}, which does not exist")
            case EnumType() | StructType():
                pass
            case VecType(elem=elem):
                self._shape_type(elem, what)
            case FrozenType(inner=inner):
                self._shape_type(inner, what)
            case _:
                self.fail("V-042", f"{what} is {t!r}, which is not a TIR type")

    def _deep(self, what: str, depth: int) -> None:
        if depth > ir.MAX_DEPTH:
            self.fail("V-044", f"{what} nests more than {ir.MAX_DEPTH} levels deep")

    def _shape_const(self, value: object, what: str, depth: int) -> None:
        self._deep(what, depth)
        if isinstance(value, ir.StructConst):
            self._pairs(value.fields, what)
            for name, inner in value.fields:
                self._shape_const(inner, f"{what}.{name}", depth + 1)
        elif isinstance(value, ir.VecConst):
            self._tuple(value.elems, f"the elements of {what}")
            for index, elem in enumerate(value.elems):
                self._shape_const(elem, f"{what}[{index}]", depth + 1)

    def _shape_body(self, body: object, what: str, depth: int) -> None:
        if not isinstance(body, tuple):
            self.fail("V-042", f"{what}, a body is {body!r}, not a list of statements")
        for stmt in body:
            self._shape_stmt(stmt, what, depth)

    def _shape_stmt(self, stmt: object, what: str, depth: int) -> None:
        self._deep(what, depth)
        inner = depth + 1
        match stmt:
            case ir.Let(type=t, init=init):
                self._shape_type(t, what)
                if init is not None:
                    self._shape_expr(init, what, inner)
            case (
                ir.Take(dest=one, src=two)
                | ir.Freeze(dest=one, src=two)
                | ir.Swap(a=one, b=two)
                | ir.Pop(seq=one, dest=two)
            ):
                self._shape_place(one, what, inner)
                self._shape_place(two, what, inner)
            case (
                ir.Assign(place=place, value=value)
                | ir.Push(seq=place, value=value)
                | ir.Copy(dest=place, src=value)
                | ir.Truncate(seq=place, length=value)
                | ir.Reserve(seq=place, cap=value)
            ):
                self._shape_place(place, what, inner)
                self._shape_expr(value, what, inner)
            case ir.If(cond=cond, then=then, otherwise=otherwise):
                self._shape_expr(cond, what, inner)
                self._shape_body(then, what, inner)
                self._shape_body(otherwise, what, inner)
            case ir.While(cond=cond, variant=variant, body=body):
                self._shape_expr(cond, what, inner)
                self._shape_expr(variant, what, inner)
                self._shape_body(body, what, inner)
            case ir.Switch(value=value, arms=arms, default=default):
                self._shape_expr(value, what, inner)
                self._members(arms, ir.Arm, f"{what}, the arms of a switch")
                for arm in arms:
                    self._shape_body(arm.body, what, inner)
                if default is not None:
                    self._shape_body(default, what, inner)
            case ir.Break() | ir.Continue():
                pass
            case ir.Return(value=value):
                if value is not None:
                    self._shape_expr(value, what, inner)
            case ir.Call(args=args, dest=dest):
                self._members(args, ir.Arg, f"{what}, the arguments of a call")
                for arg in args:
                    if isinstance(arg, ir.InArg):
                        self._shape_expr(arg.expr, what, inner)
                    else:
                        self._shape_place(arg.place, what, inner)
                if dest is not None:
                    self._shape_place(dest, what, inner)
            case _:
                self.fail("V-042", f"{what}, {stmt!r} is not a TIR statement")

    def _shape_expr(self, e: object, what: str, depth: int) -> None:
        self._deep(what, depth)
        if not isinstance(e, ir.Expr):
            self.fail("V-042", f"{what} holds {e!r}, which is not a TIR expression")
        # The two fields no child edge reaches, and then the edges themselves,
        # which `_subexpressions` already enumerates for the disjointness rules.
        match e:
            case ir.Lit(type=t) | ir.Cast(type=t):
                self._shape_type(t, what)
            case ir.StructVal(fields=fields):
                self._pairs(fields, what)
        for sub in _subexpressions(e):
            self._shape_expr(sub, what, depth + 1)

    def _shape_place(self, place: object, what: str, depth: int) -> None:
        self._deep(what, depth)
        match place:
            case ir.VarPlace():
                pass
            case ir.FieldPlace(base=base):
                self._shape_place(base, what, depth + 1)
            case ir.IndexPlace(base=base, index=index):
                self._shape_place(base, what, depth + 1)
                self._shape_expr(index, what, depth + 1)
            case _:
                self.fail("V-042", f"{what}, {place!r} is not a TIR place")

    # --- declarations ---

    def _check_names(self) -> None:
        """Every name a program declares is an identifier the artifact can carry.

        The reader enforces this on the way in; the validator has to as well, or
        a program the DSL built would validate and then fail to re-read, which
        makes `validate` a weaker statement than it looks.
        """

        def check(name: object, what: str) -> None:
            if (
                not isinstance(name, str)
                or not ir.IDENTIFIER.match(name)
                or len(name) > ir.MAX_IDENTIFIER
            ):
                self.fail("V-041", f"{what} is not an identifier: {name!r}")
            if name in ir.RESERVED:
                self.fail("V-043", f"{what} is {name!r}, which a target language keeps")
            for prefix in ir.RESERVED_PREFIXES:
                if name.startswith(prefix):
                    self.fail(
                        "V-043",
                        f"{what} starts with {prefix!r}, which the printers keep",
                    )

        for decl in self.p.enums:
            check(decl.name, "an enum name")
            for variant in decl.variants:
                check(variant, f"a variant of {decl.name}")
        for struct in self.p.structs:
            check(struct.name, "a struct name")
            for f in struct.fields:
                check(f.name, f"a field name in {struct.name}")
        for const in self.p.consts:
            check(const.name, "a constant name")
        for func in self.p.funcs:
            check(func.name, "a function name")
            for p in func.params:
                check(p.name, f"a parameter name in {func.name}")
            for stmt in _walk(func.body):
                if isinstance(stmt, ir.Let):
                    check(stmt.name, f"a local name in {func.name}")

    def _check_top_level_names(self) -> None:
        """One namespace, enum variants included.

        A variant is a package-level constant in Go and a module-level one in
        JavaScript, so it shares the scope the other declarations land in and
        two enums cannot both spell a variant `Add`. Repeats *within* one enum
        are V-004 and have already been refused, which is why this pass runs
        second.

        The namespace it collects is what V-038 then compares parameters and
        locals against, so there is one enumeration of it rather than two.
        """
        seen: dict[str, str] = {}

        def take(name: str, kind: str) -> None:
            if name in seen:
                self.fail("V-002", f"{name!r} is both {seen[name]} and {kind}")
            seen[name] = kind

        for decl in self.p.enums:
            take(decl.name, "an enum")
            for variant in decl.variants:
                take(variant, f"a variant of {decl.name}")
        for struct in self.p.structs:
            take(struct.name, "a struct")
        for const in self.p.consts:
            take(const.name, "a constant")
        for func in self.p.funcs:
            take(func.name, "a function")

        self.top_level = set(seen)

    def _check_enums(self) -> None:
        for decl in self.p.enums:
            if not decl.variants:
                self.fail("V-004", f"enum {decl.name!r} declares no variants")
            if len(set(decl.variants)) != len(decl.variants):
                self.fail("V-004", f"enum {decl.name!r} repeats a variant name")

    def _check_structs(self) -> None:
        for decl in self.p.structs:
            if not decl.fields:
                self.fail("V-005", f"struct {decl.name!r} declares no fields")
            names = [f.name for f in decl.fields]
            if len(set(names)) != len(names):
                self.fail("V-005", f"struct {decl.name!r} repeats a field name")

        # Direct containment is the only cycle that can leave a struct without
        # a size: a cycle through a vec needs a linear element type, which
        # V-006 rejects on its own. This runs before anything asks a type
        # whether it is linear, since that question walks the same edges.
        self._check_acyclic(
            [decl.name for decl in self.p.structs],
            self._contained_structs,
            "V-005",
            "a chain of structs",
        )

        for decl in self.p.structs:
            for f in decl.fields:
                self._check_type(f.type, f"field {decl.name}.{f.name}")

    def _contained_structs(self, name: str) -> list[str]:
        decl = self.p.struct_map.get(name)
        if decl is None:
            self.fail("V-003", f"struct {name!r} is not declared")
        return [reached for f in decl.fields for reached in _structs_in(f.type)]

    def _check_acyclic(
        self,
        roots: Sequence[str],
        successors: Callable[[str], list[str]],
        rule: str,
        subject: str,
    ) -> None:
        """A depth-first walk of a graph of names, iterative, memoized, and bounded.

        All three matter. Without the memo, a node reached along two edges is
        walked once per edge and a chain of diamonds costs 2^n. Without the
        explicit stack, a chain a thousand long overflows Python's. And the
        bound is what the passes downstream need: the interpreter recurses per
        call, and linearity, storage size and the zero value each recurse per
        containment step, so an unbounded chain is a stack overflow waiting in
        somebody else's module.

        The two graphs it serves are the structs a struct contains and the
        functions a function calls.
        """
        settled: set[str] = set()
        for root in roots:
            if root in settled:
                continue
            path = [root]
            on_path = {root}
            stack = [iter(successors(root))]
            while stack:
                reached = next(stack[-1], None)
                if reached is None:
                    stack.pop()
                    on_path.discard(path[-1])
                    settled.add(path.pop())
                elif reached in on_path:
                    cycle = (*path[path.index(reached) :], reached)
                    self.fail(rule, f"{subject} closes on itself: {' -> '.join(cycle)}")
                elif reached not in settled:
                    path.append(reached)
                    on_path.add(reached)
                    if len(path) > ir.MAX_DEPTH:
                        self.fail(
                            "V-044",
                            f"{subject} is more than {ir.MAX_DEPTH} long: "
                            f"{' -> '.join((path[0], '...', path[-1]))}",
                        )
                    stack.append(iter(successors(reached)))

    def _check_type(self, t: Type, what: str) -> None:
        match t:
            case Prim(name=name):
                if name not in PRIMS:
                    self.fail("V-042", f"{what} names the type {name!r}, which does not exist")
            case EnumType(name=name):
                if name not in self.p.enum_map:
                    self.fail("V-003", f"{what} names enum {name!r}, which is not declared")
            case StructType(name=name):
                if name not in self.p.struct_map:
                    self.fail("V-003", f"{what} names struct {name!r}, which is not declared")
            case VecType(elem=elem, max=maximum):
                self._check_type(elem, what)
                if self.types.is_linear(elem):
                    self.fail("V-006", f"{what} holds {elem}, which is linear")
                if elem == U8 and maximum == CEILING:
                    self.fail(
                        "V-010", f"{what} is a full-width u8 sequence, which is spelled 'bytes'"
                    )
                limit = self.types.max_capacity(elem)
                if type(maximum) is not int or not 1 <= maximum <= limit:
                    self.fail(
                        "V-007",
                        f"{what} declares a maximum of {maximum}, outside 1 .. {limit} "
                        f"for elements of {self.types.sizeof(elem)} IR bytes",
                    )
            case FrozenType(inner=inner):
                if isinstance(inner, FrozenType):
                    self.fail("V-009", f"{what} freezes a frozen type")
                self._check_type(inner, what)
                if not self.types.is_linear(inner):
                    self.fail("V-008", f"{what} freezes {inner}, which is already copyable")
            case _:
                self.fail("V-042", f"{what} is {t!r}, which is not a TIR type")

    def _check_constants(self) -> None:
        for const in self.p.consts:
            what = f"constant {const.name}"
            self._check_type(const.type, what)
            t = const.type
            scalar = isinstance(t, Prim) and t != BYTES
            if not (scalar or isinstance(t, (EnumType, FrozenType))):
                self.fail("V-011", f"{what} has type {t}, which is neither scalar nor frozen")
            self._check_const_value(const.value, t, what)

    def _check_const_value(self, value: ir.ConstValue, t: Type, what: str) -> None:
        if isinstance(t, FrozenType):
            self._check_const_value(value, t.inner, what)
        elif t == BOOL:
            if not isinstance(value, bool):
                self.fail("V-012", f"{what} is bool but its value is {value!r}")
        elif t in INT_RANGE:
            if isinstance(value, bool) or not isinstance(value, int):
                self.fail("V-012", f"{what} is {t} but its value is {value!r}")
            low, high = INT_RANGE[t]
            if not low <= value <= high:
                self.fail("V-012", f"{what} holds {value}, outside {low} .. {high} for {t}")
        elif isinstance(t, EnumType):
            if not isinstance(value, ir.EnumConst):
                self.fail("V-012", f"{what} is {t} but its value is {value!r}")
            if value.variant not in self.p.enum_map[t.name].variants:
                self.fail("V-003", f"{what} names variant {value.variant!r}, which {t} lacks")
        elif isinstance(t, StructType):
            if not isinstance(value, ir.StructConst):
                self.fail("V-012", f"{what} is {t} but its value is {value!r}")
            decl = self.p.struct_map[t.name]
            given = dict(value.fields)
            if len(given) != len(value.fields) or set(given) != {f.name for f in decl.fields}:
                self.fail("V-012", f"{what} does not give every field of {t} exactly once")
            for f in decl.fields:
                self._check_const_value(given[f.name], f.type, f"{what}.{f.name}")
        elif t == BYTES:
            if not isinstance(value, ir.BytesConst):
                self.fail("V-012", f"{what} is bytes but its value is {value!r}")
            if not isinstance(value.data, bytes):
                self.fail("V-012", f"{what} holds {value.data!r}, which is not a byte string")
        elif isinstance(t, VecType):
            if not isinstance(value, ir.VecConst):
                self.fail("V-012", f"{what} is {t} but its value is {value!r}")
            if len(value.elems) > t.max:
                self.fail(
                    "V-012",
                    f"{what} holds {len(value.elems)} elements, "
                    f"past the declared maximum {t.max}",
                )
            for i, elem in enumerate(value.elems):
                self._check_const_value(elem, t.elem, f"{what}[{i}]")
        else:
            self.fail("V-012", f"{what} has no constant form for type {t}")

    def _check_signatures(self) -> None:
        for func in self.p.funcs:
            names = [p.name for p in func.params]
            if len(set(names)) != len(names):
                self.fail("V-038", f"function {func.name!r} repeats a parameter name")
            for p in func.params:
                if p.mode not in ir.PARAM_MODES:
                    self.fail(
                        "V-040",
                        f"parameter {func.name}.{p.name} has mode {p.mode!r}, "
                        "which is neither 'in' nor 'inout'",
                    )
                self._check_type(p.type, f"parameter {func.name}.{p.name}")
                if p.mode == "in" and self.types.is_linear(p.type):
                    self.fail(
                        "V-018",
                        f"parameter {func.name}.{p.name} passes {p.type} by value, "
                        "but it is linear",
                    )
            if func.ret is not None:
                self._check_type(func.ret, f"the return type of {func.name}")
                if self.types.is_linear(func.ret):
                    self.fail(
                        "V-019", f"function {func.name!r} returns {func.ret}, which is linear"
                    )

    def _check_call_graph(self) -> None:
        edges = {func.name: sorted(self._callees(func)) for func in self.p.funcs}
        for callee in sorted({c for cs in edges.values() for c in cs}):
            if callee not in self.p.func_map:
                self.fail("V-003", f"function {callee!r} is called but not declared")

        self._check_acyclic(list(edges), edges.__getitem__, "V-021", "a chain of calls")

    def _callees(self, func: ir.Func) -> set[str]:
        return {stmt.fn for stmt in _walk(func.body) if isinstance(stmt, ir.Call)}

    # --- function bodies ---

    def _check_function(self, func: ir.Func) -> None:
        scope = Scope()
        for p in func.params:
            if p.name in self.top_level:
                self.fail("V-038", f"parameter {func.name}.{p.name} reuses a top-level name")
            scope.declare(p.name, Binding(p.type, writable=p.mode == "inout"))

        ending = self._check_body(func.body, func, scope, in_loop=False)
        if func.ret is not None and ending != RETURNS:
            self.fail("V-035", f"function {func.name!r} can reach its end without returning")

    def _check_body(
        self, body: Sequence[ir.Stmt], func: ir.Func, scope: Scope, in_loop: bool
    ) -> str:
        introduced: list[str] = []
        ending = FALLS_THROUGH
        for stmt in body:
            if ending != FALLS_THROUGH:
                self.fail(
                    "V-027", f"in {func.name!r}, a statement follows one that never falls through"
                )
            ending = self._check_stmt(stmt, func, scope, in_loop, introduced)
        for name in introduced:
            scope.live.discard(name)
        return ending

    def _check_stmt(
        self, stmt: ir.Stmt, func: ir.Func, scope: Scope, in_loop: bool, introduced: list[str]
    ) -> str:
        where = f"in {func.name!r}"
        match stmt:
            case ir.Let(name=name, type=t, init=init):
                if name in scope.bindings or name in self.top_level:
                    self.fail("V-038", f"{where}, local {name!r} reuses a name")
                self._check_type(t, f"local {func.name}.{name}")
                if init is not None:
                    if self.types.is_linear(t):
                        self.fail(
                            "V-037",
                            f"{where}, local {name!r} has the linear type {t}, "
                            "which starts empty and takes no initializer",
                        )
                    self._expect(init, t, scope, f"{where}, the initializer of {name!r}")
                scope.declare(name, Binding(t, writable=True))
                introduced.append(name)

            case ir.Assign(place=place, value=value):
                t = self._place_type(place, scope, where)
                if self.types.is_linear(t):
                    self.fail(
                        "V-024",
                        f"{where}, {t} is linear and is not assigned; use take, copy or freeze",
                    )
                self._expect(value, t, scope, f"{where}, an assignment", rule="V-024")

            case ir.Take(dest=dest, src=src):
                d = self._place_type(dest, scope, where)
                s = self._place_type(src, scope, where)
                if d != s:
                    self.fail("V-028", f"{where}, take moves a {s} into a {d}")
                self._require_disjoint("V-028", place_path(dest), place_path(src), where, "take")

            case ir.Swap(a=a, b=b):
                ta = self._place_type(a, scope, where)
                tb = self._place_type(b, scope, where)
                if ta != tb:
                    self.fail("V-029", f"{where}, swap exchanges a {ta} with a {tb}")
                self._require_disjoint("V-029", place_path(a), place_path(b), where, "swap")

            case ir.Copy(dest=dest, src=src):
                d = self._place_type(dest, scope, where)
                # The one place a linear expression may be read: copying is the
                # sanctioned duplication, and it is deep.
                s = self._type_of(src, scope, f"{where}, the source of a copy")
                if unfrozen(s) != d:
                    self.fail("V-030", f"{where}, copy makes a {d} out of a {s}")
                for path in read_paths(src):
                    self._require_disjoint("V-030", place_path(dest), path, where, "copy")

            case ir.Freeze(dest=dest, src=src):
                d = self._place_type(dest, scope, where)
                s = self._place_type(src, scope, where)
                if not self.types.is_linear(s):
                    self.fail("V-008", f"{where}, freeze takes a {s}, which is already copyable")
                if d != FrozenType(s):
                    self.fail("V-013", f"{where}, freezing a {s} yields frozen<{s}>, not a {d}")

            case ir.Push(seq=seq, value=value):
                elem = self._sequence_element(seq, scope, where, "push")
                self._expect(value, elem, scope, f"{where}, a push")
                for path in read_paths(value):
                    self._require_disjoint("V-031", place_path(seq), path, where, "push")

            case ir.Pop(seq=seq, dest=dest):
                elem = self._sequence_element(seq, scope, where, "pop")
                d = self._place_type(dest, scope, where)
                if d != elem:
                    self.fail("V-013", f"{where}, pop of a {elem} into a {d}")
                self._require_disjoint("V-031", place_path(seq), place_path(dest), where, "pop")

            case ir.Truncate(seq=seq, length=length):
                self._sequence_element(seq, scope, where, "truncate")
                self._expect(length, U32, scope, f"{where}, a truncate length")

            case ir.Reserve(seq=seq, cap=cap):
                self._sequence_element(seq, scope, where, "reserve")
                self._expect(cap, U32, scope, f"{where}, a reserve capacity")

            case ir.If(cond=cond, then=then, otherwise=otherwise):
                self._expect(cond, BOOL, scope, f"{where}, an if condition")
                a = self._check_body(then, func, scope, in_loop)
                b = self._check_body(otherwise, func, scope, in_loop)
                # An absent else is an empty one, and an empty one falls through.
                return _combine(a, b) if otherwise else FALLS_THROUGH

            case ir.While(cond=cond, variant=variant, body=body):
                self._expect(cond, BOOL, scope, f"{where}, a while condition")
                self._expect(variant, COUNTER, scope, f"{where}, a loop variant", rule="V-036")
                self._check_body(body, func, scope, in_loop=True)
                # The condition may be false the first time, so a loop never
                # settles how the body around it ends.

            case ir.Switch(value=value, arms=arms, default=default):
                return self._check_switch(stmt, func, scope, in_loop, where)

            case ir.Break() | ir.Continue():
                if not in_loop:
                    kind = "break" if isinstance(stmt, ir.Break) else "continue"
                    self.fail("V-033", f"{where}, {kind} outside a while body")
                return JUMPS

            case ir.Return(value=value):
                if func.ret is None:
                    if value is not None:
                        self.fail(
                            "V-034",
                            f"{where}, a return carries a value but the function returns nothing",
                        )
                elif value is None:
                    self.fail(
                        "V-034",
                        f"{where}, a return carries no value but the function returns {func.ret}",
                    )
                else:
                    self._expect(value, func.ret, scope, f"{where}, a return", rule="V-034")
                return RETURNS

            case ir.Call():
                self._check_call(stmt, scope, where)

            case _:
                self.fail("V-042", f"{where}, {stmt!r} is not a TIR statement")

        return FALLS_THROUGH

    def _check_switch(
        self, stmt: ir.Switch, func: ir.Func, scope: Scope, in_loop: bool, where: str
    ) -> str:
        t = self._value_type(stmt.value, scope, f"{where}, a switch")
        if not isinstance(t, EnumType):
            self.fail("V-013", f"{where}, switch on a {t}, which is not an enum")
        variants = self.p.enum_map[t.name].variants
        seen: set[str] = set()
        for arm in stmt.arms:
            if arm.variant not in variants:
                self.fail("V-032", f"{where}, switch arm {arm.variant!r} is not a variant of {t}")
            if arm.variant in seen:
                self.fail("V-032", f"{where}, switch repeats the arm {arm.variant!r}")
            seen.add(arm.variant)

        covered = seen == set(variants)
        if covered and stmt.default is not None:
            self.fail("V-032", f"{where}, switch covers {t} and still carries a default")
        if not covered and stmt.default is None:
            missing = ", ".join(sorted(set(variants) - seen))
            self.fail("V-032", f"{where}, switch on {t} has no arm for {missing}")

        endings = [self._check_body(arm.body, func, scope, in_loop) for arm in stmt.arms]
        if stmt.default is not None:
            endings.append(self._check_body(stmt.default, func, scope, in_loop))
        ending = endings[0]
        for other in endings[1:]:
            ending = _combine(ending, other)
        return ending

    def _check_call(self, call: ir.Call, scope: Scope, where: str) -> None:
        callee = self.p.func_map.get(call.fn)
        if callee is None:
            self.fail("V-003", f"{where}, a call to {call.fn!r}, which is not declared")
        if len(call.args) != len(callee.params):
            self.fail(
                "V-013",
                f"{where}, {call.fn!r} takes {len(callee.params)} arguments, "
                f"{len(call.args)} given",
            )

        writes: list[tuple[str, Path]] = []
        reads: list[tuple[str, Path]] = []
        for position, (arg, param) in enumerate(zip(call.args, callee.params)):
            label = f"argument {position + 1} of {call.fn!r}"
            if isinstance(arg, ir.InArg):
                if param.mode != "in":
                    self.fail("V-013", f"{where}, {label} is passed in, but {param.name} is inout")
                self._expect(arg.expr, param.type, scope, f"{where}, {label}")
                reads.extend((label, path) for path in read_paths(arg.expr))
            else:
                if param.mode != "inout":
                    self.fail("V-013", f"{where}, {label} is passed inout, but {param.name} is in")
                t = self._place_type(arg.place, scope, where)
                if t != param.type:
                    self.fail("V-013", f"{where}, {label} is a {t}, the parameter is {param.type}")
                writes.append((label, place_path(arg.place)))
                reads.extend((label, path) for path in place_read_paths(arg.place))

        if call.dest is None:
            if callee.ret is not None:
                self.fail("V-020", f"{where}, the {callee.ret} {call.fn!r} returns is dropped")
        else:
            if callee.ret is None:
                self.fail("V-020", f"{where}, {call.fn!r} returns nothing to store")
            t = self._place_type(call.dest, scope, where)
            if t != callee.ret:
                self.fail(
                    "V-020", f"{where}, {call.fn!r} returns {callee.ret}, stored into a {t}"
                )
            writes.append(("the result", place_path(call.dest)))
            reads.extend(("the result", path) for path in place_read_paths(call.dest))

        for label, write in writes:
            for other_label, other in reads + writes:
                if label == other_label:
                    continue
                if not provably_disjoint(write, other):
                    self.fail(
                        "V-022",
                        f"{where}, {label} may overlap {other_label}: "
                        f"{_show(write)} against {_show(other)}",
                    )

    def _require_disjoint(self, rule: str, a: Path, b: Path, where: str, what: str) -> None:
        if not provably_disjoint(a, b):
            self.fail(
                rule, f"{where}, {what} needs disjoint places, got {_show(a)} and {_show(b)}"
            )

    # --- expressions ---

    def _expect(
        self, e: ir.Expr, wanted: Type, scope: Scope, what: str, rule: str = "V-013"
    ) -> None:
        got = self._value_type(e, scope, what)
        if got != wanted:
            self.fail(rule, f"{what} wants a {wanted}, got a {got}")

    def _pairs(self, entries: object, what: str) -> None:
        """A struct's fields are (name, value) pairs, which `dict` would not say clearly."""
        if not isinstance(entries, tuple):
            self.fail("V-042", f"{what} has fields that are not a tuple: {entries!r}")
        for entry in entries:
            if not isinstance(entry, tuple) or len(entry) != 2 or not isinstance(entry[0], str):
                self.fail("V-042", f"{what} has a field that is not a name and a value: {entry!r}")

    def _known(self, op: str, inventory: Sequence[str], what: str) -> None:
        """The operator inventories of section 6 are closed sets.

        The reader already refuses an unknown operator, but a program built
        straight from `ir` never went through the reader, and the validator is
        the boundary that is supposed to hold either way.
        """
        if op not in inventory:
            self.fail("V-013", f"{what}: {op!r} is not one of {', '.join(inventory)}")

    def _value_type(self, e: ir.Expr, scope: Scope, what: str) -> Type:
        """The type of an expression used as a value, which may not be linear."""
        got = self._type_of(e, scope, what)
        if self.types.is_linear(got):
            self.fail("V-023", f"{what} reads a {got}, which is linear")
        return got

    def _type_of(self, e: ir.Expr, scope: Scope, what: str) -> Type:
        """The type of an expression, with no view on how it is used.

        A linear result is typed here without complaint: a linear value is a
        legal base for a field, an index, a len or a cap, and the source of a
        copy. `_value_type` is what refuses one used as a value.
        """
        match e:
            case ir.Lit(type=t, value=value):
                if t == BOOL:
                    if type(value) is not bool:
                        self.fail("V-014", f"{what}: {value!r} is not a bool")
                elif t in INT_RANGE:
                    # `type(...) is int` rather than isinstance: a bool is an
                    # int in Python and a float compares against a range
                    # perfectly happily, and neither is a TIR literal.
                    if type(value) is not int:
                        self.fail("V-014", f"{what}: {value!r} is not a {t}")
                    low, high = INT_RANGE[t]
                    if not low <= value <= high:
                        self.fail("V-014", f"{what}: {value} is outside {low} .. {high} for {t}")
                else:
                    # Only the reader restricts which types can carry a literal;
                    # the DSL will happily build bytes_(5).
                    self.fail("V-014", f"{what}: {t} has no literal form")
                return t

            case ir.Var(name=name):
                binding = scope.lookup(name)
                if binding is None:
                    self.fail("V-039", f"{what} reads {name!r}, which is not in scope")
                return binding.type

            case ir.ConstRef(name=name):
                const = self.p.const_map.get(name)
                if const is None:
                    self.fail("V-003", f"{what} reads constant {name!r}, which is not declared")
                return const.type

            case ir.FieldRead(base=base, name=name):
                return self._field_type(self._type_of(base, scope, what), name, what)

            case ir.IndexRead(base=base, index=index):
                base_type = self._type_of(base, scope, what)
                if not is_sequence(unfrozen(base_type)):
                    self.fail("V-013", f"{what} indexes a {base_type}, which is not a sequence")
                self._expect(index, U32, scope, f"{what}, an index")
                # Element types are copyable (V-006), so nothing here has to
                # be re-frozen on the way out of a frozen sequence.
                return element_type(base_type)

            case ir.Len(arg=arg) | ir.Cap(arg=arg):
                t = self._type_of(arg, scope, what)
                if not is_sequence(unfrozen(t)):
                    self.fail("V-013", f"{what} asks the length of a {t}")
                return U32

            case ir.Unary(op=op, arg=arg):
                self._known(op, ir.UNARY_OPS, what)
                t = self._value_type(arg, scope, what)
                if op == "not":
                    if t != BOOL:
                        self.fail("V-013", f"{what}: not takes a bool, got a {t}")
                elif t not in BITWISE_TYPES:
                    self.fail("V-013", f"{what}: {op} takes u8, i32 or u32, got a {t}")
                return t

            case ir.Binary(op=op, left=left, right=right):
                self._known(op, ir.BINARY_OPS, what)
                t = self._value_type(left, scope, what)
                allowed = ARITH_TYPES if op in ir.ARITH_OPS else BITWISE_TYPES
                if t not in allowed:
                    self.fail("V-013", f"{what}: {op} does not take a {t}")
                self._expect(right, t, scope, f"{what}, the right operand of {op}")
                return t

            case ir.Compare(op=op, left=left, right=right):
                self._known(op, ir.COMPARE_OPS, what)
                t = self._value_type(left, scope, what)
                if op in ir.EQUALITY_OPS:
                    if not (t == BOOL or t in INT_RANGE or isinstance(t, EnumType)):
                        self.fail("V-013", f"{what}: {op} does not compare a {t}")
                elif t not in ORDER_TYPES:
                    self.fail("V-013", f"{what}: {op} orders u8, i32, u32 or counter, not a {t}")
                self._expect(right, t, scope, f"{what}, the right operand of {op}")
                return BOOL

            case ir.DivRem(op=op, left=left, right=right, fallback=fallback):
                self._known(op, ir.DIVREM_OPS, what)
                t = self._value_type(left, scope, what)
                if t not in ARITH_TYPES:
                    self.fail("V-013", f"{what}: {op} does not take a {t}")
                self._expect(right, t, scope, f"{what}, the divisor")
                self._expect(fallback, t, scope, f"{what}, the fallback")
                return t

            case ir.Shift(op=op, arg=arg, count=count):
                self._known(op, ir.SHIFT_OPS, what)
                t = self._value_type(arg, scope, what)
                if t not in BITWISE_TYPES:
                    self.fail("V-013", f"{what}: {op} shifts u8, i32 or u32, not a {t}")
                if t not in SHIFT_TYPES[op]:
                    self.fail("V-016", f"{what}: {op} does not take a {t}")
                width = INT_WIDTH[t]
                if type(count) is not int or not 0 <= count <= width - 1:
                    self.fail("V-015", f"{what}: a {t} shifts by 0 .. {width - 1}, not {count}")
                return t

            case ir.Cast(type=t, arg=arg):
                source = self._value_type(arg, scope, what)
                if t not in CASTABLE_TO:
                    self.fail("V-013", f"{what} casts to {t}, which is not an integer type")
                if source not in CASTABLE_FROM:
                    self.fail("V-013", f"{what} casts from a {source}, which has no cast")
                return t

            case ir.Logical(op=op, left=left, right=right):
                self._known(op, ir.LOGICAL_OPS, what)
                self._expect(left, BOOL, scope, f"{what}, the left operand of {op}")
                self._expect(right, BOOL, scope, f"{what}, the right operand of {op}")
                return BOOL

            case ir.EnumVal(type=name, variant=variant):
                decl = self.p.enum_map.get(name)
                if decl is None:
                    self.fail("V-003", f"{what} names enum {name!r}, which is not declared")
                if variant not in decl.variants:
                    self.fail("V-003", f"{what} names variant {variant!r}, which {name!r} lacks")
                return EnumType(name)

            case ir.StructVal(type=name, fields=fields):
                decl = self.p.struct_map.get(name)
                if decl is None:
                    self.fail("V-003", f"{what} names struct {name!r}, which is not declared")
                t = StructType(name)
                if self.types.is_linear(t):
                    self.fail("V-017", f"{what} builds a {t}, which is linear")
                given = dict(fields)
                # `dict` would swallow a repeat, and so would the JSON object
                # this becomes, so the count is what says "exactly once".
                if len(given) != len(fields) or set(given) != {f.name for f in decl.fields}:
                    self.fail("V-017", f"{what} does not give every field of {t} exactly once")
                for f in decl.fields:
                    self._expect(given[f.name], f.type, scope, f"{what}, the field {f.name!r}")
                return t

        self.fail("V-042", f"{what} holds {e!r}, which is not a TIR expression")

    def _field_type(self, base: Type, name: str, what: str) -> Type:
        inner = unfrozen(base)
        if not isinstance(inner, StructType):
            self.fail("V-013", f"{what} reads the field {name!r} of a {base}, not a struct")
        field = self.p.struct_map[inner.name].field(name)
        if field is None:
            self.fail("V-013", f"{what} reads the field {name!r}, which {inner} does not have")
        if isinstance(base, FrozenType) and self.types.is_linear(field.type):
            return FrozenType(field.type)
        return field.type

    # --- places ---

    def _place_type(self, place: ir.Place, scope: Scope, where: str) -> Type:
        """The type of a place, which in TIR is always about to be written."""
        t, writable, through_frozen = self._walk_place(place, scope, where)
        if not writable:
            self.fail("V-025", f"{where}, {_show(place_path(place))} is not writable")
        if through_frozen:
            self.fail(
                "V-026", f"{where}, {_show(place_path(place))} writes through a frozen value"
            )
        return t

    def _walk_place(self, place: ir.Place, scope: Scope, where: str) -> tuple[Type, bool, bool]:
        match place:
            case ir.VarPlace(name=name):
                binding = scope.lookup(name)
                if binding is None:
                    self.fail("V-039", f"{where}, {name!r} is not in scope")
                return binding.type, binding.writable, False

            case ir.FieldPlace(base=base, name=name):
                base_type, writable, frozen = self._walk_place(base, scope, where)
                field_type = self._field_type(base_type, name, where)
                return field_type, writable, frozen or isinstance(base_type, FrozenType)

            case ir.IndexPlace(base=base, index=index):
                base_type, writable, frozen = self._walk_place(base, scope, where)
                if not is_sequence(unfrozen(base_type)):
                    self.fail("V-013", f"{where}, a {base_type} is not a sequence")
                self._expect(index, U32, scope, f"{where}, an index")
                return (
                    element_type(base_type),
                    writable,
                    frozen or isinstance(base_type, FrozenType),
                )

        self.fail("V-042", f"{where}, {place!r} is not a TIR place")

    def _sequence_element(self, seq: ir.Place, scope: Scope, where: str, what: str) -> Type:
        t = self._place_type(seq, scope, where)
        if isinstance(t, FrozenType):
            self.fail("V-026", f"{where}, {what} on a frozen sequence")
        if not is_sequence(t):
            self.fail("V-013", f"{where}, {what} needs a sequence, got a {t}")
        return element_type(t)


def _leaves(
    node: object, owner: str = "the program", field: str = "itself"
) -> Iterator[tuple[str, str, object]]:
    """Every scalar a program tree holds, with the node and field it sits in."""
    if is_dataclass(node) and not isinstance(node, type):
        name = type(node).__name__
        for f in fields(node):
            yield from _leaves(getattr(node, f.name), name, f.name)
    elif isinstance(node, (tuple, list)):
        for item in node:
            yield from _leaves(item, owner, field)
    else:
        yield owner, field, node


def _walk(body: object) -> Iterator[ir.Stmt]:
    """Every statement in a body, nested ones included.

    Tolerant of a body that is not one, because `_check_names` calls it before
    the shape pass has said which bodies are bodies.
    """
    if not isinstance(body, (tuple, list)):
        return
    for stmt in body:
        yield stmt
        match stmt:
            case ir.If(then=then, otherwise=otherwise):
                yield from _walk(then)
                yield from _walk(otherwise)
            case ir.While(body=inner):
                yield from _walk(inner)
            case ir.Switch(arms=arms, default=default):
                for arm in arms:
                    yield from _walk(arm.body)
                if default is not None:
                    yield from _walk(default)


__all__ = ["ValidationError", "provably_disjoint", "validate"]
