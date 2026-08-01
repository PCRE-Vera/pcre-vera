"""The builder API the engine is authored against.

It only builds IR. It has no execution semantics, it checks almost nothing,
and it is explicitly untrusted: a bug here shows up as a validator complaint,
a failed proof, or a differential test failure, never as a silently wrong
engine. That is why it can afford to be convenient.

The shape it aims for::

    m = Module()
    Phase = m.enum("Phase", ["Enter", "Done"])
    Task = m.struct("Task", [("n", u32), ("phase", Phase)])

    f = m.func("step", params=[("t", Task), ("out", counter, "inout")])
    t = f["t"]
    with f.if_(t.field("n") > u32(0)):
        f.set(f["out"], counter(1))
    f.ret()

    program = m.build()

Expressions carry no type here; the validator is what decides whether
`a + b` made sense. Literals are written through their type — `u32(7)` — for
the one thing the DSL genuinely cannot guess.
"""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from contextlib import contextmanager

from ..tir import ir
from ..tir.types import (
    BOOL,
    BYTES,
    COUNTER,
    I32,
    U8,
    U32,
    EnumDecl,
    EnumType,
    Field,
    FrozenType,
    StructDecl,
    StructType,
    Type,
    VecType,
)


class Expr:
    """An expression under construction. Operators build nodes, nothing more."""

    __slots__ = ("node",)

    def __init__(self, node: ir.Expr) -> None:
        self.node = node

    def __repr__(self) -> str:
        return f"Expr({self.node!r})"

    # --- projections ---

    def field(self, name: str) -> "Expr":
        return Expr(ir.FieldRead(self.node, name))

    def at(self, index: "Expr") -> "Expr":
        return Expr(ir.IndexRead(self.node, _node(index)))

    def len(self) -> "Expr":
        return Expr(ir.Len(self.node))

    def cap(self) -> "Expr":
        return Expr(ir.Cap(self.node))

    # --- arithmetic and bits ---

    def __add__(self, other: "Expr") -> "Expr":
        return Expr(ir.Binary("add", self.node, _node(other)))

    def __sub__(self, other: "Expr") -> "Expr":
        return Expr(ir.Binary("sub", self.node, _node(other)))

    def __mul__(self, other: "Expr") -> "Expr":
        return Expr(ir.Binary("mul", self.node, _node(other)))

    def __and__(self, other: "Expr") -> "Expr":
        return Expr(ir.Binary("and", self.node, _node(other)))

    def __or__(self, other: "Expr") -> "Expr":
        return Expr(ir.Binary("or", self.node, _node(other)))

    def __xor__(self, other: "Expr") -> "Expr":
        return Expr(ir.Binary("xor", self.node, _node(other)))

    def __invert__(self) -> "Expr":
        return Expr(ir.Unary("bnot", self.node))

    def __neg__(self) -> "Expr":
        return Expr(ir.Unary("neg", self.node))

    def div(self, divisor: "Expr", fallback: "Expr") -> "Expr":
        return Expr(ir.DivRem("div", self.node, _node(divisor), _node(fallback)))

    def rem(self, divisor: "Expr", fallback: "Expr") -> "Expr":
        return Expr(ir.DivRem("rem", self.node, _node(divisor), _node(fallback)))

    def shl(self, count: int) -> "Expr":
        return Expr(ir.Shift("shl", self.node, count))

    def shr(self, count: int) -> "Expr":
        return Expr(ir.Shift("shr", self.node, count))

    def sar(self, count: int) -> "Expr":
        return Expr(ir.Shift("sar", self.node, count))

    def cast(self, t: "TypeRef") -> "Expr":
        return Expr(ir.Cast(t.t, self.node))

    # --- comparisons ---

    def __lt__(self, other: "Expr") -> "Expr":
        return Expr(ir.Compare("lt", self.node, _node(other)))

    def __le__(self, other: "Expr") -> "Expr":
        return Expr(ir.Compare("le", self.node, _node(other)))

    def __gt__(self, other: "Expr") -> "Expr":
        return Expr(ir.Compare("gt", self.node, _node(other)))

    def __ge__(self, other: "Expr") -> "Expr":
        return Expr(ir.Compare("ge", self.node, _node(other)))

    def __eq__(self, other: object) -> "Expr":  # type: ignore[override]
        return Expr(ir.Compare("eq", self.node, _node(other)))

    def __ne__(self, other: object) -> "Expr":  # type: ignore[override]
        return Expr(ir.Compare("ne", self.node, _node(other)))

    __hash__ = None  # type: ignore[assignment]


class Ref(Expr):
    """An expression that is also a place: a variable, a field, or an element."""

    __slots__ = ("place",)

    def __init__(self, place: ir.Place, node: ir.Expr) -> None:
        super().__init__(node)
        self.place = place

    def __repr__(self) -> str:
        return f"Ref({self.place!r})"

    def field(self, name: str) -> "Ref":
        return Ref(ir.FieldPlace(self.place, name), ir.FieldRead(self.node, name))

    def at(self, index: Expr) -> "Ref":
        return Ref(
            ir.IndexPlace(self.place, _node(index)), ir.IndexRead(self.node, _node(index))
        )


def _node(value: object) -> ir.Expr:
    if isinstance(value, Expr):
        return value.node
    raise TypeError(
        f"a TIR operand is an Expr, got {value!r}; write the literal through its type, "
        "as in u32(7)"
    )


def lnot(x: Expr) -> Expr:
    return Expr(ir.Unary("not", _node(x)))


def land(left: Expr, right: Expr) -> Expr:
    """Short-circuit and, which TIR defines as a conditional."""
    return Expr(ir.Logical("and", _node(left), _node(right)))


def lor(left: Expr, right: Expr) -> Expr:
    return Expr(ir.Logical("or", _node(left), _node(right)))


# --- types ---


class TypeRef:
    def __init__(self, t: Type) -> None:
        self.t = t

    def __repr__(self) -> str:
        return f"TypeRef({self.t})"

    def __call__(self, value: int | bool) -> Expr:
        """A literal of this type."""
        return Expr(ir.Lit(self.t, value))


class EnumRef(TypeRef):
    def __init__(self, decl: EnumDecl) -> None:
        super().__init__(EnumType(decl.name))
        self.decl = decl

    def __getattr__(self, variant: str) -> Expr:
        # Only reached for names that are not real attributes, which is every
        # variant, so `Phase.Enter` reads as the value it denotes.
        if variant.startswith("_"):
            raise AttributeError(variant)
        return Expr(ir.EnumVal(self.decl.name, variant))


class StructRef(TypeRef):
    def __init__(self, decl: StructDecl) -> None:
        super().__init__(StructType(decl.name))
        self.decl = decl

    def of(self, **fields: Expr) -> Expr:
        return Expr(
            ir.StructVal(
                self.decl.name, tuple((name, _node(e)) for name, e in fields.items())
            )
        )


boolean = TypeRef(BOOL)
u8 = TypeRef(U8)
i32 = TypeRef(I32)
u32 = TypeRef(U32)
counter = TypeRef(COUNTER)
bytes_ = TypeRef(BYTES)


def vec(elem: TypeRef, max: int) -> TypeRef:
    return TypeRef(VecType(elem.t, max))


def frozen(inner: TypeRef) -> TypeRef:
    return TypeRef(FrozenType(inner.t))


# --- call arguments ---


class Inout:
    """Marks a call argument as passed by place."""

    __slots__ = ("ref",)

    def __init__(self, ref: Ref) -> None:
        self.ref = ref


def inout(ref: Ref) -> Inout:
    return Inout(ref)


# --- functions ---


class FuncBuilder:
    def __init__(
        self,
        name: str,
        params: Sequence[tuple],
        ret: TypeRef | None,
    ) -> None:
        self.name = name
        self.ret_type = ret
        self._params: list[ir.Param] = []
        self._refs: dict[str, Ref] = {}
        for entry in params:
            pname, ptype, *rest = entry
            mode = rest[0] if rest else "in"
            self._params.append(ir.Param(pname, ptype.t, mode))
            self._refs[pname] = Ref(ir.VarPlace(pname), ir.Var(pname))
        self._blocks: list[list[ir.Stmt]] = [[]]

    def __getitem__(self, name: str) -> Ref:
        return self._refs[name]

    # --- emission ---

    def _emit(self, stmt: ir.Stmt) -> None:
        self._blocks[-1].append(stmt)

    def _open(self) -> None:
        """Start collecting statements into a nested body."""
        self._blocks.append([])

    def _close(self) -> tuple[ir.Stmt, ...]:
        return tuple(self._blocks.pop())

    def let(self, name: str, t: TypeRef, init: Expr | None = None) -> Ref:
        self._emit(ir.Let(name, t.t, None if init is None else _node(init)))
        ref = Ref(ir.VarPlace(name), ir.Var(name))
        self._refs[name] = ref
        return ref

    def set(self, place: Ref, value: Expr) -> None:
        self._emit(ir.Assign(place.place, _node(value)))

    def take(self, dest: Ref, src: Ref) -> None:
        self._emit(ir.Take(dest.place, src.place))

    def swap(self, a: Ref, b: Ref) -> None:
        self._emit(ir.Swap(a.place, b.place))

    def copy(self, dest: Ref, src: Expr) -> None:
        self._emit(ir.Copy(dest.place, _node(src)))

    def freeze(self, dest: Ref, src: Ref) -> None:
        self._emit(ir.Freeze(dest.place, src.place))

    def push(self, seq: Ref, value: Expr) -> None:
        self._emit(ir.Push(seq.place, _node(value)))

    def pop(self, seq: Ref, dest: Ref) -> None:
        self._emit(ir.Pop(seq.place, dest.place))

    def truncate(self, seq: Ref, length: Expr) -> None:
        self._emit(ir.Truncate(seq.place, _node(length)))

    def reserve(self, seq: Ref, cap: Expr) -> None:
        self._emit(ir.Reserve(seq.place, _node(cap)))

    def call(self, fn: str, args: Sequence[Expr | Inout] = (), dest: Ref | None = None) -> None:
        built: list[ir.Arg] = []
        for arg in args:
            if isinstance(arg, Inout):
                built.append(ir.InoutArg(arg.ref.place))
            else:
                built.append(ir.InArg(_node(arg)))
        self._emit(ir.Call(fn, tuple(built), None if dest is None else dest.place))

    def ret(self, value: Expr | None = None) -> None:
        self._emit(ir.Return(None if value is None else _node(value)))

    def brk(self) -> None:
        self._emit(ir.Break())

    def cont(self) -> None:
        self._emit(ir.Continue())

    # --- blocks ---

    @contextmanager
    def if_(self, cond: Expr) -> Iterator[None]:
        self._open()
        yield
        self._emit(ir.If(_node(cond), self._close(), ()))

    @contextmanager
    def else_(self) -> Iterator[None]:
        block = self._blocks[-1]
        if not block or not isinstance(block[-1], ir.If):
            raise ValueError("else_ has to follow an if_ in the same block")
        previous = block.pop()
        self._open()
        yield
        self._emit(ir.If(previous.cond, previous.then, self._close()))

    @contextmanager
    def while_(self, cond: Expr, variant: Expr) -> Iterator[None]:
        self._open()
        yield
        self._emit(ir.While(_node(cond), _node(variant), self._close()))

    @contextmanager
    def switch(self, value: Expr) -> Iterator["SwitchBuilder"]:
        builder = SwitchBuilder(self, _node(value))
        yield builder
        self._emit(builder.finish())

    def finish(self) -> ir.Func:
        if len(self._blocks) != 1:
            raise ValueError(f"function {self.name!r} has an unclosed block")
        return ir.Func(
            name=self.name,
            params=tuple(self._params),
            ret=None if self.ret_type is None else self.ret_type.t,
            body=tuple(self._blocks[0]),
        )


class SwitchBuilder:
    def __init__(self, func: FuncBuilder, value: ir.Expr) -> None:
        self.func = func
        self.value = value
        self.arms: list[ir.Arm] = []
        self.default: tuple[ir.Stmt, ...] | None = None

    @contextmanager
    def case(self, variant: str) -> Iterator[None]:
        self.func._open()
        yield
        self.arms.append(ir.Arm(variant, self.func._close()))

    @contextmanager
    def otherwise(self) -> Iterator[None]:
        self.func._open()
        yield
        self.default = self.func._close()

    def finish(self) -> ir.Switch:
        return ir.Switch(self.value, tuple(self.arms), self.default)


# --- modules ---


class Module:
    def __init__(self) -> None:
        self.enums: list[EnumDecl] = []
        self.structs: list[StructDecl] = []
        self.consts: list[ir.Const] = []
        self.funcs: list[FuncBuilder] = []

    def enum(self, name: str, variants: Sequence[str]) -> EnumRef:
        decl = EnumDecl(name, tuple(variants))
        self.enums.append(decl)
        return EnumRef(decl)

    def struct(self, name: str, fields: Sequence[tuple[str, TypeRef]]) -> StructRef:
        decl = StructDecl(name, tuple(Field(fname, t.t) for fname, t in fields))
        self.structs.append(decl)
        return StructRef(decl)

    def const(self, name: str, t: TypeRef, value: object) -> Expr:
        self.consts.append(ir.Const(name, t.t, _const_value(value)))
        return Expr(ir.ConstRef(name))

    def func(
        self, name: str, params: Sequence[tuple] = (), ret: TypeRef | None = None
    ) -> FuncBuilder:
        builder = FuncBuilder(name, params, ret)
        self.funcs.append(builder)
        return builder

    def build(self) -> ir.Program:
        return ir.Program(
            enums=tuple(self.enums),
            structs=tuple(self.structs),
            consts=tuple(self.consts),
            funcs=tuple(f.finish() for f in self.funcs),
        )


def _const_value(value: object) -> ir.ConstValue:
    if isinstance(value, (bytes, bytearray)):
        return ir.BytesConst(bytes(value))
    if isinstance(value, (list, tuple)):
        return ir.VecConst(tuple(_const_value(v) for v in value))
    if isinstance(value, dict):
        return ir.StructConst(tuple((k, _const_value(v)) for k, v in value.items()))
    if isinstance(value, str):
        return ir.EnumConst(value)
    if isinstance(value, (bool, int)):
        return value
    raise TypeError(f"not a TIR constant value: {value!r}")
