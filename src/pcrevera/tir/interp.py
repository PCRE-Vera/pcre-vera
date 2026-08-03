"""The Python reference interpreter for TIR.

It exists so the engine can be run and tested long before the backends and the
proofs do, and later so all three can be compared. It follows TIR-SPEC.md
literally rather than efficiently: saturation is written as the pre-check the
spec states, evaluation is left to right because the spec says which trap wins,
and a loop variant is actually checked at run time, so a false one becomes a
failing test the first time the loop runs instead of a surprise in M6.

The interpreter assumes a validated program. It is not a second validator: a
program that never went through `validate` can make it raise anything at all.

It does carry a small type environment of its own, because a bare Python
integer does not say whether it wraps at 8 bits or 32. That is the same
information the validator computes and deliberately not the same code: the
interpreter needs only the widths, and a definitional interpreter that reasons
about its own operand types is easier to read than one that consults a table
somebody else built.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from . import ir
from .types import (
    BOOL,
    BYTES,
    CAP,
    CEILING,
    COUNTER,
    I32,
    U8,
    U32,
    EnumType,
    FrozenType,
    StructType,
    Type,
    VecType,
    element_type,
    unfrozen,
    wrap,
)

DEFAULT_FUEL = 1_000_000


class Trap(Exception):
    """A checked operation failed. TIR-SPEC.md section 12."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code


class VariantViolation(Exception):
    """A while loop's declared variant did not strictly decrease.

    Not a TIR outcome: the backends ignore variants and Lean discharges them as
    a proof obligation. Here it is a test failure, which is the whole point of
    checking it.
    """


class OutOfFuel(Exception):
    """The run exceeded the interpreter's step budget.

    Also not a TIR outcome. It keeps a test whose loop is wrong from running
    until somebody notices.
    """


# --- runtime values ---


@dataclass
class Seq:
    """A vec or a bytes: elements, capacity, and the maximum its type declares."""

    elem: Type
    max: int
    items: list = field(default_factory=list)
    cap: int = 0


@dataclass(frozen=True)
class Frozen:
    inner: object


@dataclass(frozen=True)
class Tag:
    enum: str
    variant: str


@dataclass
class StructValue:
    type: str
    fields: dict[str, object]


Value = bool | int | Seq | Frozen | Tag | StructValue


class Ref:
    """Where a value lives, so that an inout parameter can write through to it."""

    __slots__ = ("container", "key")

    def __init__(self, container: dict | list, key: str | int) -> None:
        self.container = container
        self.key = key

    def get(self) -> Value:
        return self.container[self.key]  # type: ignore[index]

    def set(self, value: Value) -> None:
        self.container[self.key] = value  # type: ignore[index]


class Cell:
    """A caller-visible box, for passing an inout argument in from Python."""

    def __init__(self, value: Value) -> None:
        self._slot: dict[str, Value] = {"value": value}

    @property
    def value(self) -> Value:
        return self._slot["value"]

    @value.setter
    def value(self, new: Value) -> None:
        self._slot["value"] = new

    def ref(self) -> Ref:
        return Ref(self._slot, "value")


def _read(v: Value) -> Value:
    """A value taken out of storage.

    Structs are copied because two names must never share one. Sequences are
    not, because the only expression that may yield one is the source of a
    copy, which deep-copies it immediately. A frozen value is shared on
    purpose: that is what freezing bought.
    """
    if isinstance(v, StructValue):
        return StructValue(v.type, {k: _read(x) for k, x in v.fields.items()})
    return v


def _objects(v: object, *, through_frozen: bool, out: set[int] | None = None) -> set[int]:
    """The heap objects a value reaches.

    Two walks, because two frozen views of one object are harmless — nobody can
    write through either — while a frozen view of an object something else can
    write to is not: the freeze would appear to change on its own. So the
    mutable walk stops at a frozen value and the reachable walk goes through it,
    and what must not overlap is one argument's mutable set against another's
    reachable set.
    """
    out = set() if out is None else out
    if isinstance(v, Frozen):
        if through_frozen:
            _objects(v.inner, through_frozen=True, out=out)
    elif isinstance(v, Seq):
        out.add(id(v))
        for item in v.items:
            _objects(item, through_frozen=through_frozen, out=out)
    elif isinstance(v, StructValue):
        out.add(id(v))
        for field_value in v.fields.values():
            _objects(field_value, through_frozen=through_frozen, out=out)
    return out


def _deep(v: Value) -> Value:
    """A deep copy, as the copy statement makes it.

    Every mutable sequence it reaches comes out fresh with its capacity equal
    to its length. A frozen value is shared rather than duplicated, which is
    what freezing bought and what keeps `cap` on it the same number afterwards.
    """
    if isinstance(v, StructValue):
        return StructValue(v.type, {k: _deep(x) for k, x in v.fields.items()})
    if isinstance(v, Seq):
        items = [_deep(x) for x in v.items]
        return Seq(v.elem, v.max, items, len(items))
    return v


# --- control flow, as exceptions ---


class _Return(Exception):
    def __init__(self, value: Value | None) -> None:
        self.value = value


class _Break(Exception):
    pass


class _Continue(Exception):
    pass


@dataclass
class Frame:
    locals: dict[str, Value]
    aliases: dict[str, Ref]
    types: dict[str, Type]

    def ref(self, name: str) -> Ref:
        alias = self.aliases.get(name)
        return alias if alias is not None else Ref(self.locals, name)


class Interpreter:
    def __init__(self, program: ir.Program, fuel: int = DEFAULT_FUEL) -> None:
        self.p = program
        self.fuel = fuel
        self.steps = 0

    # --- entry points ---

    def call(self, name: str, args: list[Value | Cell]) -> Value | None:
        """Call a function of a validated program from Python.

        The disjointness V-022 enforces at TIR call sites has no way to reach
        this one, so the same guarantee is enforced here instead, and in the
        same shape: nothing an inout argument can write may be reachable from
        any other argument, an `in` one included. Without that a caller could
        hand one heap-backed value two live names — two cells holding one
        sequence, or a frozen view of a sequence another argument still
        writes — which is what the whole linearity discipline exists to
        prevent.
        """
        func = self.p.func_map[name]
        if len(args) != len(func.params):
            raise TypeError(f"{name} takes {len(func.params)} arguments, {len(args)} given")

        # Two walks per argument, because two frozen views of one value are
        # harmless while a frozen view of something still mutable is not.
        footprints = []
        for param, arg in zip(func.params, args):
            value = arg.value if isinstance(arg, Cell) else arg
            reachable = {id(arg), *_objects(value, through_frozen=True)}
            writable = (
                {id(arg), *_objects(value, through_frozen=False)}
                if param.mode == "inout"
                else set()
            )
            footprints.append((param, writable, reachable))

        for index, (param, writable, _) in enumerate(footprints):
            for other, (_, _, reachable) in enumerate(footprints):
                if other != index and writable & reachable:
                    raise TypeError(
                        f"{name} can write {param.name} through argument {other + 1} as well"
                    )
        frame = Frame(locals={}, aliases={}, types={})
        for param, arg in zip(func.params, args):
            frame.types[param.name] = param.type
            if param.mode == "inout":
                assert isinstance(arg, Cell), f"{param.name} is inout and wants a Cell"
                frame.aliases[param.name] = arg.ref()
            else:
                frame.locals[param.name] = _read(arg.value if isinstance(arg, Cell) else arg)
        try:
            self._body(func.body, frame)
        except _Return as done:
            return done.value
        return None

    def zero(self, t: Type) -> Value:
        """The zero value of a type. TIR-SPEC.md section 4.1."""
        if t == BOOL:
            return False
        if t in (U8, I32, U32, COUNTER):
            return 0
        if t == BYTES:
            return Seq(U8, CEILING, [], 0)
        if isinstance(t, VecType):
            return Seq(t.elem, t.max, [], 0)
        if isinstance(t, FrozenType):
            return Frozen(self.zero(t.inner))
        if isinstance(t, EnumType):
            return Tag(t.name, self.p.enum_map[t.name].variants[0])
        assert isinstance(t, StructType)
        decl = self.p.struct_map[t.name]
        return StructValue(t.name, {f.name: self.zero(f.type) for f in decl.fields})

    # --- statements ---

    def _tick(self) -> None:
        self.steps += 1
        if self.steps > self.fuel:
            raise OutOfFuel(f"more than {self.fuel} steps")

    def _body(self, body: tuple[ir.Stmt, ...], frame: Frame) -> None:
        introduced: list[str] = []
        try:
            for stmt in body:
                self._stmt(stmt, frame, introduced)
        finally:
            for name in introduced:
                frame.locals.pop(name, None)

    def _stmt(self, stmt: ir.Stmt, frame: Frame, introduced: list[str]) -> None:
        self._tick()
        match stmt:
            case ir.Let(name=name, type=t, init=init):
                frame.types[name] = t
                frame.locals[name] = self.zero(t) if init is None else self._eval(init, frame)
                introduced.append(name)

            case ir.Assign(place=place, value=value):
                ref = self._place(place, frame)
                ref.set(self._eval(value, frame))

            case ir.Take(dest=dest, src=src):
                dest_ref = self._place(dest, frame)
                src_ref = self._place(src, frame)
                moved = src_ref.get()
                src_ref.set(self.zero(self._place_type(src, frame)))
                dest_ref.set(moved)

            case ir.Swap(a=a, b=b):
                a_ref = self._place(a, frame)
                b_ref = self._place(b, frame)
                left, right = a_ref.get(), b_ref.get()
                a_ref.set(right)
                b_ref.set(left)

            case ir.Copy(dest=dest, src=src):
                dest_ref = self._place(dest, frame)
                source = self._eval(src, frame)
                if isinstance(source, Frozen):
                    source = source.inner
                dest_ref.set(_deep(source))

            case ir.Freeze(dest=dest, src=src):
                dest_ref = self._place(dest, frame)
                src_ref = self._place(src, frame)
                moved = src_ref.get()
                src_ref.set(self.zero(self._place_type(src, frame)))
                dest_ref.set(Frozen(moved))

            case ir.Push(seq=seq, value=value):
                target = self._sequence(self._place(seq, frame))
                item = self._eval(value, frame)
                if len(target.items) >= target.max:
                    raise Trap("T-05", f"push past the declared maximum {target.max}")
                if len(target.items) == target.cap:
                    target.cap = min(target.max, max(4, 2 * target.cap))
                target.items.append(item)

            case ir.Pop(seq=seq, dest=dest):
                target = self._sequence(self._place(seq, frame))
                dest_ref = self._place(dest, frame)
                if not target.items:
                    raise Trap("T-02", "pop from an empty sequence")
                dest_ref.set(target.items.pop())

            case ir.Truncate(seq=seq, length=length):
                target = self._sequence(self._place(seq, frame))
                wanted = self._eval(length, frame)
                assert isinstance(wanted, int)
                if wanted > len(target.items):
                    raise Trap(
                        "T-03", f"truncate to {wanted}, past the length {len(target.items)}"
                    )
                del target.items[wanted:]

            case ir.Reserve(seq=seq, cap=cap):
                target = self._sequence(self._place(seq, frame))
                wanted = self._eval(cap, frame)
                assert isinstance(wanted, int)
                if wanted > target.max:
                    raise Trap("T-04", f"reserve {wanted}, past the declared maximum {target.max}")
                target.cap = max(target.cap, wanted)

            case ir.If(cond=cond, then=then, otherwise=otherwise):
                self._body(then if self._eval(cond, frame) else otherwise, frame)

            case ir.While(cond=cond, variant=variant, body=body):
                self._while(cond, variant, body, frame)

            case ir.Switch(value=value, arms=arms, default=default):
                tag = self._eval(value, frame)
                assert isinstance(tag, Tag)
                for arm in arms:
                    if arm.variant == tag.variant:
                        self._body(arm.body, frame)
                        return
                assert default is not None, "a validated switch covers every variant"
                self._body(default, frame)

            case ir.Break():
                raise _Break

            case ir.Continue():
                raise _Continue

            case ir.Return(value=value):
                raise _Return(None if value is None else self._eval(value, frame))

            case ir.Call():
                self._call(stmt, frame)

            case _:
                raise AssertionError(f"unhandled statement: {stmt!r}")

    def _while(
        self, cond: ir.Expr, variant: ir.Expr, body: tuple[ir.Stmt, ...], frame: Frame
    ) -> None:
        previous: int | None = None
        while self._eval(cond, frame):
            # A variant that traps is a defect in the program, not a TIR
            # outcome: the backends never evaluate one, so a trap here would be
            # an answer only this interpreter could give. Section 8.6.
            try:
                measure = self._eval(variant, frame)
            except Trap as trapped:
                raise VariantViolation(f"the loop variant trapped: {trapped}") from trapped
            assert isinstance(measure, int)
            if previous is not None and measure >= previous:
                raise VariantViolation(
                    f"the loop variant went from {previous} to {measure}, which is no decrease"
                )
            previous = measure
            try:
                self._body(body, frame)
            except _Break:
                return
            except _Continue:
                continue

    def _call(self, call: ir.Call, frame: Frame) -> None:
        callee = self.p.func_map[call.fn]
        inner = Frame(locals={}, aliases={}, types={})
        for arg, param in zip(call.args, callee.params):
            inner.types[param.name] = param.type
            if isinstance(arg, ir.InArg):
                inner.locals[param.name] = self._eval(arg.expr, frame)
            else:
                inner.aliases[param.name] = self._place(arg.place, frame)
        result: Value | None = None
        try:
            self._body(callee.body, inner)
        except _Return as done:
            result = done.value
        if call.dest is not None:
            self._place(call.dest, frame).set(result)

    def _sequence(self, ref: Ref) -> Seq:
        value = ref.get()
        assert isinstance(value, Seq), f"a sequence statement met {value!r}"
        return value

    # --- places ---

    def _place(self, place: ir.Place, frame: Frame) -> Ref:
        match place:
            case ir.VarPlace(name=name):
                return frame.ref(name)
            case ir.FieldPlace(base=base, name=name):
                container = self._place(base, frame).get()
                assert isinstance(container, StructValue)
                return Ref(container.fields, name)
            case ir.IndexPlace(base=base, index=index):
                container = self._place(base, frame).get()
                position = self._eval(index, frame)
                assert isinstance(container, Seq) and isinstance(position, int)
                if position >= len(container.items):
                    raise Trap(
                        "T-01", f"index {position} into a sequence of {len(container.items)}"
                    )
                return Ref(container.items, position)
        raise AssertionError(f"unhandled place: {place!r}")

    def _place_type(self, place: ir.Place, frame: Frame) -> Type:
        match place:
            case ir.VarPlace(name=name):
                return frame.types[name]
            case ir.FieldPlace(base=base, name=name):
                return self._field_type(self._place_type(base, frame), name)
            case ir.IndexPlace(base=base):
                return element_type(self._place_type(base, frame))
        raise AssertionError(f"unhandled place: {place!r}")

    def _field_type(self, base: Type, name: str) -> Type:
        struct = unfrozen(base)
        assert isinstance(struct, StructType)
        decl = self.p.struct_map[struct.name].field(name)
        assert decl is not None
        return decl.type

    # --- expressions ---

    def _eval(self, e: ir.Expr, frame: Frame) -> Value:
        self._tick()
        match e:
            case ir.Lit(value=value):
                return value

            case ir.Var(name=name):
                return _read(frame.ref(name).get())

            case ir.ConstRef(name=name):
                const = self.p.const_map[name]
                return self._const_value(const.value, const.type)

            case ir.FieldRead(base=base, name=name):
                container = self._eval(base, frame)
                if isinstance(container, Frozen):
                    inner = container.inner
                    assert isinstance(inner, StructValue)
                    value = inner.fields[name]
                    # Section 3.4: a field of a frozen struct comes out frozen
                    # only when it would otherwise be linear. A copyable field
                    # comes out as an ordinary copy, or a write to it would
                    # reach into the frozen value.
                    declared = self._field_type(StructType(inner.type), name)
                    if self.p.types.is_linear(declared):
                        return Frozen(value)
                    return _read(value)
                assert isinstance(container, StructValue)
                return _read(container.fields[name])

            case ir.IndexRead(base=base, index=index):
                container = self._eval(base, frame)
                position = self._eval(index, frame)
                sequence = container.inner if isinstance(container, Frozen) else container
                assert isinstance(sequence, Seq) and isinstance(position, int)
                if position >= len(sequence.items):
                    raise Trap(
                        "T-01", f"index {position} into a sequence of {len(sequence.items)}"
                    )
                return _read(sequence.items[position])

            case ir.Len(arg=arg):
                return len(self._as_sequence(self._eval(arg, frame)).items)

            case ir.Cap(arg=arg):
                return self._as_sequence(self._eval(arg, frame)).cap

            case ir.Unary(op=op, arg=arg):
                return self._unary(op, self._eval(arg, frame), self._type_of(arg, frame))

            case ir.Binary(op=op, left=left, right=right):
                a = self._eval(left, frame)
                b = self._eval(right, frame)
                return self._binary(op, a, b, self._type_of(left, frame))

            case ir.Compare(op=op, left=left, right=right):
                a = self._eval(left, frame)
                b = self._eval(right, frame)
                return self._compare(op, a, b)

            case ir.DivRem(op=op, left=left, right=right, fallback=fallback):
                a = self._eval(left, frame)
                b = self._eval(right, frame)
                f = self._eval(fallback, frame)
                assert isinstance(a, int) and isinstance(b, int)
                if b == 0:
                    return f
                quotient = abs(a) // abs(b)
                if (a < 0) != (b < 0):
                    quotient = -quotient
                if op == "rem":
                    return a - b * quotient
                t = self._type_of(left, frame)
                # Only i32 can leave the range here, through MIN / -1.
                return quotient if t == COUNTER else wrap(t, quotient)

            case ir.Shift(op=op, arg=arg, count=count):
                x = self._eval(arg, frame)
                assert isinstance(x, int)
                if op == "shl":
                    return wrap(self._type_of(arg, frame), x << count)
                # shr is offered only on unsigned types and sar only on i32, so
                # Python's own shift is right in both cases.
                return x >> count

            case ir.Cast(type=t, arg=arg):
                return self._cast(t, self._eval(arg, frame))

            case ir.Logical(op=op, left=left, right=right):
                a = self._eval(left, frame)
                if op == "and":
                    return self._eval(right, frame) if a else False
                return True if a else self._eval(right, frame)

            case ir.EnumVal(type=name, variant=variant):
                return Tag(name, variant)

            case ir.StructVal(type=name, fields=fields):
                given = dict(fields)
                decl = self.p.struct_map[name]
                # In the struct's declared order, which is what section 13 pins.
                return StructValue(
                    name, {f.name: self._eval(given[f.name], frame) for f in decl.fields}
                )

        raise AssertionError(f"unhandled expression: {e!r}")

    def _as_sequence(self, v: Value) -> Seq:
        sequence = v.inner if isinstance(v, Frozen) else v
        assert isinstance(sequence, Seq)
        return sequence

    def _const_value(self, value: ir.ConstValue, t: Type) -> Value:
        if isinstance(t, FrozenType):
            return Frozen(self._const_value(value, t.inner))
        if isinstance(value, ir.EnumConst):
            assert isinstance(t, EnumType)
            return Tag(t.name, value.variant)
        if isinstance(value, ir.BytesConst):
            return Seq(U8, CEILING, list(value.data), len(value.data))
        if isinstance(value, ir.VecConst):
            assert isinstance(t, VecType)
            items = [self._const_value(v, t.elem) for v in value.elems]
            return Seq(t.elem, t.max, items, len(items))
        if isinstance(value, ir.StructConst):
            assert isinstance(t, StructType)
            given = dict(value.fields)
            decl = self.p.struct_map[t.name]
            return StructValue(
                t.name, {f.name: self._const_value(given[f.name], f.type) for f in decl.fields}
            )
        return value

    # --- operators ---

    def _unary(self, op: str, x: Value, t: Type) -> Value:
        if op == "not":
            assert isinstance(x, bool)
            return not x
        assert isinstance(x, int)
        return wrap(t, -x if op == "neg" else ~x)

    def _binary(self, op: str, a: Value, b: Value, t: Type) -> Value:
        assert isinstance(a, int) and isinstance(b, int)
        if t == COUNTER:
            # The pre-checked saturation of section 6.7, written the way the
            # spec states it rather than as add-then-clamp.
            if op == "add":
                return CAP if a > CAP - b else a + b
            if op == "sub":
                return 0 if a < b else a - b
            if op == "mul":
                if a == 0 or b == 0:
                    return 0
                return CAP if a > CAP // b else a * b
            raise AssertionError(f"counter has no {op}")
        match op:
            case "add":
                return wrap(t, a + b)
            case "sub":
                return wrap(t, a - b)
            case "mul":
                return wrap(t, a * b)
            # Bitwise operations run on the two's-complement patterns, which is
            # what Python's own operators do on the signed values.
            case "and":
                return wrap(t, a & b)
            case "or":
                return wrap(t, a | b)
            case "xor":
                return wrap(t, a ^ b)
        raise AssertionError(f"unhandled binary operator: {op}")

    def _compare(self, op: str, a: Value, b: Value) -> bool:
        if isinstance(a, Tag):
            assert isinstance(b, Tag)
            return a.variant == b.variant if op == "eq" else a.variant != b.variant
        assert isinstance(a, (bool, int)) and isinstance(b, (bool, int))
        match op:
            case "eq":
                return a == b
            case "ne":
                return a != b
            case "lt":
                return a < b
            case "le":
                return a <= b
            case "gt":
                return a > b
            case "ge":
                return a >= b
        raise AssertionError(f"unhandled comparison: {op}")

    def _cast(self, t: Type, x: Value) -> Value:
        value = int(x) if isinstance(x, bool) else x
        assert isinstance(value, int)
        # counter is unsigned and counts things, so a negative i32 lands at 0
        # rather than reinterpreting; anything else truncates.
        return max(0, value) if t == COUNTER else wrap(t, value)

    # --- static types, for the operators whose width matters ---

    def _type_of(self, e: ir.Expr, frame: Frame) -> Type:
        match e:
            case ir.Lit(type=t) | ir.Cast(type=t):
                return t
            case ir.Len() | ir.Cap():
                return U32
            case ir.Compare() | ir.Logical():
                return BOOL
            case ir.Unary(op=op, arg=arg):
                return BOOL if op == "not" else self._type_of(arg, frame)
            case ir.Shift(arg=arg):
                return self._type_of(arg, frame)
            case ir.Binary(left=left) | ir.DivRem(left=left):
                return self._type_of(left, frame)
            case ir.Var(name=name):
                return frame.types[name]
            case ir.ConstRef(name=name):
                return self.p.const_map[name].type
            case ir.FieldRead(base=base, name=name):
                return self._field_type(self._type_of(base, frame), name)
            case ir.IndexRead(base=base):
                return element_type(self._type_of(base, frame))
            case ir.StructVal(type=name):
                return StructType(name)
            case ir.EnumVal(type=name):
                return EnumType(name)
        raise AssertionError(f"unhandled expression: {e!r}")


def run(
    program: ir.Program,
    name: str,
    args: list[Value | Cell] | None = None,
    fuel: int = DEFAULT_FUEL,
) -> Value | None:
    """Call one function of a validated program."""
    return Interpreter(program, fuel=fuel).call(name, args or [])


__all__ = [
    "Cell",
    "Frozen",
    "Interpreter",
    "OutOfFuel",
    "Seq",
    "StructValue",
    "Tag",
    "Trap",
    "VariantViolation",
    "run",
]
