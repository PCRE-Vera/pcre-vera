"""TIR to Go.

A syntax-directed printer and nothing else: one output construct per input
node, no optimization, no reordering, no cleverness. Its smallness is the
trust argument (DESIGN.md section 7), so anything that would make it larger
has to earn its place.

Three obligations of TIR-SPEC.md section 16 are worth pointing at, because
they are where the obvious lowering is wrong rather than merely ugly.

The first is that an assignment to an element bounds-checks the destination
*before* it evaluates the value. Go's own order is the other way round, so the
check is emitted rather than left to the language.

The second is that sequences never go through `append`. A raw append
reallocates and then discovers it was over the limit, which would report the
wrong peak to the M5 analyzer; the generated helpers check first and allocate
afterwards, on the growth schedule of TIR-SPEC.md section 11. A Go slice
carries both numbers that schedule talks about — `len` is the TIR length and
`cap` the TIR capacity — so the mapping is exact rather than approximate.

The third is that Go's constant expressions do not wrap: `uint8(200) +
uint8(100)` is a compile error where TIR says 44. Any arithmetic whose
operands are all literals therefore has one operand passed through `tir_k`,
which is the identity and is not a constant expression, so the whole thing
becomes ordinary runtime arithmetic and wraps the way it should.

Names are printed verbatim, which is only safe because the generated package
holds nothing else (TIR-SPEC.md section 16). Go being what it is, the wrapper
in the neighbouring package cannot reach a lower-case name, so the printer
also emits an exported façade — `Tir_`-prefixed forwarders and field readers —
and refuses any program whose own names would collide with it.

The output is the printer's own formatting rather than gofmt's. Running gofmt
over it would produce a diff, which is the right answer for a file that says
DO NOT EDIT at the top, and keeping the two in step would mean reproducing
go/printer's expression-spacing rules here for no gain.
"""

from __future__ import annotations

from ...tir import ir
from ...tir.types import (
    BOOL,
    BYTES,
    COUNTER,
    I32,
    U8,
    U32,
    EnumType,
    FrozenType,
    Prim,
    StructType,
    Type,
    VecType,
    declared_max,
    element_type,
    unfrozen,
)
from ..support import (
    Types,
    banner,
    declared_names,
    has_jump,
    hoisted,
    plan_copies,
    reads,
    terminates,
    type_tag,
)

FACADE_PREFIX = "Tir_"
"""What the exported façade puts in front of a TIR name.

Go can only export a name that starts with a capital, so the façade cannot use
the `tir_` prefix the helpers use. Rule V-043 reserves both, so a validated
program cannot collide with either; `_check_names` says so again, because a
printer that trusted its input would be the one place where "validated" and
"printable" could quietly come apart.
"""

OWN_NAMES = frozenset({"ArtifactSHA256"})
"""Package-level names the printer emits with no prefix at all, also in V-043."""

PRIMS = {
    "bool": "bool",
    "u8": "uint8",
    "i32": "int32",
    "u32": "uint32",
    "counter": "uint64",
    "bytes": "[]byte",
}

BINARY = {"add": "+", "sub": "-", "mul": "*", "and": "&", "or": "|", "xor": "^"}
COMPARE = {"eq": "==", "ne": "!=", "lt": "<", "le": "<=", "gt": ">", "ge": ">="}
SHIFT = {"shl": "<<", "shr": ">>", "sar": ">>"}

WRAPPING = frozenset({"add", "sub", "mul"})
"""The operators whose constant form Go refuses to wrap."""

TRAP_NOTE = (
    "A tir_ helper panics where TIR-SPEC.md section 12 says a checked operation "
    "traps. A trap is an engine bug rather than a caller error, so it fails loudly "
    "instead of reading past the end of an array."
)

ENGINE_SUMMARY = (
    "The wave 1 pcre-vera engine as printed from its TIR artifact: the pattern "
    "parser, the bytecode compiler, and the backtracking matcher. The public API "
    "lives in the package next door."
)


class GoError(Exception):
    """The program cannot be printed as Go without inventing a rule."""


def render(
    program: ir.Program,
    sha256: str,
    *,
    package: str = "engine",
    origin: str = "engine.tir.json",
    summary: str = ENGINE_SUMMARY,
) -> str:
    """The generated Go package, as one file."""
    return _Printer(program, sha256, package, origin, summary).run()


def _go_type(t: Type) -> str:
    if isinstance(t, Prim):
        return PRIMS[t.name]
    if isinstance(t, (EnumType, StructType)):
        return t.name
    if isinstance(t, VecType):
        return "[]" + _go_type(t.elem)
    if isinstance(t, FrozenType):
        return _go_type(t.inner)
    raise GoError(f"not a TIR type: {t!r}")


def _is_go_const(t: Type) -> bool:
    """Whether a TIR constant of this type is emitted with Go's `const` keyword.

    A sequence or a struct cannot be one, so those go out as package variables
    instead. `_const` and `_const_only` both ask this, and they have to get the
    same answer: the first decides what is emitted, the second decides whether
    Go will evaluate a use of it at compile time.
    """
    inner = unfrozen(t)
    return not (inner == BYTES or isinstance(inner, (VecType, StructType)))


class _Printer:
    def __init__(
        self, program: ir.Program, sha256: str, package: str, origin: str, summary: str
    ) -> None:
        self.p = program
        self.sha = sha256
        self.package = package
        self.origin = origin
        self.summary = summary
        self.out: list[str] = []
        self.copies: dict[str, Type] = {}
        self.types: Types
        self.read_names: set[str] = set()
        self.inout: set[str] = set()
        self.temps = 0
        self.labels = 0
        self.loops: list[str | None] = []

    def line(self, depth: int, text: str = "") -> None:
        self.out.append(("\t" * depth + text) if text else "")

    def run(self) -> str:
        self._check_names()
        self._header()
        self.out.append(SUPPORT.strip("\n"))
        self.line(0)
        for enum in self.p.enums:
            self._enum(enum)
        for struct in self.p.structs:
            self._struct(struct)
        for const in self.p.consts:
            self._const(const)
        for func in self.p.funcs:
            self._func(func)
        self._copy_helpers()
        self._facade()
        return "\n".join(self.out).rstrip("\n") + "\n"

    def _check_names(self) -> None:
        """Rule V-043 again, from the side that would suffer if it were wrong."""
        for name in declared_names(self.p):
            if name in OWN_NAMES or name.startswith(FACADE_PREFIX):
                raise GoError(
                    f"{name!r} collides with a name the Go printer emits: nothing "
                    f"may start with {FACADE_PREFIX!r} or be called "
                    f"{', '.join(sorted(OWN_NAMES))}"
                )

    def _header(self) -> None:
        comment = banner(self.origin, self.sha, self.summary, "package", TRAP_NOTE)
        lines = [("// " + line).rstrip() for line in comment]
        lines += [
            "",
            f"package {self.package}",
            "",
            "// ArtifactSHA256 is the SHA-256 of the TIR artifact this package was printed",
            "// from.",
            f'const ArtifactSHA256 = "{self.sha}"',
            "",
        ]
        for text in lines:
            self.line(0, text)

    # --- declarations ---

    def _enum(self, decl: ir.EnumDecl) -> None:
        self.line(0, f"type {decl.name} int32")
        self.line(0)
        for ordinal, variant in enumerate(decl.variants):
            self.line(0, f"const {variant} {decl.name} = {ordinal}")
        self.line(0)

    def _struct(self, decl: ir.StructDecl) -> None:
        self.line(0, f"type {decl.name} struct {{")
        for field in decl.fields:
            self.line(1, f"{field.name} {_go_type(field.type)}")
        self.line(0, "}")
        self.line(0)

    def _const(self, decl: ir.Const) -> None:
        text = self._const_value(decl.value, decl.type, 0)
        if _is_go_const(decl.type):
            self.line(0, f"const {decl.name} {_go_type(decl.type)} = {text}")
        else:
            # No Go constant can hold a sequence or a struct, so these are
            # package variables that nothing writes; the frozen type is what
            # says nothing may.
            self.line(0, f"var {decl.name} = {text}")
        self.line(0)

    def _const_value(self, value: ir.ConstValue, t: Type, depth: int) -> str:
        inner = unfrozen(t)
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, int):
            return str(value)
        if isinstance(value, ir.EnumConst):
            return value.variant
        if isinstance(value, ir.BytesConst):
            return self._bytes_literal(value.data, depth)
        if isinstance(value, ir.VecConst):
            assert isinstance(inner, VecType)
            items = [self._const_value(v, inner.elem, depth + 1) for v in value.elems]
            return self._block_literal(_go_type(inner), items, depth)
        assert isinstance(value, ir.StructConst) and isinstance(inner, StructType)
        given = dict(value.fields)
        items = [
            f"{f.name}: {self._const_value(given[f.name], f.type, depth + 1)}"
            for f in self.p.struct_map[inner.name].fields
        ]
        return self._block_literal(inner.name, items, depth)

    def _bytes_literal(self, data: bytes, depth: int) -> str:
        if not data:
            return "[]byte{}"
        pad = "\t" * (depth + 1)
        rows = [
            pad + " ".join(f"0x{byte:02x}," for byte in data[at : at + 12])
            for at in range(0, len(data), 12)
        ]
        return "[]byte{\n" + "\n".join(rows) + "\n" + "\t" * depth + "}"

    def _block_literal(self, kind: str, items: list[str], depth: int) -> str:
        if not items:
            return kind + "{}"
        pad = "\t" * (depth + 1)
        rows = "\n".join(f"{pad}{item}," for item in items)
        return f"{kind}{{\n{rows}\n" + "\t" * depth + "}"

    # --- functions ---

    def _signature(self, f: ir.Func) -> str:
        params = ", ".join(
            f"{p.name} {'*' if p.mode == 'inout' else ''}{_go_type(p.type)}" for p in f.params
        )
        return f"({params})" + ("" if f.ret is None else " " + _go_type(f.ret))

    def _func(self, f: ir.Func) -> None:
        self.types = Types(self.p, f)
        self.read_names = reads(f)
        self.inout = {p.name for p in f.params if p.mode == "inout"}
        self.temps = 0
        self.labels = 0
        self.loops = []
        self.line(0, f"func {f.name}{self._signature(f)} {{")
        self._body(f.body, 1)
        if f.ret is not None and not terminates(f.body):
            self.line(1, "panic(tir_fellOff)")
        self.line(0, "}")
        self.line(0)

    def _body(self, body: tuple[ir.Stmt, ...], depth: int) -> None:
        for stmt in body:
            self._stmt(stmt, depth)

    def _temp(self) -> str:
        self.temps += 1
        return f"tir_t{self.temps}"

    def _stmt(self, s: ir.Stmt, depth: int) -> None:
        match s:
            case ir.Let(name=name, type=t, init=init):
                declared = f"var {name} {_go_type(t)}"
                self.line(depth, declared if init is None else f"{declared} = {self._expr(init)}")
                if name not in self.read_names:
                    # Go refuses a variable nothing reads, and TIR does not.
                    self.line(depth, f"_ = {name}")

            case ir.Assign(place=place, value=value):
                target = self._place(place, depth)
                self.line(depth, f"{target} = {self._expr(value)}")

            case ir.Take(dest=dest, src=src) | ir.Freeze(dest=dest, src=src):
                target = self._place(dest, depth)
                source = self._place(src, depth)
                self.line(depth, f"{target} = {source}")
                self.line(depth, f"{source} = {self._zero(self.types.place(src))}")

            case ir.Swap(a=a, b=b):
                left = self._place(a, depth)
                right = self._place(b, depth)
                held = self._temp()
                self.line(depth, f"{held} := {left}")
                self.line(depth, f"{left} = {right}")
                self.line(depth, f"{right} = {held}")

            case ir.Copy(dest=dest, src=src):
                target = self._place(dest, depth)
                helper = self._copy_helper(self.types.place(dest))
                self.line(depth, f"{target} = {helper}({self._expr(src)})")

            case ir.Push(seq=seq, value=value):
                target = self._place(seq, depth)
                limit = declared_max(self.types.place(seq))
                self.line(depth, f"tir_push(&{target}, {limit}, {self._expr(value)})")

            case ir.Pop(seq=seq, dest=dest):
                source = self._place(seq, depth)
                target = self._place(dest, depth)
                self.line(depth, f"{target} = tir_pop(&{source})")

            case ir.Truncate(seq=seq, length=length):
                target = self._place(seq, depth)
                self.line(depth, f"tir_truncate(&{target}, {self._expr(length)})")

            case ir.Reserve(seq=seq, cap=cap):
                target = self._place(seq, depth)
                limit = declared_max(self.types.place(seq))
                self.line(depth, f"tir_reserve(&{target}, {self._expr(cap)}, {limit})")

            case ir.If(cond=cond, then=then, otherwise=otherwise):
                self.line(depth, f"if {self._expr(cond)} {{")
                self._body(then, depth + 1)
                if otherwise:
                    self.line(depth, "} else {")
                    self._body(otherwise, depth + 1)
                self.line(depth, "}")

            case ir.While(cond=cond, body=body):
                label = None
                if has_jump(body):
                    # A TIR break belongs to the loop even inside a switch arm,
                    # where a bare Go break would belong to the switch.
                    self.labels += 1
                    label = f"tir_loop{self.labels}"
                    self.line(depth, f"{label}:")
                self.line(depth, f"for {self._expr(cond)} {{")
                self.loops.append(label)
                self._body(body, depth + 1)
                self.loops.pop()
                self.line(depth, "}")

            case ir.Switch(value=value, arms=arms, default=default):
                self.line(depth, f"switch {self._expr(value)} {{")
                for arm in arms:
                    self.line(depth, f"case {arm.variant}:")
                    self._body(arm.body, depth + 1)
                if default is not None:
                    self.line(depth, "default:")
                    self._body(default, depth + 1)
                self.line(depth, "}")

            case ir.Break():
                label = self.loops[-1]
                self.line(depth, f"break {label}" if label else "break")

            case ir.Continue():
                label = self.loops[-1]
                self.line(depth, f"continue {label}" if label else "continue")

            case ir.Return(value=value):
                self.line(depth, "return" if value is None else f"return {self._expr(value)}")

            case ir.Call(fn=fn, args=args, dest=dest):
                call = f"{fn}({', '.join(self._args(args, depth))})"
                if dest is None:
                    self.line(depth, call)
                else:
                    # The destination place is resolved after the call, not
                    # before it, which is the order section 13 pins.
                    held = self._temp()
                    self.line(depth, f"{held} := {call}")
                    self.line(depth, f"{self._place(dest, depth)} = {held}")

            case _:
                raise GoError(f"not a TIR statement: {s!r}")

    def _args(self, args: tuple[ir.Arg, ...], depth: int) -> list[str]:
        """The arguments, resolved strictly left to right."""
        rendered = []
        for arg, first in zip(args, hoisted(args)):
            if not first:
                rendered.append(self._arg(arg, depth))
                continue
            assert isinstance(arg, ir.InArg)
            held = self._temp()
            self.line(depth, f"{held} := {self._expr(arg.expr)}")
            rendered.append(held)
        return rendered

    def _arg(self, arg: ir.Arg, depth: int) -> str:
        if isinstance(arg, ir.InArg):
            return self._expr(arg.expr)
        place = arg.place
        if isinstance(place, ir.VarPlace) and place.name in self.inout:
            return place.name
        return "&" + self._place(place, depth)

    # --- places ---

    def _place(self, p: ir.Place, depth: int) -> str:
        match p:
            case ir.VarPlace(name=name):
                return f"(*{name})" if name in self.inout else name
            case ir.FieldPlace(base=base, name=name):
                return f"{self._place(base, depth)}.{name}"
            case ir.IndexPlace(base=base, index=index):
                container = self._place(base, depth)
                at = self._temp()
                self.line(depth, f"{at} := {self._expr(index)}")
                self.line(depth, f"if {at} >= uint32(len({container})) {{")
                self.line(depth + 1, f"tir_oob({at}, uint32(len({container})))")
                self.line(depth, "}")
                return f"{container}[{at}]"
        raise GoError(f"not a TIR place: {p!r}")

    # --- expressions ---

    def _const_only(self, e: ir.Expr) -> bool:
        """Whether Go would evaluate this expression at compile time.

        It refuses the overflow TIR defines when it does, so this is where
        `tir_k` gets inserted. A named constant counts: the printer emits a
        scalar one with `const`, which makes every use of it a constant
        expression exactly as a literal is. The imprecision falls the harmless
        way — an extra `tir_k` costs nothing, a missing one is a build error —
        and only the operands `_guard` reaches can arrive here.
        """
        match e:
            case ir.Lit():
                return True
            case ir.ConstRef(name=name):
                return _is_go_const(self.p.const_map[name].type)
            case ir.Unary(arg=arg) | ir.Cast(arg=arg) | ir.Shift(arg=arg):
                return self._const_only(arg)
            case ir.Binary(left=left, right=right):
                return self._const_only(left) and self._const_only(right)
        return False

    def _guard(self, e: ir.Expr, text: str) -> str:
        return f"tir_k({text})" if self._const_only(e) else text

    def _expr(self, e: ir.Expr) -> str:
        match e:
            case ir.Lit(type=t, value=value):
                if t == BOOL:
                    return "true" if value else "false"
                return f"{_go_type(t)}({value})"

            case ir.Var(name=name):
                return f"(*{name})" if name in self.inout else name

            case ir.ConstRef(name=name):
                return name

            case ir.FieldRead(base=base, name=name):
                return f"{self._expr(base)}.{name}"

            case ir.IndexRead(base=base, index=index):
                return f"{self._expr(base)}[{self._expr(index)}]"

            case ir.Len(arg=arg):
                return f"uint32(len({self._expr(arg)}))"

            case ir.Cap(arg=arg):
                return f"uint32(cap({self._expr(arg)}))"

            case ir.Unary(op=op, arg=arg):
                text = self._expr(arg)
                if op == "not":
                    return f"(!{text})"
                return f"({'-' if op == 'neg' else '^'}{self._guard(arg, text)})"

            case ir.Binary(op=op, left=left, right=right):
                a, b = self._expr(left), self._expr(right)
                if self.types.of(left) == COUNTER:
                    return f"tir_c{op}({a}, {b})"
                return f"({self._guard(left, a) if op in WRAPPING else a} {BINARY[op]} {b})"

            case ir.Compare(op=op, left=left, right=right):
                return f"({self._expr(left)} {COMPARE[op]} {self._expr(right)})"

            case ir.DivRem(op=op, left=left, right=right, fallback=fallback):
                suffix = type_tag(self.types.of(left))
                return (
                    f"tir_{op}_{suffix}({self._expr(left)}, {self._expr(right)}, "
                    f"{self._expr(fallback)})"
                )

            case ir.Shift(op=op, arg=arg, count=count):
                text = self._expr(arg)
                if op == "shl":
                    text = self._guard(arg, text)
                return f"({text} {SHIFT[op]} {count})"

            case ir.Cast(type=t, arg=arg):
                source = self.types.of(arg)
                text = self._expr(arg)
                if source == BOOL:
                    return f"tir_b({text})" if t == COUNTER else f"{_go_type(t)}(tir_b({text}))"
                if t == COUNTER and source == I32:
                    return f"tir_c({text})"
                return f"{_go_type(t)}({self._guard(arg, text)})"

            case ir.Logical(op=op, left=left, right=right):
                symbol = "&&" if op == "and" else "||"
                return f"({self._expr(left)} {symbol} {self._expr(right)})"

            case ir.EnumVal(variant=variant):
                return variant

            case ir.StructVal(type=name, fields=fields):
                given = dict(fields)
                assigned = ", ".join(
                    f"{f.name}: {self._expr(given[f.name])}"
                    for f in self.p.struct_map[name].fields
                )
                # Parenthesized, because an unparenthesized composite literal
                # is ambiguous in an if or for header.
                return f"({name}{{{assigned}}})"

        raise GoError(f"not a TIR expression: {e!r}")

    def _zero(self, t: Type) -> str:
        inner = unfrozen(t)
        if inner == BOOL:
            return "false"
        if inner in (U8, I32, U32, COUNTER):
            return f"{_go_type(inner)}(0)"
        if inner == BYTES or isinstance(inner, VecType):
            return "nil"
        if isinstance(inner, EnumType):
            return self.p.enum_map[inner.name].variants[0]
        assert isinstance(inner, StructType)
        return f"{inner.name}{{}}"

    # --- deep copy, one helper per type a copy statement reaches ---

    def _copy_helper(self, t: Type) -> str:
        return plan_copies(self.p, t, self.copies)

    def _copy_helpers(self) -> None:
        # Registering a type registers everything it reaches, so the plan is
        # complete before the first helper is written.
        for tag, t in list(self.copies.items()):
            self._one_copy_helper(t, "tir_copy_" + tag)

    def _one_copy_helper(self, t: Type, name: str) -> None:
        go = _go_type(t)
        self.line(0, f"func {name}(s {go}) {go} {{")
        if isinstance(t, FrozenType):
            # Freezing bought sharing and a deep copy keeps it: nothing under a
            # frozen value can change, so duplicating it would only cost.
            self.line(1, "return s")
        elif t == BYTES or isinstance(t, VecType):
            self.line(1, f"d := make({go}, len(s), len(s))")
            self.line(1, "for i := range s {")
            self.line(2, f"d[i] = {self._copy_helper(element_type(t))}(s[i])")
            self.line(1, "}")
            self.line(1, "return d")
        elif isinstance(t, StructType):
            self.line(1, f"var d {go}")
            for field in self.p.struct_map[t.name].fields:
                helper = self._copy_helper(field.type)
                self.line(1, f"d.{field.name} = {helper}(s.{field.name})")
            self.line(1, "return d")
        else:
            self.line(1, "return s")
        self.line(0, "}")
        self.line(0)

    # --- the exported façade ---

    def _facade(self) -> None:
        for text in (
            "// The exported façade. Go cannot reach a lower-case name from another",
            "// package and TIR names are printed verbatim, so the wrapper next door",
            "// talks to the program through these. They add no behaviour of their own.",
            "",
        ):
            self.line(0, text)
        for f in self.p.funcs:
            arguments = ", ".join(p.name for p in f.params)
            self.line(0, f"func {FACADE_PREFIX}{f.name}{self._signature(f)} {{")
            self.line(1, f"{'return ' if f.ret is not None else ''}{f.name}({arguments})")
            self.line(0, "}")
            self.line(0)
        for decl in self.p.structs:
            readable = [f for f in decl.fields if not self.p.types.is_linear(f.type)]
            for field in readable:
                self.line(
                    0,
                    f"func (v *{decl.name}) {FACADE_PREFIX}{field.name}() "
                    f"{_go_type(field.type)} {{ return v.{field.name} }}",
                )
            if readable:
                self.line(0)


SUPPORT = r"""
// Tir_Trap is what a checked operation panics with, per TIR-SPEC.md section 12.
type Tir_Trap struct {
	Code  string
	What  string
	Index uint32
	Bound uint32
}

func (t Tir_Trap) Error() string {
	return "pcrevera: TIR trap " + t.Code + ": " + t.What
}

const tir_CAP uint64 = 9007199254740991

const tir_fellOff = "pcrevera: a value-returning function reached its end"

func tir_oob(index uint32, bound uint32) {
	panic(Tir_Trap{Code: "T-01", What: "index past the end of a sequence", Index: index, Bound: bound})
}

// tir_k is the identity. It stands between a literal and an operator whose Go
// constant form would refuse to wrap, and it costs nothing once inlined.
func tir_k[T any](x T) T { return x }

func tir_b(x bool) uint64 {
	if x {
		return 1
	}
	return 0
}

// tir_c is the i32-to-counter cast: a count has no negative reading, so a
// negative operand lands at zero rather than being reinterpreted.
func tir_c(x int32) uint64 {
	if x < 0 {
		return 0
	}
	return uint64(x)
}

// The three counter operators of TIR-SPEC.md section 6.7, checked before the
// arithmetic rather than clamped after it.
func tir_cadd(a uint64, b uint64) uint64 {
	if a > tir_CAP-b {
		return tir_CAP
	}
	return a + b
}

func tir_csub(a uint64, b uint64) uint64 {
	if a < b {
		return 0
	}
	return a - b
}

func tir_cmul(a uint64, b uint64) uint64 {
	if a == 0 || b == 0 {
		return 0
	}
	if a > tir_CAP/b {
		return tir_CAP
	}
	return a * b
}

// Division and remainder, with a zero divisor answered by the fallback and the
// two i32 corners that would otherwise be a runtime panic.
func tir_div_u8(a uint8, b uint8, f uint8) uint8 {
	if b == 0 {
		return f
	}
	return a / b
}

func tir_rem_u8(a uint8, b uint8, f uint8) uint8 {
	if b == 0 {
		return f
	}
	return a % b
}

func tir_div_u32(a uint32, b uint32, f uint32) uint32 {
	if b == 0 {
		return f
	}
	return a / b
}

func tir_rem_u32(a uint32, b uint32, f uint32) uint32 {
	if b == 0 {
		return f
	}
	return a % b
}

func tir_div_counter(a uint64, b uint64, f uint64) uint64 {
	if b == 0 {
		return f
	}
	return a / b
}

func tir_rem_counter(a uint64, b uint64, f uint64) uint64 {
	if b == 0 {
		return f
	}
	return a % b
}

func tir_div_i32(a int32, b int32, f int32) int32 {
	if b == 0 {
		return f
	}
	if b == -1 {
		return -a
	}
	return a / b
}

func tir_rem_i32(a int32, b int32, f int32) int32 {
	if b == 0 {
		return f
	}
	if b == -1 {
		return 0
	}
	return a % b
}

// Sequences. A Go slice already carries the two numbers the growth schedule of
// TIR-SPEC.md section 11 talks about: len is the TIR length and cap the TIR
// capacity. Every allocation goes through tir_grow, which copies into a fresh
// buffer rather than reallocating in place, because the memory accounting
// counts both buffers as live at once.
func tir_grow[T any](s []T, capacity int) []T {
	grown := make([]T, len(s), capacity)
	copy(grown, s)
	return grown
}

func tir_push[T any](s *[]T, limit int, v T) {
	n := len(*s)
	if n >= limit {
		panic(Tir_Trap{Code: "T-05", What: "push past the declared maximum", Index: uint32(n), Bound: uint32(limit)})
	}
	if n == cap(*s) {
		capacity := 2 * cap(*s)
		if capacity < 4 {
			capacity = 4
		}
		if capacity > limit {
			capacity = limit
		}
		*s = tir_grow(*s, capacity)
	}
	*s = (*s)[:n+1]
	(*s)[n] = v
}

func tir_pop[T any](s *[]T) T {
	n := len(*s)
	if n == 0 {
		panic(Tir_Trap{Code: "T-02", What: "pop from an empty sequence", Index: 0, Bound: 0})
	}
	v := (*s)[n-1]
	*s = (*s)[:n-1]
	return v
}

func tir_truncate[T any](s *[]T, length uint32) {
	if uint64(length) > uint64(len(*s)) {
		panic(Tir_Trap{Code: "T-03", What: "truncate past the current length", Index: length, Bound: uint32(len(*s))})
	}
	*s = (*s)[:length]
}

func tir_reserve[T any](s *[]T, capacity uint32, limit int) {
	if uint64(capacity) > uint64(limit) {
		panic(Tir_Trap{Code: "T-04", What: "reserve past the declared maximum", Index: capacity, Bound: uint32(limit)})
	}
	if uint64(capacity) > uint64(cap(*s)) {
		*s = tir_grow(*s, int(capacity))
	}
}
"""

__all__ = ["GoError", "render"]
