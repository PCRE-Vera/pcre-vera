"""TIR to JavaScript.

The same syntax-directed printer as the Go one, against a language that gets
four things wrong if you lower TIR naively. TIR-SPEC.md section 16 names them
and the conformance suite aims at each.

Multiplication goes through `Math.imul`. A plain double product of two 32-bit
operands loses low bits above 2^53, and it loses them *before* any `| 0` or
`>>> 0` can look at them, so the coercion cannot repair what the multiply
already threw away. Everything else is coerced on the way out: `& 255` for u8,
`| 0` for i32, `>>> 0` for u32, so a value is always in its type's range and
comparisons can stay the plain JavaScript ones.

Indexing is checked explicitly. A typed array reads `undefined` past its end
instead of failing, which would turn a trap into a silently wrong answer, so
`tir_at` and `tir_bound` are emitted rather than relying on the language.

A copyable struct is cloned when it is read out of storage. A class instance
is a reference, so `q = p` would alias where Go copies, and a later write
through `q` would show up in `p`. Every read whose type is a struct emits a
field-by-field clone; the frozen values inside it are shared, not cloned,
which is exactly what freezing bought.

Sequences are a backing store plus an explicit length, because a typed array
has no length of its own that could carry the TIR one, and because the growth
schedule of TIR-SPEC.md section 11 needs the capacity to be a number the
program controls rather than one the host picks. The store is fixed per
element type, not left to the printer's mood.

Two smaller things. An `inout` parameter is a one-field cell in every case,
not only for scalars: a callee may `take` or `assign` the whole parameter, and
passing the object itself would leave that write in the callee's local. And a
`switch` is printed as an if-chain rather than a JavaScript switch, because
JavaScript cases fall through, share one block scope, and would swallow the
`break` that TIR means for the enclosing loop.
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
    hoisted,
    plan_copies,
    type_tag,
)

GLOBALS = frozenset(
    {"Array", "Error", "Float64Array", "Int32Array", "Math", "Uint32Array", "Uint8Array"}
)
"""The host names the generated module reads.

A TIR name is printed verbatim, so one of these would shadow the global the
printer needs — `Math.imul` is the loud example, and a *parameter* called Math
shadows it just as thoroughly as a function would. Rule V-043 reserves them,
so a validated program cannot arrive with one; `_check_names` says so again,
because a printer that trusted its input would be the one place where
"validated" and "printable" could quietly come apart.
"""

OWN_NAMES = frozenset({"artifactSha256"})
"""Module-level names the printer emits itself, also in V-043."""

COMPARE = {"eq": "===", "ne": "!==", "lt": "<", "le": "<=", "gt": ">", "ge": ">="}
BITWISE = {"and": "&", "or": "|", "xor": "^"}

# What each type's values are coerced back into after an operation. `counter`
# is absent because every counter operator is a helper that stays in range.
COERCE = {U8: "& 255", I32: "| 0", U32: ">>> 0"}

STORES = {
    "u8": ("tir_mk_u8", "tir_EMPTY_U8"),
    "i32": ("tir_mk_i32", "tir_EMPTY_I32"),
    "u32": ("tir_mk_u32", "tir_EMPTY_U32"),
    "counter": ("tir_mk_f64", "tir_EMPTY_F64"),
    "bool": ("tir_mk_bool", "tir_EMPTY_BOOL"),
    "obj": ("tir_mk_obj", "tir_EMPTY_OBJ"),
}


TRAP_NOTE = (
    "A tir_Trap is thrown where TIR-SPEC.md section 12 says a checked operation "
    "traps. A trap is an engine bug rather than a caller error, so it fails loudly "
    "instead of reading undefined off the end of a typed array."
)

ENGINE_SUMMARY = (
    "The wave 1 pcre-vera engine as printed from its TIR artifact: the pattern "
    "parser, the bytecode compiler, and the backtracking matcher. The public API "
    "is the hand-written wrapper in index.mjs."
)


class JsError(Exception):
    """The program cannot be printed as JavaScript without inventing a rule."""


def render(
    program: ir.Program,
    sha256: str,
    *,
    origin: str = "engine.tir.json",
    summary: str = ENGINE_SUMMARY,
) -> str:
    """The generated ES module, as one file."""
    return _Printer(program, sha256, origin, summary).run()


def _store(elem: Type) -> tuple[str, str]:
    """The backing store an element type lives in, as (maker, empty)."""
    if isinstance(elem, Prim) and elem.name in STORES:
        return STORES[elem.name]
    if isinstance(elem, EnumType):
        return STORES["i32"]
    return STORES["obj"]


def _maker(elem: Type) -> str:
    """What allocates a backing store of this element type."""
    return _store(elem)[0]


def _empty(elem: Type) -> str:
    """The shared zero-capacity store of this element type, which nothing writes."""
    return _store(elem)[1]


class _Printer:
    def __init__(self, program: ir.Program, sha256: str, origin: str, summary: str) -> None:
        self.p = program
        self.sha = sha256
        self.origin = origin
        self.summary = summary
        self.out: list[str] = []
        self.copies: dict[str, Type] = {}
        self.types: Types
        self.inout: set[str] = set()
        self.temps = 0

    def line(self, depth: int, text: str = "") -> None:
        self.out.append(("  " * depth + text) if text else "")

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
        self._factories()
        return "\n".join(self.out).rstrip("\n") + "\n"

    def _check_names(self) -> None:
        """Rule V-043 again, from the side that would suffer if it were wrong."""
        clashing = sorted(set(declared_names(self.p)) & (GLOBALS | OWN_NAMES))
        if clashing:
            raise JsError(
                f"{', '.join(clashing)} would shadow a name the generated module "
                f"needs; nothing may be called "
                f"{', '.join(sorted(GLOBALS | OWN_NAMES))}"
            )

    def _header(self) -> None:
        comment = banner(self.origin, self.sha, self.summary, "module", TRAP_NOTE)
        lines = [("// " + line).rstrip() for line in comment]
        lines += [
            "",
            "/** SHA-256 of the TIR artifact this module was printed from. */",
            f'export const artifactSha256 = "{self.sha}";',
            "",
        ]
        for text in lines:
            self.line(0, text)

    # --- declarations ---

    def _enum(self, decl: ir.EnumDecl) -> None:
        self.line(0, f"// enum {decl.name}")
        for ordinal, variant in enumerate(decl.variants):
            self.line(0, f"export const {variant} = {ordinal};")
        self.line(0)

    def _struct(self, decl: ir.StructDecl) -> None:
        self.line(0, f"export class {decl.name} {{")
        self.line(1, "constructor() {")
        for field in decl.fields:
            self.line(2, f"this.{field.name} = {self._zero(field.type)};")
        self.line(1, "}")
        if not self.p.types.is_linear(StructType(decl.name)):
            self.line(0)
            self.line(1, "tir_clone() {")
            self.line(2, f"const o = new {decl.name}();")
            for field in decl.fields:
                read = f"this.{field.name}"
                if isinstance(field.type, StructType):
                    read += ".tir_clone()"
                self.line(2, f"o.{field.name} = {read};")
            self.line(2, "return o;")
            self.line(1, "}")
        self.line(0, "}")
        self.line(0)
        arguments = ", ".join(f.name for f in decl.fields)
        self.line(0, f"function tir_new_{decl.name}({arguments}) {{")
        self.line(1, f"const o = new {decl.name}();")
        for field in decl.fields:
            self.line(1, f"o.{field.name} = {field.name};")
        self.line(1, "return o;")
        self.line(0, "}")
        self.line(0)

    def _const(self, decl: ir.Const) -> None:
        self.line(0, f"export const {decl.name} = {self._const_value(decl.value, decl.type)};")
        self.line(0)

    def _const_value(self, value: ir.ConstValue, t: Type) -> str:
        inner = unfrozen(t)
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, int):
            return str(value)
        if isinstance(value, ir.EnumConst):
            return value.variant
        if isinstance(value, ir.BytesConst):
            body = ", ".join(str(byte) for byte in value.data)
            return f"new tir_Seq(new Uint8Array([{body}]), {len(value.data)})"
        if isinstance(value, ir.VecConst):
            assert isinstance(inner, VecType)
            maker = _store(inner.elem)[0]
            items = ", ".join(self._const_value(v, inner.elem) for v in value.elems)
            return f"tir_filled({maker}({len(value.elems)}), [{items}])"
        assert isinstance(value, ir.StructConst) and isinstance(inner, StructType)
        given = dict(value.fields)
        items = ", ".join(
            self._const_value(given[f.name], f.type)
            for f in self.p.struct_map[inner.name].fields
        )
        return f"tir_new_{inner.name}({items})"

    # --- functions ---

    def _func(self, f: ir.Func) -> None:
        self.types = Types(self.p, f)
        self.inout = {p.name for p in f.params if p.mode == "inout"}
        self.temps = 0
        params = ", ".join(p.name for p in f.params)
        self.line(0, f"export function {f.name}({params}) {{")
        self._body(f.body, 1)
        self.line(0, "}")
        self.line(0)

    def _body(self, body: tuple[ir.Stmt, ...], depth: int) -> None:
        for stmt in body:
            self._stmt(stmt, depth)

    def _block(self, body: tuple[ir.Stmt, ...], depth: int) -> None:
        """A nested body, which is allowed to be empty.

        An empty one still has to be printed — a switch arm that did nothing
        would otherwise fall through to the default — and a bare `{}` is what
        every JavaScript linter is entitled to ask about, so it gets a line
        saying that is what it means.
        """
        if body:
            self._body(body, depth)
        else:
            self.line(depth, "// nothing")

    def _temp(self) -> str:
        self.temps += 1
        return f"tir_t{self.temps}"

    def _stmt(self, s: ir.Stmt, depth: int) -> None:
        match s:
            case ir.Let(name=name, type=t, init=init):
                value = self._zero(t) if init is None else self._expr(init)
                self.line(depth, f"let {name} = {value};")

            case ir.Assign(place=place, value=value):
                target = self._place(place, depth)
                self.line(depth, f"{target} = {self._expr(value)};")

            case ir.Take(dest=dest, src=src) | ir.Freeze(dest=dest, src=src):
                target = self._place(dest, depth)
                source = self._place(src, depth)
                self.line(depth, f"{target} = {source};")
                self.line(depth, f"{source} = {self._zero(self.types.place(src))};")

            case ir.Swap(a=a, b=b):
                left = self._place(a, depth)
                right = self._place(b, depth)
                held = self._temp()
                self.line(depth, f"const {held} = {left};")
                self.line(depth, f"{left} = {right};")
                self.line(depth, f"{right} = {held};")

            case ir.Copy(dest=dest, src=src):
                target = self._place(dest, depth)
                helper = self._copy_helper(self.types.place(dest))
                self.line(depth, f"{target} = {helper}({self._expr(src)});")

            case ir.Push(seq=seq, value=value):
                target = self._place(seq, depth)
                t = self.types.place(seq)
                maker = _maker(element_type(t))
                self.line(
                    depth,
                    f"tir_push({target}, {declared_max(t)}, {maker}, {self._expr(value)});",
                )

            case ir.Pop(seq=seq, dest=dest):
                source = self._place(seq, depth)
                target = self._place(dest, depth)
                self.line(depth, f"{target} = tir_pop({source});")

            case ir.Truncate(seq=seq, length=length):
                target = self._place(seq, depth)
                self.line(depth, f"tir_truncate({target}, {self._expr(length)});")

            case ir.Reserve(seq=seq, cap=cap):
                target = self._place(seq, depth)
                t = self.types.place(seq)
                maker = _maker(element_type(t))
                self.line(
                    depth,
                    f"tir_reserve({target}, {self._expr(cap)}, {declared_max(t)}, {maker});",
                )

            case ir.If(cond=cond, then=then, otherwise=otherwise):
                self.line(depth, f"if ({self._expr(cond)}) {{")
                self._block(then, depth + 1)
                if otherwise:
                    self.line(depth, "} else {")
                    self._body(otherwise, depth + 1)
                self.line(depth, "}")

            case ir.While(cond=cond, body=body):
                self.line(depth, f"while ({self._expr(cond)}) {{")
                self._block(body, depth + 1)
                self.line(depth, "}")

            case ir.Switch(value=value, arms=arms, default=default):
                # An if-chain rather than a JavaScript switch: cases there fall
                # through, share one block scope, and would capture the break
                # that TIR means for the enclosing loop.
                held = self._temp()
                self.line(depth, f"const {held} = {self._expr(value)};")
                if not arms:
                    # Rule V-032 makes the default a body whenever the arms
                    # leave a gap, so with no arms at all it is simply what
                    # happens; testing for it would be `if (true)`.
                    assert default is not None
                    self._body(default, depth)
                    return
                for index, arm in enumerate(arms):
                    keyword = "if" if index == 0 else "} else if"
                    self.line(depth, f"{keyword} ({held} === {arm.variant}) {{")
                    self._block(arm.body, depth + 1)
                if default is not None:
                    self.line(depth, "} else {")
                    self._block(default, depth + 1)
                self.line(depth, "}")

            case ir.Break():
                self.line(depth, "break;")

            case ir.Continue():
                self.line(depth, "continue;")

            case ir.Return(value=value):
                self.line(depth, "return;" if value is None else f"return {self._expr(value)};")

            case ir.Call(fn=fn, args=args, dest=dest):
                rendered = []
                writebacks = []
                for arg, first in zip(args, hoisted(args)):
                    if first:
                        assert isinstance(arg, ir.InArg)
                        early = self._temp()
                        self.line(depth, f"const {early} = {self._expr(arg.expr)};")
                        rendered.append(early)
                        continue
                    text, back = self._arg(arg, depth)
                    rendered.append(text)
                    if back is not None:
                        writebacks.append(back)
                call = f"{fn}({', '.join(rendered)})"
                held = self._temp() if dest is not None else None
                self.line(depth, f"const {held} = {call};" if held else f"{call};")
                for target, cell in writebacks:
                    self.line(depth, f"{target} = {cell}.v;")
                if dest is not None:
                    self.line(depth, f"{self._place(dest, depth)} = {held};")

            case _:
                raise JsError(f"not a TIR statement: {s!r}")

    def _arg(self, arg: ir.Arg, depth: int) -> tuple[str, tuple[str, str] | None]:
        """One argument, plus what has to be written back after the call."""
        if isinstance(arg, ir.InArg):
            return self._expr(arg.expr), None
        place = arg.place
        if isinstance(place, ir.VarPlace) and place.name in self.inout:
            # Already a cell, and passing it on keeps one cell per value rather
            # than a chain of copies.
            return place.name, None
        target = self._place(place, depth)
        cell = self._temp()
        self.line(depth, f"const {cell} = tir_cell({target});")
        return cell, (target, cell)

    # --- places ---

    def _place(self, p: ir.Place, depth: int) -> str:
        match p:
            case ir.VarPlace(name=name):
                return f"{name}.v" if name in self.inout else name
            case ir.FieldPlace(base=base, name=name):
                return f"{self._place(base, depth)}.{name}"
            case ir.IndexPlace(base=base, index=index):
                container = self._place(base, depth)
                at = self._temp()
                self.line(depth, f"const {at} = {self._expr(index)};")
                self.line(depth, f"tir_bound({container}.n, {at});")
                return f"{container}.a[{at}]"
        raise JsError(f"not a TIR place: {p!r}")

    # --- expressions ---

    def _expr(self, e: ir.Expr, borrow: bool = False) -> str:
        """One expression.

        `borrow` says the result is only going to be projected from — the base
        of a field, an index, a len or a cap — so it does not have to be
        copied. That is what section 6.2 means by projecting not being reading,
        and it is also what lets a linear struct appear here at all: `w.nodes`
        has to reach the sequence itself rather than a copy of it.
        """
        match e:
            case ir.Lit(type=t, value=value):
                if t == BOOL:
                    return "true" if value else "false"
                return str(value)

            case ir.Var(name=name):
                text = f"{name}.v" if name in self.inout else name
                return text if borrow else self._cloned(self.types.of(e), text)

            case ir.ConstRef(name=name):
                return name

            case ir.FieldRead(base=base, name=name):
                text = f"{self._expr(base, borrow=True)}.{name}"
                # The type of the read, not of the declared field: a linear
                # field of a frozen struct comes out frozen, hence shared.
                return text if borrow else self._cloned(self.types.of(e), text)

            case ir.IndexRead(base=base, index=index):
                container = self._expr(base, borrow=True)
                text = f"tir_at({container}, {self._expr(index)})"
                if borrow:
                    return text
                return self._cloned(element_type(self.types.of(base)), text)

            case ir.Len(arg=arg):
                return f"{self._expr(arg, borrow=True)}.n"

            case ir.Cap(arg=arg):
                return f"{self._expr(arg, borrow=True)}.a.length"

            case ir.Unary(op=op, arg=arg):
                text = self._expr(arg)
                if op == "not":
                    return f"(!{text})"
                return self._coerced(f"{'-' if op == 'neg' else '~'}{text}", self.types.of(arg))

            case ir.Binary(op=op, left=left, right=right):
                t = self.types.of(left)
                a, b = self._expr(left), self._expr(right)
                if t == COUNTER:
                    return f"tir_c{op}({a}, {b})"
                if op == "mul":
                    return self._coerced(f"Math.imul({a}, {b})", t)
                if op in BITWISE:
                    return self._coerced(f"{a} {BITWISE[op]} {b}", t, bitwise=True)
                return self._coerced(f"{a} {'+' if op == 'add' else '-'} {b}", t)

            case ir.Compare(op=op, left=left, right=right):
                return f"({self._expr(left)} {COMPARE[op]} {self._expr(right)})"

            case ir.DivRem(op=op, left=left, right=right, fallback=fallback):
                suffix = type_tag(self.types.of(left))
                return (
                    f"tir_{op}_{suffix}({self._expr(left)}, {self._expr(right)}, "
                    f"{self._expr(fallback)})"
                )

            case ir.Shift(op=op, arg=arg, count=count):
                t = self.types.of(arg)
                text = self._expr(arg)
                if op == "shl":
                    return self._coerced(f"{text} << {count}", t)
                # shr is offered only on unsigned types and sar only on i32, so
                # the two JavaScript spellings are a lookup rather than a choice.
                return f"({text} {'>>>' if op == 'shr' else '>>'} {count})"

            case ir.Cast(type=t, arg=arg):
                return self._cast(t, self.types.of(arg), self._expr(arg))

            case ir.Logical(op=op, left=left, right=right):
                symbol = "&&" if op == "and" else "||"
                return f"({self._expr(left)} {symbol} {self._expr(right)})"

            case ir.EnumVal(variant=variant):
                return variant

            case ir.StructVal(type=name, fields=fields):
                given = dict(fields)
                arguments = ", ".join(
                    self._expr(given[f.name]) for f in self.p.struct_map[name].fields
                )
                return f"tir_new_{name}({arguments})"

        raise JsError(f"not a TIR expression: {e!r}")

    def _cloned(self, t: Type, text: str) -> str:
        """A struct read out of storage is copied, because a class is a reference.

        Only a copyable one: a linear struct never becomes a value at all, so
        it has no clone method and needs none.
        """
        if isinstance(t, StructType) and not self.p.types.is_linear(t):
            return f"{text}.tir_clone()"
        return text

    def _coerced(self, text: str, t: Type, bitwise: bool = False) -> str:
        if t == I32 and bitwise:
            # The bitwise operators already answer in int32.
            return f"({text})"
        # The inner parentheses matter: a shift binds tighter than `&`, so
        # `a & b >>> 0` would coerce the wrong operand.
        return f"(({text}) {COERCE[t]})"

    def _cast(self, t: Type, source: Type, text: str) -> str:
        if source == BOOL:
            return f"({text} ? 1 : 0)"
        if t == COUNTER:
            # A count has no negative reading, so a negative i32 lands at zero
            # rather than being reinterpreted. The helper is there so the
            # operand is written once rather than twice.
            return f"tir_i32c({text})" if source == I32 else f"({text})"
        return f"(({text}) {COERCE[t]})"

    def _zero(self, t: Type) -> str:
        inner = unfrozen(t)
        if inner == BOOL:
            return "false"
        if inner in (U8, I32, U32, COUNTER):
            return "0"
        if inner == BYTES or isinstance(inner, VecType):
            return f"new tir_Seq({_empty(element_type(inner))}, 0)"
        if isinstance(inner, EnumType):
            return self.p.enum_map[inner.name].variants[0]
        assert isinstance(inner, StructType)
        return f"new {inner.name}()"

    # --- deep copy, one helper per type a copy statement reaches ---

    def _copy_helper(self, t: Type) -> str:
        return plan_copies(self.p, t, self.copies)

    def _copy_helpers(self) -> None:
        # Registering a type registers everything it reaches, so the plan is
        # complete before the first helper is written.
        for tag, t in list(self.copies.items()):
            self._one_copy_helper(t, "tir_copy_" + tag)

    def _one_copy_helper(self, t: Type, name: str) -> None:
        self.line(0, f"function {name}(s) {{")
        if isinstance(t, FrozenType):
            # Nothing under a frozen value can change, so a deep copy shares it.
            self.line(1, "return s;")
        elif t == BYTES or isinstance(t, VecType):
            self.line(1, f"const store = {_maker(element_type(t))}(s.n);")
            self.line(1, "for (let i = 0; i < s.n; i++) {")
            self.line(2, f"store[i] = {self._copy_helper(element_type(t))}(s.a[i]);")
            self.line(1, "}")
            self.line(1, "return new tir_Seq(store, s.n);")
        elif isinstance(t, StructType):
            self.line(1, f"const d = new {t.name}();")
            for field in self.p.struct_map[t.name].fields:
                helper = self._copy_helper(field.type)
                self.line(1, f"d.{field.name} = {helper}(s.{field.name});")
            self.line(1, "return d;")
        else:
            self.line(1, "return s;")
        self.line(0, "}")
        self.line(0)

    # --- zero values the wrapper needs to hand in ---

    def _factories(self) -> None:
        self.line(0, "// Zero values for every inout parameter type, so the wrapper can")
        self.line(0, "// build what it passes in without knowing how a value is laid out.")
        self.line(0)
        seen: set[str] = set()
        for f in self.p.funcs:
            for param in f.params:
                tag = type_tag(param.type)
                if param.mode != "inout" or tag in seen:
                    continue
                seen.add(tag)
                self.line(0, f"export function tir_zero_{tag}() {{")
                self.line(1, f"return {self._zero(param.type)};")
                self.line(0, "}")
                self.line(0)


SUPPORT = r"""
/** What a checked operation throws, per TIR-SPEC.md section 12. */
export class tir_Trap extends Error {
  constructor(code, what) {
    super(`pcrevera: TIR trap ${code}: ${what}`);
    this.name = "tir_Trap";
    this.code = code;
  }
}

const tir_CAP = 9007199254740991;

function tir_i32c(x) {
  return x < 0 ? 0 : x;
}

function tir_oob(index, bound) {
  throw new tir_Trap("T-01", `index ${index} past the end of a sequence of ${bound}`);
}

/** A sequence: a backing store whose length is the capacity, plus the length. */
export class tir_Seq {
  constructor(a, n) {
    this.a = a;
    this.n = n;
  }
}

/** An inout parameter, which is always a one-field cell. */
export function tir_cell(v) {
  return { v };
}

/** A frozen bytes value over an existing Uint8Array, which it does not copy. */
export function tir_bytes(bytes) {
  return new tir_Seq(bytes, bytes.length);
}

const tir_EMPTY_U8 = new Uint8Array(0);
const tir_EMPTY_I32 = new Int32Array(0);
const tir_EMPTY_U32 = new Uint32Array(0);
const tir_EMPTY_F64 = new Float64Array(0);
const tir_EMPTY_BOOL = [];
const tir_EMPTY_OBJ = [];

function tir_mk_u8(n) {
  return new Uint8Array(n);
}

function tir_mk_i32(n) {
  return new Int32Array(n);
}

function tir_mk_u32(n) {
  return new Uint32Array(n);
}

function tir_mk_f64(n) {
  return new Float64Array(n);
}

function tir_mk_bool(n) {
  return new Array(n).fill(false);
}

function tir_mk_obj(n) {
  return new Array(n).fill(null);
}

function tir_filled(store, items) {
  for (let i = 0; i < items.length; i++) {
    store[i] = items[i];
  }
  return new tir_Seq(store, items.length);
}

function tir_bound(bound, index) {
  if (index >= bound) {
    tir_oob(index, bound);
  }
}

function tir_at(s, index) {
  if (index >= s.n) {
    tir_oob(index, s.n);
  }
  return s.a[index];
}

// Growth allocates a fresh store and copies, on the schedule of TIR-SPEC.md
// section 11; nothing here reallocates in place, because the memory accounting
// counts both stores as live at once.
function tir_grow(s, capacity, make) {
  const store = make(capacity);
  const old = s.a;
  for (let i = 0; i < s.n; i++) {
    store[i] = old[i];
  }
  s.a = store;
}

function tir_push(s, limit, make, v) {
  const n = s.n;
  if (n >= limit) {
    throw new tir_Trap("T-05", `push past the declared maximum of ${limit}`);
  }
  if (n === s.a.length) {
    let capacity = 2 * s.a.length;
    if (capacity < 4) {
      capacity = 4;
    }
    if (capacity > limit) {
      capacity = limit;
    }
    tir_grow(s, capacity, make);
  }
  s.a[n] = v;
  s.n = n + 1;
}

function tir_pop(s) {
  const n = s.n;
  if (n === 0) {
    throw new tir_Trap("T-02", "pop from an empty sequence");
  }
  s.n = n - 1;
  return s.a[n - 1];
}

function tir_truncate(s, length) {
  if (length > s.n) {
    throw new tir_Trap("T-03", `truncate to ${length}, past the length ${s.n}`);
  }
  s.n = length;
}

function tir_reserve(s, capacity, limit, make) {
  if (capacity > limit) {
    throw new tir_Trap("T-04", `reserve ${capacity}, past the declared maximum ${limit}`);
  }
  if (capacity > s.a.length) {
    tir_grow(s, capacity, make);
  }
}

// The three counter operators of TIR-SPEC.md section 6.7, checked before the
// arithmetic rather than clamped after it: a plain product of two large
// counters rounds before any comparison could look at it.
function tir_cadd(a, b) {
  return a > tir_CAP - b ? tir_CAP : a + b;
}

function tir_csub(a, b) {
  return a < b ? 0 : a - b;
}

function tir_cmul(a, b) {
  if (a === 0 || b === 0) {
    return 0;
  }
  return a > Math.floor(tir_CAP / b) ? tir_CAP : a * b;
}

// Division and remainder. The operands are non-negative for every type but
// i32, where truncation towards zero and the two overflow corners are the
// whole reason these are helpers.
function tir_div_u8(a, b, f) {
  return b === 0 ? f : Math.floor(a / b);
}

function tir_rem_u8(a, b, f) {
  return b === 0 ? f : a % b;
}

function tir_div_u32(a, b, f) {
  return b === 0 ? f : Math.floor(a / b);
}

function tir_rem_u32(a, b, f) {
  return b === 0 ? f : a % b;
}

function tir_div_counter(a, b, f) {
  return b === 0 ? f : Math.floor(a / b);
}

function tir_rem_counter(a, b, f) {
  return b === 0 ? f : a % b;
}

function tir_div_i32(a, b, f) {
  if (b === 0) {
    return f;
  }
  return Math.trunc(a / b) | 0;
}

function tir_rem_i32(a, b, f) {
  if (b === 0) {
    return f;
  }
  if (b === -1) {
    return 0;
  }
  return (a % b) | 0;
}
"""

__all__ = ["JsError", "render"]
