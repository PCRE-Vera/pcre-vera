"""The TIR program tree.

One dataclass per node of TIR-SPEC.md sections 5 to 9. Nothing here checks
anything: the tree a caller builds may be nonsense, and saying so is the
validator's job. Keeping construction and checking apart is what lets the
authoring DSL stay untrusted.

Places and expressions have the same three shapes in JSON but different Python
classes, because a place's base is another place while an expression's base is
an expression. A constant reference is an expression and can never be a place,
and that is a difference the type of the field should carry rather than a
check somebody has to remember to write.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from functools import cached_property

from .types import EnumDecl, StructDecl, Type, TypeEnv

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
MAX_IDENTIFIER = 64

MAX_DEPTH = 64
"""How deep a program may nest. TIR-SPEC.md section 2, rule V-044."""

PARAM_MODES = ("in", "inout")

RESERVED_PREFIXES = ("tir_", "Tir_")
"""What the printers keep for themselves.

`tir_` is the helpers. `Tir_` is the exported façade the Go printer has to
emit, because Go cannot reach a lower-case name from another package and TIR
names are printed verbatim; a second prefix rather than a case-insensitive
test, since section 2 compares identifiers by exact byte equality.
"""

# Names a backend could not print verbatim, so TIR refuses them outright
# rather than inventing a mangling scheme each printer would have to reproduce
# exactly. Go's keywords and predeclared identifiers come first — shadowing
# `len` or `cap` at package level would break every generated use of them —
# then JavaScript's reserved words, its strict-mode and future-reserved ones
# included, then the two Go spells but cannot use as names: `_` names nothing
# that can be referred to, and `init` may only ever be a function that nothing
# calls.
#
# Last are the names the generated scope holds besides the program: the host
# globals the JavaScript module reads, where a shadowing name would make
# `Math.imul` mean something else, and the constant each printer stamps the
# artifact hash into. Those are printer-owned and versioned with this
# repository, unlike the wrapper's own names, which stay outside TIR because
# they live in a different scope (TIR-SPEC.md section 16).
#
# TIR-SPEC.md section 2 carries the same list, and a test compares the two so
# they cannot drift.
RESERVED = frozenset(
    """
    break case chan const continue default defer else fallthrough for func go goto if
    import interface map package range return select struct switch type var
    any bool byte comparable complex64 complex128 error float32 float64 int int8 int16
    int32 int64 rune string uint uint8 uint16 uint32 uint64 uintptr
    true false iota nil append cap clear close complex copy delete imag len make max min
    new panic print println real recover
    await catch class debugger do enum export extends finally function in instanceof let
    new null super this throw try typeof void while with yield static implements
    private protected public arguments eval
    _ init
    Array Error Float64Array Int32Array Math Uint32Array Uint8Array
    ArtifactSHA256 artifactSha256
    """.split()
)

# Operator names, exactly as they appear in the artifact.
UNARY_OPS = ("not", "neg", "bnot")
BINARY_OPS = ("add", "sub", "mul", "and", "or", "xor")
ARITH_OPS = ("add", "sub", "mul")
BITWISE_OPS = ("and", "or", "xor")
COMPARE_OPS = ("eq", "ne", "lt", "le", "gt", "ge")
EQUALITY_OPS = ("eq", "ne")
DIVREM_OPS = ("div", "rem")
SHIFT_OPS = ("shl", "shr", "sar")
LOGICAL_OPS = ("and", "or")


# --- expressions ---


@dataclass(frozen=True)
class Lit:
    type: Type
    value: int | bool


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class ConstRef:
    name: str


@dataclass(frozen=True)
class FieldRead:
    base: "Expr"
    name: str


@dataclass(frozen=True)
class IndexRead:
    base: "Expr"
    index: "Expr"


@dataclass(frozen=True)
class Len:
    arg: "Expr"


@dataclass(frozen=True)
class Cap:
    arg: "Expr"


@dataclass(frozen=True)
class Unary:
    op: str
    arg: "Expr"


@dataclass(frozen=True)
class Binary:
    op: str
    left: "Expr"
    right: "Expr"


@dataclass(frozen=True)
class Compare:
    op: str
    left: "Expr"
    right: "Expr"


@dataclass(frozen=True)
class DivRem:
    op: str
    left: "Expr"
    right: "Expr"
    fallback: "Expr"


@dataclass(frozen=True)
class Shift:
    op: str
    arg: "Expr"
    count: int


@dataclass(frozen=True)
class Cast:
    type: Type
    arg: "Expr"


@dataclass(frozen=True)
class Logical:
    op: str
    left: "Expr"
    right: "Expr"


@dataclass(frozen=True)
class EnumVal:
    type: str
    variant: str


@dataclass(frozen=True)
class StructVal:
    type: str
    fields: tuple[tuple[str, "Expr"], ...]

    def __post_init__(self) -> None:
        # A JSON object has no order, and the canonical form sorts its keys, so
        # a tuple in any other order would not survive a round trip. Evaluation
        # order is the struct's declared field order either way (TIR-SPEC.md
        # section 13), so nothing is lost by settling it here.
        object.__setattr__(self, "fields", tuple(sorted(self.fields, key=lambda kv: kv[0])))


Expr = (
    Lit
    | Var
    | ConstRef
    | FieldRead
    | IndexRead
    | Len
    | Cap
    | Unary
    | Binary
    | Compare
    | DivRem
    | Shift
    | Cast
    | Logical
    | EnumVal
    | StructVal
)


# --- places ---


@dataclass(frozen=True)
class VarPlace:
    name: str


@dataclass(frozen=True)
class FieldPlace:
    base: "Place"
    name: str


@dataclass(frozen=True)
class IndexPlace:
    base: "Place"
    index: Expr


Place = VarPlace | FieldPlace | IndexPlace


# --- statements ---


@dataclass(frozen=True)
class Let:
    name: str
    type: Type
    init: Expr | None = None


@dataclass(frozen=True)
class Assign:
    place: Place
    value: Expr


@dataclass(frozen=True)
class Take:
    dest: Place
    src: Place


@dataclass(frozen=True)
class Swap:
    a: Place
    b: Place


@dataclass(frozen=True)
class Copy:
    dest: Place
    src: Expr


@dataclass(frozen=True)
class Freeze:
    dest: Place
    src: Place


@dataclass(frozen=True)
class Push:
    seq: Place
    value: Expr


@dataclass(frozen=True)
class Pop:
    seq: Place
    dest: Place


@dataclass(frozen=True)
class Truncate:
    seq: Place
    length: Expr


@dataclass(frozen=True)
class Reserve:
    seq: Place
    cap: Expr


@dataclass(frozen=True)
class If:
    cond: Expr
    then: tuple["Stmt", ...]
    otherwise: tuple["Stmt", ...] = ()


@dataclass(frozen=True)
class While:
    cond: Expr
    variant: Expr
    body: tuple["Stmt", ...]


@dataclass(frozen=True)
class Arm:
    variant: str
    body: tuple["Stmt", ...]


@dataclass(frozen=True)
class Switch:
    value: Expr
    arms: tuple[Arm, ...]
    default: tuple["Stmt", ...] | None = None


@dataclass(frozen=True)
class Break:
    pass


@dataclass(frozen=True)
class Continue:
    pass


@dataclass(frozen=True)
class Return:
    value: Expr | None = None


@dataclass(frozen=True)
class InArg:
    expr: Expr


@dataclass(frozen=True)
class InoutArg:
    place: Place


Arg = InArg | InoutArg


@dataclass(frozen=True)
class Call:
    fn: str
    args: tuple[Arg, ...]
    dest: Place | None = None


Stmt = (
    Let
    | Assign
    | Take
    | Swap
    | Copy
    | Freeze
    | Push
    | Pop
    | Truncate
    | Reserve
    | If
    | While
    | Switch
    | Break
    | Continue
    | Return
    | Call
)


# --- constant values ---


@dataclass(frozen=True)
class EnumConst:
    variant: str


@dataclass(frozen=True)
class StructConst:
    fields: tuple[tuple[str, "ConstValue"], ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "fields", tuple(sorted(self.fields, key=lambda kv: kv[0])))


@dataclass(frozen=True)
class BytesConst:
    data: bytes


@dataclass(frozen=True)
class VecConst:
    elems: tuple["ConstValue", ...]


ConstValue = bool | int | EnumConst | StructConst | BytesConst | VecConst


# --- declarations ---


@dataclass(frozen=True)
class Const:
    name: str
    type: Type
    value: ConstValue


@dataclass(frozen=True)
class Param:
    name: str
    type: Type
    mode: str  # "in" or "inout"


@dataclass(frozen=True)
class Func:
    name: str
    params: tuple[Param, ...]
    ret: Type | None
    body: tuple[Stmt, ...]

    def param(self, name: str) -> Param | None:
        for p in self.params:
            if p.name == name:
                return p
        return None


@dataclass(frozen=True)
class Program:
    enums: tuple[EnumDecl, ...] = ()
    structs: tuple[StructDecl, ...] = ()
    consts: tuple[Const, ...] = ()
    funcs: tuple[Func, ...] = ()

    def __post_init__(self) -> None:
        # Declaration order carries no meaning, and the canonical encoding sorts
        # by name, so a program that kept the author's order would decode to
        # something that compares unequal to what it was written from.
        for name in ("enums", "structs", "consts", "funcs"):
            decls = getattr(self, name)
            object.__setattr__(self, name, tuple(sorted(decls, key=lambda d: d.name)))

    # The lookups below are derived, so they stay out of the dataclass fields
    # and out of equality, where they would only restate the tuples. A cached
    # property writes straight into the instance dictionary, which a frozen
    # dataclass permits.

    @cached_property
    def enum_map(self) -> dict[str, EnumDecl]:
        return {d.name: d for d in self.enums}

    @cached_property
    def struct_map(self) -> dict[str, StructDecl]:
        return {d.name: d for d in self.structs}

    @cached_property
    def const_map(self) -> dict[str, Const]:
        return {d.name: d for d in self.consts}

    @cached_property
    def func_map(self) -> dict[str, Func]:
        return {d.name: d for d in self.funcs}

    @cached_property
    def types(self) -> TypeEnv:
        return TypeEnv(self.enum_map, self.struct_map)
