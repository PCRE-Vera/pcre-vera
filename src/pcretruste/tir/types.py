"""TIR types, and the questions everything else asks of one.

Is it linear, so that it moves rather than copies? What does it weigh in IR
bytes? What may hold it? TIR-SPEC.md sections 3 and 4 are the normative
answers; this module is their transcription.

Linearity and storage size both depend on the struct declarations, so those
two live on `TypeEnv` rather than on the types themselves. A recursive struct
has neither, which is why `TypeEnv` refuses to answer for one instead of
recursing forever.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

CEILING = 2**31 - 1
"""The portable allocation ceiling, in IR bytes, inclusive."""

CAP = 2**53 - 1
"""The counter saturation point."""


@dataclass(frozen=True)
class Prim:
    """One of the six built-in types.

    The six constants below are the ones every module names, but nothing may
    depend on getting those exact objects: types are compared by value
    everywhere, so a `Prim` the reader rebuilt, or one the DSL wrote out by
    hand, is the same type as the constant. Comparing by identity instead would
    make `Prim("bytes")` a type that is not linear and has no size.
    """

    name: str

    def __str__(self) -> str:
        return self.name


BOOL = Prim("bool")
U8 = Prim("u8")
I32 = Prim("i32")
U32 = Prim("u32")
COUNTER = Prim("counter")
BYTES = Prim("bytes")

PRIMS = {p.name: p for p in (BOOL, U8, I32, U32, COUNTER, BYTES)}


@dataclass(frozen=True)
class EnumType:
    name: str

    def __str__(self) -> str:
        return f"enum {self.name}"


@dataclass(frozen=True)
class StructType:
    name: str

    def __str__(self) -> str:
        return f"struct {self.name}"


@dataclass(frozen=True)
class VecType:
    elem: "Type"
    max: int

    def __str__(self) -> str:
        return f"vec<{self.elem}, {self.max}>"


@dataclass(frozen=True)
class FrozenType:
    inner: "Type"

    def __str__(self) -> str:
        return f"frozen<{self.inner}>"


Type = Prim | EnumType | StructType | VecType | FrozenType


@dataclass(frozen=True)
class Field:
    name: str
    type: Type


@dataclass(frozen=True)
class EnumDecl:
    name: str
    variants: tuple[str, ...]

    def ordinal(self, variant: str) -> int:
        return self.variants.index(variant)


@dataclass(frozen=True)
class StructDecl:
    name: str
    fields: tuple[Field, ...]

    def field(self, name: str) -> Field | None:
        for field in self.fields:
            if field.name == name:
                return field
        return None


class RecursiveStruct(Exception):
    """A struct that contains itself has no size and no zero value.

    The validator rejects one before anything asks; this exception exists so
    that a caller who asks first gets a diagnosis rather than a stack overflow.
    """


# Integer types, with the two facts every arithmetic rule is written from.
INT_WIDTH = {U8: 8, I32: 32, U32: 32}

INT_RANGE = {
    U8: (0, 255),
    I32: (-(2**31), 2**31 - 1),
    U32: (0, 2**32 - 1),
    COUNTER: (0, CAP),
}

SIGNED = {I32}

SCALAR_SIZE = {BOOL: 1, U8: 1, I32: 4, U32: 4, COUNTER: 8}

HANDLE_SIZE = 8
"""What a sequence or frozen value weighs where it sits; its elements are counted apart."""

ENUM_SIZE = 4


def is_integer(t: Type) -> bool:
    return t in INT_RANGE


def is_sequence(t: Type) -> bool:
    return t == BYTES or isinstance(t, VecType)


def element_type(t: Type) -> Type:
    """The element type of a sequence, frozen or not."""
    if isinstance(t, FrozenType):
        t = t.inner
    if t == BYTES:
        return U8
    assert isinstance(t, VecType), f"{t} is not a sequence"
    return t.elem


def declared_max(t: Type) -> int:
    """The declared maximum length of a sequence type."""
    if isinstance(t, FrozenType):
        t = t.inner
    if t == BYTES:
        return CEILING
    assert isinstance(t, VecType), f"{t} is not a sequence"
    return t.max


def unfrozen(t: Type) -> Type:
    return t.inner if isinstance(t, FrozenType) else t


def wrap(t: Type, value: int) -> int:
    """Reduce an integer mod 2^w and read it back in the type.

    TIR-SPEC.md section 6.6. `counter` never wraps, so it is not accepted here:
    saturation is a different rule and lives in the interpreter.
    """
    width = INT_WIDTH[t]
    residue = value % (1 << width)
    if t in SIGNED and residue >= 1 << (width - 1):
        residue -= 1 << width
    return residue


def in_range(t: Type, value: int) -> bool:
    low, high = INT_RANGE[t]
    return low <= value <= high


class TypeEnv:
    """The declared enums and structs, plus the derived facts about them.

    Both derived facts — linearity and size — are memoized, because the
    validator asks for them once per expression node and a deeply nested struct
    would otherwise be walked again for every mention of it.
    """

    def __init__(self, enums: Mapping[str, EnumDecl], structs: Mapping[str, StructDecl]) -> None:
        self.enums = dict(enums)
        self.structs = dict(structs)
        self._linear: dict[str, bool] = {}
        self._size: dict[str, int] = {}

    def struct(self, name: str) -> StructDecl:
        return self.structs[name]

    def is_linear(self, t: Type) -> bool:
        """Linear means heap-backed: it moves, it does not copy.

        TIR-SPEC.md section 3.3.
        """
        if t == BYTES or isinstance(t, VecType):
            return True
        if isinstance(t, StructType):
            return self._struct_linear(t.name, ())
        return False

    def is_copyable(self, t: Type) -> bool:
        return not self.is_linear(t)

    def _struct_linear(self, name: str, path: tuple[str, ...]) -> bool:
        if name in self._linear:
            return self._linear[name]
        if name in path:
            raise RecursiveStruct(" -> ".join((*path, name)))
        decl = self.structs[name]
        answer = False
        for field in decl.fields:
            t = field.type
            if isinstance(t, StructType):
                if self._struct_linear(t.name, (*path, name)):
                    answer = True
            elif self.is_linear(t):
                answer = True
        self._linear[name] = answer
        return answer

    def sizeof(self, t: Type) -> int:
        """Storage size in IR bytes. TIR-SPEC.md section 4.2."""
        if t in SCALAR_SIZE:
            return SCALAR_SIZE[t]
        if isinstance(t, EnumType):
            return ENUM_SIZE
        if t == BYTES or isinstance(t, (VecType, FrozenType)):
            return HANDLE_SIZE
        assert isinstance(t, StructType)
        return self._struct_size(t.name, ())

    def _struct_size(self, name: str, path: tuple[str, ...]) -> int:
        if name in self._size:
            return self._size[name]
        if name in path:
            raise RecursiveStruct(" -> ".join((*path, name)))
        total = 0
        for field in self.structs[name].fields:
            t = field.type
            if isinstance(t, StructType):
                total += self._struct_size(t.name, (*path, name))
            else:
                total += self.sizeof(t)
        self._size[name] = total
        return total

    def max_capacity(self, elem: Type) -> int:
        """How many elements of this type fit under the ceiling."""
        return CEILING // self.sizeof(elem)
