"""Storage sizes, linearity, and the capacity derivation of TIR-SPEC.md sections 3 and 4."""

from __future__ import annotations

import pytest

from pcretruste.tir.types import (
    BOOL,
    BYTES,
    CAP,
    CEILING,
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
    TypeEnv,
    VecType,
    wrap,
)


def env(*structs: StructDecl, enums: tuple[EnumDecl, ...] = ()) -> TypeEnv:
    return TypeEnv({e.name: e for e in enums}, {s.name: s for s in structs})


def test_the_two_ceilings_are_the_documented_numbers():
    assert CEILING == 2**31 - 1
    assert CAP == 2**53 - 1


@pytest.mark.parametrize(
    "t, size",
    [(BOOL, 1), (U8, 1), (I32, 4), (U32, 4), (COUNTER, 8), (BYTES, 8)],
)
def test_scalar_sizes(t, size):
    assert env().sizeof(t) == size


def test_a_struct_is_packed_in_declared_order():
    frame = StructDecl("Frame", (Field("a", U8), Field("b", COUNTER), Field("c", U32)))
    assert env(frame).sizeof(StructType("Frame")) == 1 + 8 + 4


def test_handles_weigh_the_same_whatever_they_point_at():
    types = env()
    assert types.sizeof(VecType(U8, 16)) == types.sizeof(VecType(COUNTER, 16)) == 8
    assert types.sizeof(FrozenType(BYTES)) == 8


def test_an_enum_is_four_bytes():
    phase = EnumDecl("Phase", ("Enter", "Left"))
    assert env(enums=(phase,)).sizeof(EnumType("Phase")) == 4


def test_sequences_are_linear_and_scalars_are_not():
    types = env()
    assert types.is_linear(BYTES)
    assert types.is_linear(VecType(U32, 8))
    assert not types.is_linear(U32)
    assert not types.is_linear(FrozenType(BYTES))


def test_a_struct_is_linear_exactly_when_it_holds_something_linear():
    plain = StructDecl("Plain", (Field("a", U32),))
    holder = StructDecl("Holder", (Field("v", BYTES),))
    nested = StructDecl("Nested", (Field("inner", StructType("Holder")),))
    shared = StructDecl("Shared", (Field("v", FrozenType(BYTES)),))
    types = env(plain, holder, nested, shared)
    assert not types.is_linear(StructType("Plain"))
    assert types.is_linear(StructType("Holder"))
    assert types.is_linear(StructType("Nested"))
    assert not types.is_linear(StructType("Shared"))


def test_capacity_comes_from_the_element_size():
    types = env()
    assert types.max_capacity(U8) == CEILING
    assert types.max_capacity(U32) == CEILING // 4
    assert types.max_capacity(COUNTER) == CEILING // 8


@pytest.mark.parametrize(
    "t, value, expected",
    [
        (U8, 256, 0),
        (U8, -1, 255),
        (U32, 2**32, 0),
        (U32, -1, 2**32 - 1),
        (I32, 2**31, -(2**31)),
        (I32, -(2**31) - 1, 2**31 - 1),
        (I32, 2**32 + 5, 5),
    ],
)
def test_wrapping_reads_the_residue_back_in_the_type(t, value, expected):
    assert wrap(t, value) == expected

