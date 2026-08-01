"""The reference interpreter against the operator tables of TIR-SPEC.md.

Every case here is a sentence from the specification turned into an assertion:
the saturation pre-checks of section 6.7, the two i32 division corners of
section 6.9, the trap list of section 12, the growth schedule of section 11.2,
and the evaluation order of section 13.
"""

from __future__ import annotations

import pytest

from pcretruste.tir import Cell, Trap, ir, run, validate
from pcretruste.tir.interp import Frozen, OutOfFuel, Seq, StructValue, VariantViolation
from pcretruste.tir.types import (
    BOOL,
    BYTES,
    CAP,
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
    VecType,
)

I32_MIN = -(2**31)
I32_MAX = 2**31 - 1
U32_MAX = 2**32 - 1

WORDS = VecType(U32, 64)


def program(*, funcs, structs=(), enums=(), consts=()) -> ir.Program:
    built = ir.Program(
        enums=tuple(enums), structs=tuple(structs), consts=tuple(consts), funcs=tuple(funcs)
    )
    validate(built)
    return built


def evaluate(node: ir.Expr, ret, before=(), **decls):
    """Run `return node` in a function, after whatever statements set it up."""
    main = ir.Func("main", (), ret, (*before, ir.Return(node)))
    return run(program(funcs=[main], **decls), "main")


def sequence(name: str, values, elem=U8, t=BYTES):
    """Statements that build a sequence local holding these values."""
    return [
        ir.Let(name, t, None),
        *[ir.Push(ir.VarPlace(name), ir.Lit(elem, v)) for v in values],
    ]


# --- counter saturation, section 6.7 ---


@pytest.mark.parametrize(
    "op, a, b, expected",
    [
        ("add", 1, 2, 3),
        ("add", CAP - 1, 1, CAP),
        ("add", CAP, 1, CAP),
        ("add", CAP, CAP, CAP),
        ("sub", 5, 3, 2),
        ("sub", 0, 1, 0),
        ("sub", 3, 5, 0),
        ("mul", 0, CAP, 0),
        ("mul", CAP, 0, 0),
        ("mul", 2, (CAP - 1) // 2, CAP - 1),
        ("mul", 2, (CAP - 1) // 2 + 1, CAP),
        ("mul", CAP, CAP, CAP),
    ],
)
def test_counter_arithmetic_saturates(op, a, b, expected):
    node = ir.Binary(op, ir.Lit(COUNTER, a), ir.Lit(COUNTER, b))
    assert evaluate(node, COUNTER) == expected


def test_the_saturation_point_is_exactly_the_documented_one():
    assert evaluate(ir.Lit(COUNTER, CAP), COUNTER) == 2**53 - 1


# --- wrapping arithmetic, section 6.6 and 6.7 ---


@pytest.mark.parametrize(
    "t, op, a, b, expected",
    [
        (U8, "add", 200, 100, 44),
        (U8, "sub", 5, 10, 251),
        (U8, "mul", 16, 16, 0),
        (U32, "sub", 0, 1, U32_MAX),
        (U32, "mul", 65536, 65536, 0),
        (I32, "add", I32_MAX, 1, I32_MIN),
        (I32, "sub", I32_MIN, 1, I32_MAX),
        (I32, "mul", 65536, 65536, 0),
        (I32, "mul", -1, I32_MIN, I32_MIN),
    ],
)
def test_integer_arithmetic_wraps(t, op, a, b, expected):
    assert evaluate(ir.Binary(op, ir.Lit(t, a), ir.Lit(t, b)), t) == expected


@pytest.mark.parametrize(
    "t, op, x, expected",
    [
        (I32, "neg", I32_MIN, I32_MIN),
        (I32, "neg", 5, -5),
        (U8, "neg", 1, 255),
        (U32, "neg", 0, 0),
        (U8, "bnot", 0, 255),
        (I32, "bnot", 0, -1),
        (U32, "bnot", 0, U32_MAX),
    ],
)
def test_unary_operators(t, op, x, expected):
    assert evaluate(ir.Unary(op, ir.Lit(t, x)), t) == expected


@pytest.mark.parametrize(
    "t, op, a, b, expected",
    [
        (U8, "and", 0xF0, 0x3C, 0x30),
        (U8, "or", 0xF0, 0x0F, 0xFF),
        (U8, "xor", 0xFF, 0x0F, 0xF0),
        (I32, "and", -1, 0x7F, 0x7F),
        (I32, "or", -2, 1, -1),
        (I32, "xor", -1, -1, 0),
    ],
)
def test_bitwise_operators_run_on_the_bit_patterns(t, op, a, b, expected):
    assert evaluate(ir.Binary(op, ir.Lit(t, a), ir.Lit(t, b)), t) == expected


# --- checked division, section 6.9 ---


@pytest.mark.parametrize(
    "t, op, a, b, fallback, expected",
    [
        (U32, "div", 7, 2, 0, 3),
        (U32, "rem", 7, 2, 0, 1),
        (I32, "div", -7, 2, 0, -3),
        (I32, "rem", -7, 2, 0, -1),
        (I32, "div", 7, -2, 0, -3),
        (I32, "rem", 7, -2, 0, 1),
        (I32, "div", I32_MIN, -1, 0, I32_MIN),
        (I32, "rem", I32_MIN, -1, 0, 0),
        (U32, "div", 1, 0, 42, 42),
        (U32, "rem", 1, 0, 42, 42),
        (COUNTER, "div", CAP, 2, 0, (CAP - 1) // 2),
        (COUNTER, "rem", CAP, 2, 0, 1),
        (COUNTER, "div", 5, 0, 99, 99),
    ],
)
def test_division_and_remainder(t, op, a, b, fallback, expected):
    node = ir.DivRem(op, ir.Lit(t, a), ir.Lit(t, b), ir.Lit(t, fallback))
    assert evaluate(node, t) == expected


def test_the_fallback_is_evaluated_whether_or_not_it_is_needed():
    """It is an expression like any other, so its trap fires even on a live divisor."""
    node = ir.DivRem(
        "div",
        ir.Lit(U8, 6),
        ir.Lit(U8, 3),
        ir.IndexRead(ir.Var("b"), ir.Lit(U32, 9)),
    )
    with pytest.raises(Trap) as caught:
        evaluate(node, U8, before=sequence("b", [1, 2]))
    assert caught.value.code == "T-01"


# --- shifts, section 6.10 ---


@pytest.mark.parametrize(
    "t, op, x, count, expected",
    [
        (U8, "shl", 1, 7, 128),
        (U8, "shl", 200, 1, 144),
        (U8, "shr", 200, 4, 12),
        (U32, "shl", 1, 31, 2**31),
        (U32, "shr", U32_MAX, 31, 1),
        (I32, "shl", 1, 31, I32_MIN),
        (I32, "sar", -8, 2, -2),
        (I32, "sar", -1, 31, -1),
        (I32, "sar", I32_MAX, 31, 0),
        (U8, "shl", 5, 0, 5),
    ],
)
def test_shifts(t, op, x, count, expected):
    assert evaluate(ir.Shift(op, ir.Lit(t, x), count), t) == expected


# --- casts, section 6.13 ---


@pytest.mark.parametrize(
    "source, value, target, expected",
    [
        (BOOL, True, U8, 1),
        (BOOL, False, COUNTER, 0),
        (I32, -1, U8, 255),
        (I32, -1, U32, U32_MAX),
        (U32, U32_MAX, I32, -1),
        (U32, 300, U8, 44),
        (I32, -5, COUNTER, 0),
        (I32, 5, COUNTER, 5),
        (U32, U32_MAX, COUNTER, U32_MAX),
        (COUNTER, CAP, U32, U32_MAX),
        (COUNTER, CAP, U8, 255),
        (U32, 7, U32, 7),
    ],
)
def test_casts(source, value, target, expected):
    assert evaluate(ir.Cast(target, ir.Lit(source, value)), target) == expected


# --- boolean and / or, section 6.12 ---


def test_and_does_not_evaluate_a_right_operand_it_does_not_need():
    reads_past_the_end = ir.Compare(
        "eq", ir.IndexRead(ir.Var("b"), ir.Lit(U32, 9)), ir.Lit(U8, 0)
    )
    node = ir.Logical("and", ir.Lit(BOOL, False), reads_past_the_end)
    assert evaluate(node, BOOL, before=sequence("b", [1, 2])) is False


def test_or_does_not_evaluate_a_right_operand_it_does_not_need():
    reads_past_the_end = ir.Compare(
        "eq", ir.IndexRead(ir.Var("b"), ir.Lit(U32, 9)), ir.Lit(U8, 0)
    )
    node = ir.Logical("or", ir.Lit(BOOL, True), reads_past_the_end)
    assert evaluate(node, BOOL, before=sequence("b", [1, 2])) is True


def test_and_does_evaluate_the_right_operand_when_it_matters():
    reads_past_the_end = ir.Compare(
        "eq", ir.IndexRead(ir.Var("b"), ir.Lit(U32, 9)), ir.Lit(U8, 0)
    )
    node = ir.Logical("and", ir.Lit(BOOL, True), reads_past_the_end)
    with pytest.raises(Trap):
        evaluate(node, BOOL, before=sequence("b", [1, 2]))


# --- traps, section 12 ---


def test_t01_reading_past_the_end():
    with pytest.raises(Trap) as caught:
        evaluate(ir.IndexRead(ir.Var("b"), ir.Lit(U32, 2)), U8, before=sequence("b", [1, 2]))
    assert caught.value.code == "T-01"


def test_t01_reading_past_the_end_of_a_frozen_sequence():
    before = [
        *sequence("b", [1, 2]),
        ir.Let("fz", FrozenType(BYTES), None),
        ir.Freeze(ir.VarPlace("fz"), ir.VarPlace("b")),
    ]
    with pytest.raises(Trap) as caught:
        evaluate(ir.IndexRead(ir.Var("fz"), ir.Lit(U32, 2)), U8, before=before)
    assert caught.value.code == "T-01"


def test_t01_reading_past_the_end_of_a_constant():
    const = ir.Const("TABLE", FrozenType(BYTES), ir.BytesConst(bytes([1, 2])))
    with pytest.raises(Trap) as caught:
        evaluate(ir.IndexRead(ir.ConstRef("TABLE"), ir.Lit(U32, 2)), U8, consts=[const])
    assert caught.value.code == "T-01"


def test_t01_writing_past_the_end():
    body = [
        *sequence("b", [1, 2]),
        ir.Assign(ir.IndexPlace(ir.VarPlace("b"), ir.Lit(U32, 5)), ir.Lit(U8, 0)),
    ]
    with pytest.raises(Trap) as caught:
        run(program(funcs=[ir.Func("main", (), None, tuple(body))]), "main")
    assert caught.value.code == "T-01"


@pytest.mark.parametrize(
    "code, stmt, values, maximum",
    [
        ("T-02", ir.Pop(ir.VarPlace("b"), ir.VarPlace("x")), [], 64),
        ("T-03", ir.Truncate(ir.VarPlace("b"), ir.Lit(U32, 3)), [1, 2], 64),
        ("T-04", ir.Reserve(ir.VarPlace("b"), ir.Lit(U32, 5)), [], 4),
        ("T-05", ir.Push(ir.VarPlace("b"), ir.Lit(U8, 9)), [1, 2], 2),
    ],
)
def test_the_sequence_traps(code, stmt, values, maximum):
    t = VecType(U8, maximum)
    body = [ir.Let("x", U8, ir.Lit(U8, 0)), *sequence("b", values, t=t), stmt]
    with pytest.raises(Trap) as caught:
        run(program(funcs=[ir.Func("main", (), None, tuple(body))]), "main")
    assert caught.value.code == code


# --- growth, section 11.2 ---


def test_capacity_doubles_from_four():
    caps = []
    for pushes in range(6):
        node = ir.Cap(ir.Var("v"))
        caps.append(evaluate(node, U32, before=sequence("v", [1] * pushes, t=VecType(U8, 64))))
    assert caps == [0, 4, 4, 4, 4, 8]


def test_growth_stops_at_the_declared_maximum():
    before = sequence("v", [1] * 5, t=VecType(U8, 6))
    assert evaluate(ir.Cap(ir.Var("v")), U32, before=before) == 6


def test_reserve_sets_the_capacity_exactly_and_a_push_leaves_it_alone():
    before = [
        ir.Let("v", VecType(U8, 64), None),
        ir.Reserve(ir.VarPlace("v"), ir.Lit(U32, 10)),
        ir.Push(ir.VarPlace("v"), ir.Lit(U8, 1)),
    ]
    assert evaluate(ir.Cap(ir.Var("v")), U32, before=before) == 10


def test_reserve_never_shrinks():
    before = [
        ir.Let("v", VecType(U8, 64), None),
        ir.Reserve(ir.VarPlace("v"), ir.Lit(U32, 10)),
        ir.Reserve(ir.VarPlace("v"), ir.Lit(U32, 2)),
    ]
    assert evaluate(ir.Cap(ir.Var("v")), U32, before=before) == 10


def test_truncate_shortens_without_touching_capacity():
    before = [
        *sequence("v", [1, 2, 3, 4, 5], t=VecType(U8, 64)),
        ir.Truncate(ir.VarPlace("v"), ir.Lit(U32, 2)),
    ]
    assert evaluate(ir.Len(ir.Var("v")), U32, before=before) == 2
    assert evaluate(ir.Cap(ir.Var("v")), U32, before=before) == 8


# --- evaluation order, section 13 ---


def test_a_destination_place_is_resolved_before_the_value():
    body = [
        *sequence("v", [1]),
        *sequence("w", [1, 2, 3]),
        ir.Assign(
            ir.IndexPlace(ir.VarPlace("v"), ir.Lit(U32, 10)),
            ir.IndexRead(ir.Var("w"), ir.Lit(U32, 20)),
        ),
    ]
    with pytest.raises(Trap) as caught:
        run(program(funcs=[ir.Func("main", (), None, tuple(body))]), "main")
    assert "index 10 into a sequence of 1" in str(caught.value)


def test_a_trapping_divisor_wins_over_a_trapping_fallback():
    node = ir.DivRem(
        "div",
        ir.Lit(U8, 6),
        ir.IndexRead(ir.Var("v"), ir.Lit(U32, 5)),
        ir.IndexRead(ir.Var("w"), ir.Lit(U32, 7)),
    )
    with pytest.raises(Trap) as caught:
        evaluate(node, U8, before=[*sequence("v", [1]), *sequence("w", [1, 2])])
    assert "index 5 into a sequence of 1" in str(caught.value)


def test_call_arguments_are_resolved_left_to_right():
    callee = ir.Func(
        "g", (ir.Param("a", U8, "in"), ir.Param("b", U8, "in")), None, (ir.Return(None),)
    )
    caller = ir.Func(
        "main",
        (),
        None,
        (
            *sequence("v", [1]),
            *sequence("w", [1, 2]),
            ir.Call(
                "g",
                (
                    ir.InArg(ir.IndexRead(ir.Var("v"), ir.Lit(U32, 5))),
                    ir.InArg(ir.IndexRead(ir.Var("w"), ir.Lit(U32, 7))),
                ),
                None,
            ),
        ),
    )
    with pytest.raises(Trap) as caught:
        run(program(funcs=[caller, callee]), "main")
    assert "index 5 into a sequence of 1" in str(caught.value)


def test_a_binary_operator_evaluates_left_to_right():
    node = ir.Binary(
        "add",
        ir.IndexRead(ir.Var("v"), ir.Lit(U32, 5)),
        ir.IndexRead(ir.Var("w"), ir.Lit(U32, 7)),
    )
    with pytest.raises(Trap) as caught:
        evaluate(node, U8, before=[*sequence("v", [1]), *sequence("w", [1, 2])])
    assert "index 5 into a sequence of 1" in str(caught.value)


# --- linear movement, sections 8.3 and 10 ---


def lengths(stmt: ir.Stmt) -> list[int]:
    """Run one movement statement over two byte sequences, and report both lengths."""
    main = ir.Func(
        "main",
        (ir.Param("out", VecType(U32, 4), "inout"),),
        None,
        (
            *sequence("a", [1, 2, 3]),
            ir.Let("b", BYTES, None),
            stmt,
            ir.Push(ir.VarPlace("out"), ir.Len(ir.Var("a"))),
            ir.Push(ir.VarPlace("out"), ir.Len(ir.Var("b"))),
        ),
    )
    out = Cell(Seq(U32, 4, [], 0))
    run(program(funcs=[main]), "main", [out])
    return list(out.value.items)


def test_take_leaves_the_zero_value_behind():
    assert lengths(ir.Take(ir.VarPlace("b"), ir.VarPlace("a"))) == [0, 3]


def test_swap_exchanges_two_places():
    assert lengths(ir.Swap(ir.VarPlace("a"), ir.VarPlace("b"))) == [0, 3]


def test_copy_leaves_the_source_alone():
    assert lengths(ir.Copy(ir.VarPlace("b"), ir.Var("a"))) == [3, 3]


def test_a_copy_is_deep():
    body = [
        *sequence("a", [1, 2, 3]),
        ir.Let("b", BYTES, None),
        ir.Copy(ir.VarPlace("b"), ir.Var("a")),
        ir.Assign(ir.IndexPlace(ir.VarPlace("b"), ir.Lit(U32, 0)), ir.Lit(U8, 99)),
        ir.Return(ir.IndexRead(ir.Var("a"), ir.Lit(U32, 0))),
    ]
    assert run(program(funcs=[ir.Func("main", (), U8, tuple(body))]), "main") == 1


def test_a_copy_has_capacity_equal_to_its_length():
    before = [
        *sequence("a", [1, 2, 3], t=VecType(U8, 64)),
        ir.Let("b", VecType(U8, 64), None),
        ir.Copy(ir.VarPlace("b"), ir.Var("a")),
    ]
    assert evaluate(ir.Cap(ir.Var("a")), U32, before=before) == 4
    assert evaluate(ir.Cap(ir.Var("b")), U32, before=before) == 3


def test_freeze_moves_the_value_out_of_its_old_home():
    body = [
        *sequence("a", [1, 2, 3]),
        ir.Let("fz", FrozenType(BYTES), None),
        ir.Freeze(ir.VarPlace("fz"), ir.VarPlace("a")),
        ir.Return(ir.Binary("add", ir.Len(ir.Var("fz")), ir.Len(ir.Var("a")))),
    ]
    assert run(program(funcs=[ir.Func("main", (), U32, tuple(body))]), "main") == 3


def test_a_copyable_field_read_through_a_frozen_struct_is_a_copy():
    """Writing to what came out must not reach into the frozen value."""
    inner = StructDecl("Inner", (Field("a", U32),))
    outer = StructDecl("Outer", (Field("inner", StructType("Inner")), Field("v", BYTES)))
    body = [
        ir.Let("o", StructType("Outer"), None),
        ir.Let("fz", FrozenType(StructType("Outer")), None),
        ir.Freeze(ir.VarPlace("fz"), ir.VarPlace("o")),
        ir.Let("mine", StructType("Inner"), ir.FieldRead(ir.Var("fz"), "inner")),
        ir.Assign(ir.FieldPlace(ir.VarPlace("mine"), "a"), ir.Lit(U32, 7)),
        ir.Return(ir.FieldRead(ir.FieldRead(ir.Var("fz"), "inner"), "a")),
    ]
    built = program(structs=[inner, outer], funcs=[ir.Func("main", (), U32, tuple(body))])
    assert run(built, "main") == 0


def test_a_frozen_field_of_a_frozen_struct_stays_frozen():
    outer = StructDecl("Outer", (Field("v", BYTES),))
    body = [
        *sequence("b", [1, 2, 3]),
        ir.Let("o", StructType("Outer"), None),
        ir.Take(ir.FieldPlace(ir.VarPlace("o"), "v"), ir.VarPlace("b")),
        ir.Let("fz", FrozenType(StructType("Outer")), None),
        ir.Freeze(ir.VarPlace("fz"), ir.VarPlace("o")),
        ir.Return(ir.Len(ir.FieldRead(ir.Var("fz"), "v"))),
    ]
    built = program(structs=[outer], funcs=[ir.Func("main", (), U32, tuple(body))])
    assert run(built, "main") == 3


def test_a_struct_read_out_of_storage_is_a_copy():
    struct = StructDecl("Pair", (Field("a", U32), Field("b", U32)))
    body = [
        ir.Let("p", StructType("Pair"), None),
        ir.Let("q", StructType("Pair"), ir.Var("p")),
        ir.Assign(ir.FieldPlace(ir.VarPlace("q"), "a"), ir.Lit(U32, 7)),
        ir.Return(ir.FieldRead(ir.Var("p"), "a")),
    ]
    built = program(structs=[struct], funcs=[ir.Func("main", (), U32, tuple(body))])
    assert run(built, "main") == 0


# --- inout, section 9 ---


def test_an_inout_scalar_is_written_through():
    callee = ir.Func(
        "bump",
        (ir.Param("n", U32, "inout"),),
        None,
        (ir.Assign(ir.VarPlace("n"), ir.Binary("add", ir.Var("n"), ir.Lit(U32, 1))),),
    )
    caller = ir.Func(
        "main",
        (ir.Param("n", U32, "inout"),),
        None,
        (ir.Call("bump", (ir.InoutArg(ir.VarPlace("n")),), None),),
    )
    cell = Cell(41)
    run(program(funcs=[caller, callee]), "main", [cell])
    assert cell.value == 42


def test_an_in_parameter_does_not_leak_back():
    callee = ir.Func(
        "fill",
        (ir.Param("p", StructType("Pair"), "in"),),
        U32,
        (ir.Return(ir.FieldRead(ir.Var("p"), "a")),),
    )
    caller = ir.Func(
        "main",
        (),
        U32,
        (
            ir.Let("p", StructType("Pair"), None),
            ir.Let("n", U32, ir.Lit(U32, 0)),
            ir.Call("fill", (ir.InArg(ir.Var("p")),), ir.VarPlace("n")),
            ir.Return(ir.Var("n")),
        ),
    )
    struct = StructDecl("Pair", (Field("a", U32), Field("b", U32)))
    assert run(program(structs=[struct], funcs=[caller, callee]), "main") == 0


# --- switch and control flow ---


def test_switch_picks_the_arm_and_falls_back_to_the_default():
    enum = EnumDecl("E", ("A", "B", "C"))

    def which(variant: str) -> int:
        body = [
            ir.Let("e", EnumType("E"), ir.EnumVal("E", variant)),
            ir.Switch(
                ir.Var("e"),
                (ir.Arm("A", (ir.Return(ir.Lit(U32, 1)),)),),
                (ir.Return(ir.Lit(U32, 0)),),
            ),
        ]
        return run(program(enums=[enum], funcs=[ir.Func("main", (), U32, tuple(body))]), "main")

    assert which("A") == 1
    assert which("B") == 0
    assert which("C") == 0


def test_break_leaves_the_loop_and_continue_skips_the_rest():
    body = [
        ir.Let("i", COUNTER, ir.Lit(COUNTER, 5)),
        ir.Let("seen", COUNTER, ir.Lit(COUNTER, 0)),
        ir.While(
            ir.Compare("gt", ir.Var("i"), ir.Lit(COUNTER, 0)),
            ir.Var("i"),
            (
                ir.Assign(ir.VarPlace("i"), ir.Binary("sub", ir.Var("i"), ir.Lit(COUNTER, 1))),
                ir.If(
                    ir.Compare("eq", ir.Var("i"), ir.Lit(COUNTER, 3)),
                    (ir.Continue(),),
                    (),
                ),
                ir.If(ir.Compare("eq", ir.Var("i"), ir.Lit(COUNTER, 1)), (ir.Break(),), ()),
                ir.Assign(
                    ir.VarPlace("seen"), ir.Binary("add", ir.Var("seen"), ir.Lit(COUNTER, 1))
                ),
            ),
        ),
        ir.Return(ir.Var("seen")),
    ]
    assert run(program(funcs=[ir.Func("main", (), COUNTER, tuple(body))]), "main") == 2


# --- the interpreter's own guards ---


def test_a_variant_that_does_not_decrease_is_reported():
    body = [
        ir.Let("i", COUNTER, ir.Lit(COUNTER, 3)),
        ir.While(ir.Compare("gt", ir.Var("i"), ir.Lit(COUNTER, 0)), ir.Lit(COUNTER, 7), ()),
    ]
    with pytest.raises(VariantViolation):
        run(program(funcs=[ir.Func("main", (), None, tuple(body))]), "main")


def test_a_variant_that_traps_is_reported_as_a_variant_defect():
    """Section 8.6: the backends never evaluate a variant, so its trap is not an outcome."""
    body = [
        ir.Let("i", COUNTER, ir.Lit(COUNTER, 3)),
        ir.Let("v", VecType(COUNTER, 4), None),
        ir.While(
            ir.Compare("gt", ir.Var("i"), ir.Lit(COUNTER, 0)),
            ir.IndexRead(ir.Var("v"), ir.Lit(U32, 0)),
            (ir.Assign(ir.VarPlace("i"), ir.Binary("sub", ir.Var("i"), ir.Lit(COUNTER, 1))),),
        ),
    ]
    with pytest.raises(VariantViolation, match="trapped"):
        run(program(funcs=[ir.Func("main", (), None, tuple(body))]), "main")


def test_no_value_reaches_two_inout_parameters():
    """V-022 cannot reach the host API, so the same guarantee is enforced here."""
    main = ir.Func(
        "main",
        (ir.Param("a", BYTES, "inout"), ir.Param("b", BYTES, "inout")),
        None,
        (ir.Push(ir.VarPlace("a"), ir.Lit(U8, 7)),),
    )
    built = program(funcs=[main])

    shared_cell = Cell(Seq(U8, 8, [], 0))
    with pytest.raises(TypeError, match="as well"):
        run(built, "main", [shared_cell, shared_cell])

    # Two cells is no better if they hold the same sequence.
    shared_value = Seq(U8, 8, [], 0)
    with pytest.raises(TypeError, match="as well"):
        run(built, "main", [Cell(shared_value), Cell(shared_value)])

    run(built, "main", [Cell(Seq(U8, 8, [], 0)), Cell(Seq(U8, 8, [], 0))])


def test_a_frozen_view_of_something_still_mutable_is_caught():
    """Otherwise the frozen argument watches the other one change under it."""
    main = ir.Func(
        "main",
        (ir.Param("snapshot", FrozenType(BYTES), "inout"), ir.Param("live", BYTES, "inout")),
        None,
        (ir.Push(ir.VarPlace("live"), ir.Lit(U8, 7)),),
    )
    built = program(funcs=[main])
    shared = Seq(U8, 8, [], 0)
    with pytest.raises(TypeError, match="as well"):
        run(built, "main", [Cell(Frozen(shared)), Cell(shared)])


def test_an_in_argument_counts_too():
    """V-022 covers in arguments because they read; so does this."""
    main = ir.Func(
        "main",
        (ir.Param("snapshot", FrozenType(BYTES), "in"), ir.Param("live", BYTES, "inout")),
        U32,
        (
            ir.Push(ir.VarPlace("live"), ir.Lit(U8, 7)),
            ir.Return(ir.Len(ir.Var("snapshot"))),
        ),
    )
    built = program(funcs=[main])
    shared = Seq(U8, 8, [], 0)
    with pytest.raises(TypeError, match="as well"):
        run(built, "main", [Frozen(shared), Cell(shared)])
    assert run(built, "main", [Frozen(Seq(U8, 8, [], 0)), Cell(Seq(U8, 8, [], 0))]) == 0


def test_two_frozen_views_of_one_value_are_fine():
    """Nobody can write through either, which is the whole point of freezing."""
    main = ir.Func(
        "main",
        (
            ir.Param("a", FrozenType(BYTES), "inout"),
            ir.Param("b", FrozenType(BYTES), "inout"),
        ),
        U32,
        (ir.Return(ir.Binary("add", ir.Len(ir.Var("a")), ir.Len(ir.Var("b")))),),
    )
    shared = Frozen(Seq(U8, 8, [1, 2], 2))
    assert run(program(funcs=[main]), "main", [Cell(shared), Cell(shared)]) == 4


def test_a_value_nested_inside_another_is_caught_too():
    struct = StructDecl("Box", (Field("v", BYTES),))
    main = ir.Func(
        "main",
        (ir.Param("a", StructType("Box"), "inout"), ir.Param("b", BYTES, "inout")),
        None,
        (ir.Push(ir.FieldPlace(ir.VarPlace("a"), "v"), ir.Lit(U8, 7)),),
    )
    built = program(structs=[struct], funcs=[main])
    inner = Seq(U8, 8, [], 0)
    with pytest.raises(TypeError, match="as well"):
        run(built, "main", [Cell(StructValue("Box", {"v": inner})), Cell(inner)])


def test_calling_with_the_wrong_number_of_arguments_says_so():
    main = ir.Func("main", (ir.Param("n", U32, "in"),), None, (ir.Return(None),))
    with pytest.raises(TypeError, match="1 arguments"):
        run(program(funcs=[main]), "main", [])


def test_a_run_that_will_not_end_stops_at_the_fuel_bound():
    body = [
        ir.Let("i", COUNTER, ir.Lit(COUNTER, 100)),
        ir.While(
            ir.Compare("gt", ir.Var("i"), ir.Lit(COUNTER, 0)),
            ir.Var("i"),
            (ir.Assign(ir.VarPlace("i"), ir.Binary("sub", ir.Var("i"), ir.Lit(COUNTER, 1))),),
        ),
    ]
    built = program(funcs=[ir.Func("main", (), None, tuple(body))])
    run(built, "main")
    with pytest.raises(OutOfFuel):
        run(built, "main", fuel=20)


# --- constants ---


def test_a_frozen_constant_reads_as_a_shared_sequence():
    const = ir.Const("TABLE", FrozenType(BYTES), ir.BytesConst(bytes([9, 8, 7])))
    node = ir.IndexRead(ir.ConstRef("TABLE"), ir.Lit(U32, 1))
    assert evaluate(node, U8, consts=[const]) == 8


def test_a_struct_constant_keeps_its_fields():
    struct = StructDecl("Box", (Field("v", BYTES), Field("n", U32)))
    const = ir.Const(
        "BOX",
        FrozenType(StructType("Box")),
        ir.StructConst((("v", ir.BytesConst(b"hi")), ("n", 5))),
    )
    node = ir.Binary(
        "add",
        ir.Len(ir.FieldRead(ir.ConstRef("BOX"), "v")),
        ir.FieldRead(ir.ConstRef("BOX"), "n"),
    )
    assert evaluate(node, U32, structs=[struct], consts=[const]) == 7


def test_the_zero_value_of_an_enum_is_its_first_variant():
    enum = EnumDecl("E", ("First", "Second"))
    body = [
        ir.Let("e", EnumType("E"), None),
        ir.Return(ir.Compare("eq", ir.Var("e"), ir.EnumVal("E", "First"))),
    ]
    assert run(program(enums=[enum], funcs=[ir.Func("main", (), BOOL, tuple(body))]), "main")


def test_the_zero_value_of_a_struct_zeroes_every_field():
    struct = StructDecl("Pair", (Field("a", U32), Field("v", BYTES)))
    body = [
        ir.Let("p", StructType("Pair"), None),
        ir.Return(
            ir.Binary("add", ir.FieldRead(ir.Var("p"), "a"), ir.Len(ir.FieldRead(ir.Var("p"), "v")))
        ),
    ]
    built = program(structs=[struct], funcs=[ir.Func("main", (), U32, tuple(body))])
    assert run(built, "main") == 0


def test_a_struct_value_survives_a_round_through_a_sequence():
    struct = StructDecl("Pair", (Field("a", U32), Field("b", U32)))
    t = VecType(StructType("Pair"), 8)
    body = [
        ir.Let("v", t, None),
        ir.Let("p", StructType("Pair"), None),
        ir.Push(ir.VarPlace("v"), ir.StructVal("Pair", (("a", ir.Lit(U32, 4)), ("b", ir.Lit(U32, 6))))),
        ir.Pop(ir.VarPlace("v"), ir.VarPlace("p")),
        ir.Return(ir.Binary("add", ir.FieldRead(ir.Var("p"), "a"), ir.FieldRead(ir.Var("p"), "b"))),
    ]
    built = program(structs=[struct], funcs=[ir.Func("main", (), U32, tuple(body))])
    assert run(built, "main") == 10
