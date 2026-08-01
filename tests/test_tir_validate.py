"""A negative test for every validator rule of TIR-SPEC.md section 15.

Rule V-001 is the schema version, which the reader checks; its test is in
`test_tir_serialize.py`, because a decoded program no longer carries a version.

Programs here are built straight from `ir` rather than through the DSL, since
half of the point is to construct things the DSL would not make it easy to
write.
"""

from __future__ import annotations

import pytest

from pcretruste.tir import ir, validate
from pcretruste.tir.types import (
    BOOL,
    BYTES,
    CEILING,
    COUNTER,
    I32,
    U8,
    U32,
    EnumDecl,
    EnumType,
    Field,
    FrozenType,
    Prim,
    StructDecl,
    StructType,
    VecType,
)
from pcretruste.tir.validate import ValidationError, provably_disjoint

WORDS = VecType(U32, 8)


def prog(*, enums=(), structs=(), consts=(), funcs=()) -> ir.Program:
    return ir.Program(
        enums=tuple(enums), structs=tuple(structs), consts=tuple(consts), funcs=tuple(funcs)
    )


def func(name="f", params=(), ret=None, body=()) -> ir.Func:
    return ir.Func(name=name, params=tuple(params), ret=ret, body=tuple(body))


def rejects(rule: str, program: ir.Program) -> ValidationError:
    with pytest.raises(ValidationError) as caught:
        validate(program)
    assert caught.value.rule == rule, f"expected {rule}, got {caught.value}"
    return caught.value


def var(name: str) -> ir.VarPlace:
    return ir.VarPlace(name)


# --- program structure ---


def test_v002_one_top_level_namespace():
    rejects("V-002", prog(enums=[EnumDecl("X", ("A",))], funcs=[func("X")]))


@pytest.mark.parametrize(
    "program",
    [
        prog(enums=[EnumDecl("Kind", ("Add",)), EnumDecl("Op", ("Add",))]),
        prog(enums=[EnumDecl("E", ("A",))], structs=[StructDecl("A", (Field("x", U32),))]),
    ],
    ids=["two enums", "a variant over a struct"],
)
def test_v002_variants_are_in_that_namespace_too(program):
    """A variant is a package-level constant in Go, so two of them collide there."""
    rejects("V-002", program)


@pytest.mark.parametrize(
    "program",
    [
        prog(funcs=[func(body=[ir.Call("g", (), None)])]),
        prog(funcs=[func(params=[ir.Param("s", StructType("Nope"), "in")])]),
        prog(funcs=[func(ret=U32, body=[ir.Return(ir.ConstRef("MISSING"))])]),
        prog(
            enums=[EnumDecl("E", ("A",))],
            funcs=[func(ret=EnumType("E"), body=[ir.Return(ir.EnumVal("E", "B"))])],
        ),
    ],
    ids=["function", "struct type", "constant", "variant"],
)
def test_v003_every_name_resolves(program):
    rejects("V-003", program)


@pytest.mark.parametrize(
    "decl", [EnumDecl("E", ()), EnumDecl("E", ("A", "A"))], ids=["empty", "repeated"]
)
def test_v004_enums(decl):
    rejects("V-004", prog(enums=[decl]))


@pytest.mark.parametrize(
    "decl",
    [
        StructDecl("S", ()),
        StructDecl("S", (Field("a", U32), Field("a", U8))),
        StructDecl("S", (Field("self", StructType("S")),)),
    ],
    ids=["empty", "repeated", "recursive"],
)
def test_v005_structs(decl):
    rejects("V-005", prog(structs=[decl]))


@pytest.mark.parametrize(
    "field_type",
    [FrozenType(StructType("S")), VecType(StructType("S"), 4)],
    ids=["through frozen", "through a vec"],
)
def test_v005_catches_a_cycle_closed_by_a_type_constructor(field_type):
    """frozen<S> has S's zero value, so a cycle through one still has none."""
    struct = StructDecl("S", (Field("v", BYTES), Field("next", field_type)))
    rejects("V-005", prog(structs=[struct]))


def test_v005_catches_a_cycle_through_another_struct():
    rejects(
        "V-005",
        prog(
            structs=[
                StructDecl("A", (Field("b", StructType("B")),)),
                StructDecl("B", (Field("a", StructType("A")),)),
            ]
        ),
    )


# --- types ---


def test_v006_a_vec_element_is_copyable():
    rejects("V-006", prog(structs=[StructDecl("S", (Field("v", VecType(BYTES, 4)),))]))


@pytest.mark.parametrize(
    "t",
    [VecType(U32, 0), VecType(U32, -1), VecType(COUNTER, CEILING // 8 + 1)],
    ids=["zero", "negative", "over the ceiling"],
)
def test_v007_a_vec_maximum_fits_under_the_ceiling(t):
    rejects("V-007", prog(structs=[StructDecl("S", (Field("v", t),))]))


def test_v008_frozen_wants_something_linear():
    rejects("V-008", prog(structs=[StructDecl("S", (Field("f", FrozenType(U32)),))]))


def test_v009_frozen_does_not_nest():
    rejects("V-009", prog(structs=[StructDecl("S", (Field("f", FrozenType(FrozenType(BYTES))),))]))


def test_v010_a_full_width_u8_sequence_is_spelled_bytes():
    rejects("V-010", prog(structs=[StructDecl("S", (Field("v", VecType(U8, CEILING)),))]))


# --- constants ---


def test_v011_a_constant_is_scalar_or_frozen():
    rejects("V-011", prog(consts=[ir.Const("B", BYTES, ir.BytesConst(b""))]))


@pytest.mark.parametrize(
    "const",
    [
        ir.Const("N", U8, 300),
        ir.Const("N", U32, True),
        ir.Const("N", BOOL, 1),
        ir.Const("V", FrozenType(VecType(U32, 2)), ir.VecConst((1, 2, 3))),
        ir.Const("V", FrozenType(BYTES), 7),
    ],
    ids=["out of range", "a bool is not a number", "a number is not a bool", "too long", "shape"],
)
def test_v012_a_constant_matches_its_type(const):
    rejects("V-012", prog(consts=[const]))


@pytest.mark.parametrize(
    "fields",
    [
        (("v", ir.BytesConst(b"")),),
        (("v", ir.BytesConst(b"")), ("n", 1), ("n", 2)),
    ],
    ids=["a field left out", "a field given twice"],
)
def test_v012_a_frozen_struct_constant_names_every_field_exactly_once(fields):
    struct = StructDecl("S", (Field("v", BYTES), Field("n", U32)))
    const = ir.Const("C", FrozenType(StructType("S")), ir.StructConst(fields))
    rejects("V-012", prog(structs=[struct], consts=[const]))


def test_v003_a_constant_naming_a_variant_the_enum_lacks():
    enum = EnumDecl("E", ("A",))
    const = ir.Const("C", EnumType("E"), ir.EnumConst("B"))
    rejects("V-003", prog(enums=[enum], consts=[const]))


# --- expressions ---


@pytest.mark.parametrize(
    "program",
    [
        prog(
            funcs=[
                func(
                    ret=U32,
                    body=[ir.Return(ir.Binary("add", ir.Lit(U32, 1), ir.Lit(U8, 1)))],
                )
            ]
        ),
        prog(funcs=[func(body=[ir.If(ir.Lit(U32, 1), (), ())])]),
        prog(funcs=[func(ret=U32, body=[ir.Return(ir.Len(ir.Lit(U32, 1)))])]),
        prog(
            funcs=[
                func(
                    params=[ir.Param("v", WORDS, "inout")],
                    ret=U32,
                    body=[ir.Return(ir.IndexRead(ir.Var("v"), ir.Lit(I32, 0)))],
                )
            ]
        ),
        prog(
            funcs=[
                func(ret=BOOL, body=[ir.Return(ir.Binary("add", ir.Lit(BOOL, True), ir.Lit(BOOL, True)))])
            ]
        ),
        prog(
            enums=[EnumDecl("E", ("A", "B"))],
            funcs=[
                func(
                    ret=BOOL,
                    body=[
                        ir.Return(ir.Compare("lt", ir.EnumVal("E", "A"), ir.EnumVal("E", "B")))
                    ],
                )
            ],
        ),
        prog(
            funcs=[func(ret=U32, body=[ir.Return(ir.Cast(U32, ir.EnumVal("E", "A")))])],
            enums=[EnumDecl("E", ("A",))],
        ),
    ],
    ids=[
        "mixed operand widths",
        "a condition is a bool",
        "len of a scalar",
        "an index is a u32",
        "arithmetic on bools",
        "ordering enum variants",
        "casting an enum",
    ],
)
def test_v013_expressions_are_well_typed(program):
    rejects("V-013", program)


def test_a_bool_casts_to_an_integer():
    validate(prog(funcs=[func(ret=U32, body=[ir.Return(ir.Cast(U32, ir.Lit(BOOL, True)))])]))


@pytest.mark.parametrize(
    "t, value",
    [(U8, 300), (I32, 2**31), (COUNTER, -1), (U32, True), (BOOL, 1)],
    ids=[
        "past a u8",
        "past an i32",
        "a negative counter",
        "a bool for a number",
        "a number for a bool",
    ],
)
def test_v014_a_literal_is_in_range(t, value):
    rejects("V-014", prog(funcs=[func(ret=t, body=[ir.Return(ir.Lit(t, value))])]))


@pytest.mark.parametrize(
    "node",
    [
        ir.Unary("wat", ir.Lit(U32, 1)),
        ir.Binary("wat", ir.Lit(U32, 1), ir.Lit(U32, 1)),
        ir.Compare("wat", ir.Lit(U32, 1), ir.Lit(U32, 1)),
        ir.DivRem("wat", ir.Lit(U32, 1), ir.Lit(U32, 1), ir.Lit(U32, 0)),
        ir.Shift("wat", ir.Lit(U32, 1), 1),
        ir.Logical("wat", ir.Lit(BOOL, True), ir.Lit(BOOL, False)),
    ],
    ids=["un", "bin", "cmp", "divrem", "shift", "logical"],
)
def test_v013_the_operator_inventories_are_closed(node):
    """The reader has never heard of these; a program built straight from ir has not been read."""
    rejects("V-013", prog(funcs=[func(body=[ir.Let("x", U32, ir.Cast(U32, node))])]))


def test_v014_a_type_with_no_literal_form():
    """The reader cannot build one, but the DSL will happily write bytes_(5)."""
    body = [ir.Let("n", U32, ir.Cast(U32, ir.Lit(BYTES, 5)))]
    rejects("V-014", prog(funcs=[func(body=body)]))


def test_v015_a_shift_count_is_in_range():
    rejects(
        "V-015",
        prog(funcs=[func(ret=U8, body=[ir.Return(ir.Shift("shl", ir.Lit(U8, 1), 8))])]),
    )


@pytest.mark.parametrize(
    "op, t", [("shr", I32), ("sar", U32), ("sar", U8)], ids=["shr on i32", "sar on u32", "sar on u8"]
)
def test_v016_the_shift_spelling_matches_the_operand(op, t):
    rejects("V-016", prog(funcs=[func(ret=t, body=[ir.Return(ir.Shift(op, ir.Lit(t, 1), 1))])]))


@pytest.mark.parametrize(
    "fields",
    [
        (("a", ir.Lit(U32, 1)),),
        (("a", ir.Lit(U32, 1)), ("b", ir.Lit(U32, 2)), ("b", ir.Lit(U32, 3))),
    ],
    ids=["a field left out", "a field given twice"],
)
def test_v017_a_struct_literal_names_every_field_exactly_once(fields):
    struct = StructDecl("S", (Field("a", U32), Field("b", U32)))
    body = [ir.Return(ir.StructVal("S", fields))]
    rejects("V-017", prog(structs=[struct], funcs=[func(ret=StructType("S"), body=body)]))


def test_v017_a_linear_struct_has_no_literal():
    struct = StructDecl("S", (Field("v", BYTES), Field("n", U32)))
    literal = ir.StructVal("S", (("v", ir.Var("b")), ("n", ir.Lit(U32, 1))))
    body = [
        ir.Let("b", BYTES, None),
        ir.Let("n", U32, ir.FieldRead(literal, "n")),
    ]
    rejects("V-017", prog(structs=[struct], funcs=[func(body=body)]))


# --- functions and calls ---


def test_v018_an_in_parameter_is_copyable():
    rejects("V-018", prog(funcs=[func(params=[ir.Param("v", BYTES, "in")])]))


def test_v019_a_return_type_is_copyable():
    rejects(
        "V-019",
        prog(
            funcs=[
                func(
                    params=[ir.Param("v", BYTES, "inout")],
                    ret=BYTES,
                    body=[ir.Return(ir.Var("v"))],
                )
            ]
        ),
    )


@pytest.mark.parametrize(
    "dest, callee_ret, callee_body",
    [
        (var("n"), None, ()),
        (None, U32, (ir.Return(ir.Lit(U32, 0)),)),
    ],
    ids=["a dest for nothing", "nowhere to put the answer"],
)
def test_v020_a_dest_appears_exactly_when_the_callee_returns(dest, callee_ret, callee_body):
    caller = func(
        "caller",
        body=[ir.Let("n", U32, ir.Lit(U32, 0)), ir.Call("g", (), dest)],
    )
    rejects("V-020", prog(funcs=[caller, func("g", ret=callee_ret, body=callee_body)]))


def test_v020_a_dest_has_the_return_type():
    caller = func(
        "caller", body=[ir.Let("n", U8, ir.Lit(U8, 0)), ir.Call("g", (), var("n"))]
    )
    callee = func("g", ret=U32, body=[ir.Return(ir.Lit(U32, 0))])
    rejects("V-020", prog(funcs=[caller, callee]))


def test_v021_a_function_does_not_call_itself():
    rejects("V-021", prog(funcs=[func(body=[ir.Call("f", (), None)])]))


def test_v021_catches_a_longer_cycle():
    rejects(
        "V-021",
        prog(
            funcs=[
                func("a", body=[ir.Call("b", (), None)]),
                func("b", body=[ir.Call("c", (), None)]),
                func("c", body=[ir.Call("a", (), None)]),
            ]
        ),
    )


def test_v022_the_same_place_cannot_travel_twice():
    callee = func("g", params=[ir.Param("x", WORDS, "inout"), ir.Param("y", WORDS, "inout")])
    caller = func(
        "caller",
        params=[ir.Param("v", WORDS, "inout")],
        body=[ir.Call("g", (ir.InoutArg(var("v")), ir.InoutArg(var("v"))), None)],
    )
    rejects("V-022", prog(funcs=[caller, callee]))


def test_v022_catches_a_sequence_and_an_element_of_it():
    callee = func("g", params=[ir.Param("x", U32, "inout"), ir.Param("y", WORDS, "inout")])
    caller = func(
        "caller",
        params=[ir.Param("v", WORDS, "inout")],
        body=[
            ir.Let("i", U32, ir.Lit(U32, 0)),
            ir.Call(
                "g",
                (
                    ir.InoutArg(ir.IndexPlace(var("v"), ir.Var("i"))),
                    ir.InoutArg(var("v")),
                ),
                None,
            ),
        ],
    )
    rejects("V-022", prog(funcs=[caller, callee]))


def test_v022_catches_a_struct_and_its_own_field():
    struct = StructDecl("S", (Field("v", WORDS), Field("n", U32)))
    callee = func(
        "g",
        params=[ir.Param("x", StructType("S"), "inout"), ir.Param("y", WORDS, "inout")],
    )
    caller = func(
        "caller",
        params=[ir.Param("s", StructType("S"), "inout")],
        body=[
            ir.Call(
                "g",
                (ir.InoutArg(var("s")), ir.InoutArg(ir.FieldPlace(var("s"), "v"))),
                None,
            )
        ],
    )
    rejects("V-022", prog(structs=[struct], funcs=[caller, callee]))


def test_v022_catches_an_in_argument_reading_an_inout_place():
    callee = func("g", params=[ir.Param("x", WORDS, "inout"), ir.Param("n", U32, "in")])
    caller = func(
        "caller",
        params=[ir.Param("v", WORDS, "inout")],
        body=[ir.Call("g", (ir.InoutArg(var("v")), ir.InArg(ir.Len(ir.Var("v")))), None)],
    )
    rejects("V-022", prog(funcs=[caller, callee]))


def test_v022_catches_an_in_argument_whose_index_reads_an_inout_place():
    """The spec's own example: f(inout i, in v[i]) reads i while i is being written."""
    callee = func("g", params=[ir.Param("k", U32, "inout"), ir.Param("n", U32, "in")])
    caller = func(
        "caller",
        params=[ir.Param("v", WORDS, "inout")],
        body=[
            ir.Let("i", U32, ir.Lit(U32, 0)),
            ir.Call(
                "g",
                (
                    ir.InoutArg(var("i")),
                    ir.InArg(ir.IndexRead(ir.Var("v"), ir.Var("i"))),
                ),
                None,
            ),
        ],
    )
    rejects("V-022", prog(funcs=[caller, callee]))


def test_v022_catches_a_destination_that_overlaps_an_inout_argument():
    callee = func("g", params=[ir.Param("x", WORDS, "inout")], ret=U32, body=[ir.Return(ir.Lit(U32, 0))])
    caller = func(
        "caller",
        params=[ir.Param("v", WORDS, "inout")],
        body=[
            ir.Call(
                "g",
                (ir.InoutArg(var("v")),),
                ir.IndexPlace(var("v"), ir.Lit(U32, 0)),
            )
        ],
    )
    rejects("V-022", prog(funcs=[caller, callee]))


def test_two_literal_indices_settle_disjointness():
    callee = func("g", params=[ir.Param("x", U32, "inout"), ir.Param("y", U32, "inout")])
    caller = func(
        "caller",
        params=[ir.Param("v", WORDS, "inout")],
        body=[
            ir.Call(
                "g",
                (
                    ir.InoutArg(ir.IndexPlace(var("v"), ir.Lit(U32, 0))),
                    ir.InoutArg(ir.IndexPlace(var("v"), ir.Lit(U32, 1))),
                ),
                None,
            )
        ],
    )
    validate(prog(funcs=[caller, callee]))


def test_two_fields_of_one_element_settle_disjointness():
    """The equal indices leave the question open; the field names close it."""
    struct = StructDecl("Pair", (Field("a", U32), Field("b", U32)))
    pairs = VecType(StructType("Pair"), 4)
    callee = func("g", params=[ir.Param("x", U32, "inout"), ir.Param("y", U32, "inout")])
    element = ir.IndexPlace(var("v"), ir.Lit(U32, 0))
    caller = func(
        "caller",
        params=[ir.Param("v", pairs, "inout")],
        body=[
            ir.Call(
                "g",
                (
                    ir.InoutArg(ir.FieldPlace(element, "a")),
                    ir.InoutArg(ir.FieldPlace(element, "b")),
                ),
                None,
            )
        ],
    )
    validate(prog(structs=[struct], funcs=[caller, callee]))


# --- statements ---


def test_v023_a_linear_value_is_not_read():
    body = [ir.Let("v", BYTES, None), ir.Let("n", U32, ir.Cast(U32, ir.Var("v")))]
    rejects("V-023", prog(funcs=[func(body=body)]))


def test_v024_a_linear_value_is_not_assigned():
    body = [ir.Let("a", BYTES, None), ir.Let("b", BYTES, None), ir.Assign(var("a"), ir.Var("b"))]
    rejects("V-024", prog(funcs=[func(body=body)]))


def test_v025_an_in_parameter_is_immutable():
    rejects(
        "V-025",
        prog(
            funcs=[
                func(
                    params=[ir.Param("n", U32, "in")],
                    body=[ir.Assign(var("n"), ir.Lit(U32, 1))],
                )
            ]
        ),
    )


def test_v026_no_write_through_a_frozen_value():
    body = [
        ir.Let("fz", FrozenType(BYTES), None),
        ir.Assign(ir.IndexPlace(var("fz"), ir.Lit(U32, 0)), ir.Lit(U8, 1)),
    ]
    rejects("V-026", prog(funcs=[func(body=body)]))


def test_v026_no_sequence_statement_on_a_frozen_sequence():
    body = [ir.Let("fz", FrozenType(BYTES), None), ir.Push(var("fz"), ir.Lit(U8, 1))]
    rejects("V-026", prog(funcs=[func(body=body)]))


@pytest.mark.parametrize(
    "body",
    [
        [ir.Return(None), ir.Return(None)],
        [ir.While(ir.Lit(BOOL, True), ir.Lit(COUNTER, 0), (ir.Break(), ir.Return(None)))],
        [ir.While(ir.Lit(BOOL, True), ir.Lit(COUNTER, 0), (ir.Continue(), ir.Break()))],
    ],
    ids=["after a return", "after a break", "after a continue"],
)
def test_v027_nothing_follows_a_statement_that_never_falls_through(body):
    rejects("V-027", prog(funcs=[func(body=body)]))


@pytest.mark.parametrize(
    "stmt, rule",
    [
        (ir.Take(var("a"), var("a")), "V-028"),
        (ir.Swap(var("a"), var("a")), "V-029"),
        (ir.Copy(var("a"), ir.Var("a")), "V-030"),
    ],
    ids=["take", "swap", "copy"],
)
def test_movement_statements_want_disjoint_places(stmt, rule):
    rejects(rule, prog(funcs=[func(body=[ir.Let("a", BYTES, None), stmt])]))


def test_v028_take_moves_between_places_of_one_type():
    body = [ir.Let("a", BYTES, None), ir.Let("b", WORDS, None), ir.Take(var("a"), var("b"))]
    rejects("V-028", prog(funcs=[func(body=body)]))


def test_v029_swap_exchanges_places_of_one_type():
    body = [ir.Let("a", BYTES, None), ir.Let("b", WORDS, None), ir.Swap(var("a"), var("b"))]
    rejects("V-029", prog(funcs=[func(body=body)]))


def test_v030_copy_makes_a_t_from_a_t_or_a_frozen_t():
    body = [ir.Let("a", BYTES, None), ir.Let("b", WORDS, None), ir.Copy(var("a"), ir.Var("b"))]
    rejects("V-030", prog(funcs=[func(body=body)]))


@pytest.mark.parametrize(
    "stmt",
    [
        ir.Push(var("v"), ir.Len(ir.Var("v"))),
        ir.Pop(var("v"), ir.IndexPlace(var("v"), ir.Lit(U32, 0))),
    ],
    ids=["push", "pop"],
)
def test_v031_a_sequence_statement_does_not_touch_its_own_sequence(stmt):
    rejects("V-031", prog(funcs=[func(params=[ir.Param("v", WORDS, "inout")], body=[stmt])]))


def switch_program(arms, default) -> ir.Program:
    body = [
        ir.Let("e", EnumType("E"), ir.EnumVal("E", "A")),
        ir.Switch(ir.Var("e"), tuple(arms), default),
    ]
    return prog(enums=[EnumDecl("E", ("A", "B"))], funcs=[func(body=body)])


@pytest.mark.parametrize(
    "arms, default",
    [
        ([ir.Arm("A", ())], None),
        ([ir.Arm("A", ()), ir.Arm("B", ())], ()),
        ([ir.Arm("A", ()), ir.Arm("A", ())], ()),
        ([ir.Arm("C", ())], ()),
    ],
    ids=["a gap with no default", "covered and still defaulted", "a repeated arm", "a foreign arm"],
)
def test_v032_switch_arms(arms, default):
    rejects("V-032", switch_program(arms, default))


@pytest.mark.parametrize("stmt", [ir.Break(), ir.Continue()], ids=["break", "continue"])
def test_v033_jumps_belong_to_a_loop(stmt):
    rejects("V-033", prog(funcs=[func(body=[stmt])]))


@pytest.mark.parametrize(
    "ret, value",
    [(None, ir.Lit(U32, 1)), (U32, None), (U32, ir.Lit(U8, 1))],
    ids=["a value from a void function", "no value from a value function", "the wrong type"],
)
def test_v034_a_return_matches_the_signature(ret, value):
    rejects("V-034", prog(funcs=[func(ret=ret, body=[ir.Return(value)])]))


@pytest.mark.parametrize(
    "body",
    [
        [],
        [ir.If(ir.Lit(BOOL, True), (ir.Return(ir.Lit(U32, 1)),), ())],
        [ir.While(ir.Lit(BOOL, True), ir.Lit(COUNTER, 0), (ir.Return(ir.Lit(U32, 1)),))],
    ],
    ids=["an empty body", "only one arm returns", "a loop is not a guarantee"],
)
def test_v035_every_path_returns(body):
    rejects("V-035", prog(funcs=[func(ret=U32, body=body)]))


def test_v035_accepts_an_if_where_both_arms_return():
    body = [
        ir.If(ir.Lit(BOOL, True), (ir.Return(ir.Lit(U32, 1)),), (ir.Return(ir.Lit(U32, 2)),))
    ]
    validate(prog(funcs=[func(ret=U32, body=body)]))


def test_v036_a_loop_variant_is_a_counter():
    rejects(
        "V-036",
        prog(funcs=[func(body=[ir.While(ir.Lit(BOOL, False), ir.Lit(U32, 0), ())])]),
    )


def test_v037_a_linear_local_takes_no_initializer():
    rejects("V-037", prog(funcs=[func(body=[ir.Let("v", BYTES, ir.Lit(U32, 0))])]))


@pytest.mark.parametrize(
    "program",
    [
        prog(funcs=[func(body=[ir.Let("a", U32, ir.Lit(U32, 0)), ir.Let("a", U8, ir.Lit(U8, 0))])]),
        prog(
            consts=[ir.Const("N", U32, 1)],
            funcs=[func(body=[ir.Let("N", U32, ir.Lit(U32, 0))])],
        ),
        prog(funcs=[func(params=[ir.Param("n", U32, "in"), ir.Param("n", U8, "in")])]),
        prog(funcs=[func(params=[ir.Param("f", U32, "in")])]),
    ],
    ids=["two locals", "a local over a constant", "two parameters", "a parameter over a function"],
)
def test_v038_names_do_not_shadow(program):
    rejects("V-038", program)


def test_v038_catches_a_name_reused_in_a_sibling_block():
    body = [
        ir.If(ir.Lit(BOOL, True), (ir.Let("x", U32, ir.Lit(U32, 0)),), ()),
        ir.If(ir.Lit(BOOL, True), (ir.Let("x", U32, ir.Lit(U32, 0)),), ()),
    ]
    rejects("V-038", prog(funcs=[func(body=body)]))


def test_v040_a_parameter_mode_is_one_of_two_words():
    rejects("V-040", prog(funcs=[func(params=[ir.Param("n", U32, "out")])]))


@pytest.mark.parametrize(
    "program",
    [
        prog(enums=[EnumDecl("not a name", ("A",))]),
        prog(enums=[EnumDecl("E", ("not a variant",))]),
        prog(structs=[StructDecl("S", (Field("9lives", U32),))]),
        prog(consts=[ir.Const("", U32, 1)]),
        prog(funcs=[func(name="a" * 65)]),
        prog(funcs=[func(params=[ir.Param("n-1", U32, "in")])]),
        prog(funcs=[func(body=[ir.Let("class name", U32, ir.Lit(U32, 0))])]),
    ],
    ids=["enum", "variant", "field", "constant", "function", "parameter", "local"],
)
def test_v041_declared_names_are_identifiers(program):
    rejects("V-041", program)


@pytest.mark.parametrize(
    "rule, program",
    [
        ("V-042", prog(funcs=[func(body=[ir.Arm("A", ())])])),
        ("V-042", prog(funcs=[func(body=[ir.Let("x", Prim("word"), None)])])),
        ("V-042", prog(funcs=[func(ret=U32, body=[ir.Return(ir.VarPlace("x"))])])),
        ("V-042", prog(funcs=[func(body=[ir.Assign(ir.Var("x"), ir.Lit(U32, 1))])])),
        ("V-042", prog(structs=[EnumDecl("E", ("A",))])),
        ("V-042", prog(enums=[EnumDecl("E", ["A"])])),
        ("V-042", prog(funcs=[ir.Func("f", (), None, [ir.Return()])])),
        ("V-042", prog(funcs=[func(body=[ir.Switch(ir.Lit(U32, 0), (ir.Break(),), None)])])),
        ("V-042", prog(funcs=[func(body=[ir.Call("f", (ir.Lit(U32, 0),), None)])])),
        ("V-042", prog(consts=[ir.Const("K", FrozenType(VecType(U32, 4)), ir.VecConst([1]))])),
        ("V-014", prog(funcs=[func(ret=U8, body=[ir.Return(ir.Lit(U8, 1.0))])])),
        (
            "V-015",
            prog(funcs=[func(ret=U8, body=[ir.Return(ir.Shift("shl", ir.Lit(U8, 1), 1.0))])]),
        ),
        ("V-007", prog(structs=[StructDecl("S", (Field("v", VecType(U8, 4.0)),))])),
        ("V-012", prog(consts=[ir.Const("K", FrozenType(BYTES), ir.BytesConst("00"))])),
    ],
    ids=[
        "an arm is not a statement",
        "a type that does not exist",
        "a place where an expression belongs",
        "an expression where a place belongs",
        "an enum among the structs",
        "variants that are not a list",
        "a body that is not a list",
        "a switch arm that is not an arm",
        "an argument that is not one",
        "constant elements that are not a list",
        "a literal that is not an integer",
        "a shift count that is not an integer",
        "a vec maximum that is not an integer",
        "a bytes payload that is not bytes",
    ],
)
def test_v042_every_node_is_a_form_the_document_defines(rule, program):
    """The reader cannot build any of these; a program straight from ir was never read."""
    rejects(rule, program)


class Impostor:
    """Something that resolves like a name and serializes like nothing at all."""

    def __init__(self, target: str) -> None:
        self.target = target

    def __hash__(self) -> int:
        return hash(self.target)

    def __eq__(self, other: object) -> bool:
        return other == self.target


@pytest.mark.parametrize(
    "program",
    [
        prog(funcs=[func(ret=Prim(Impostor("u32")), body=[ir.Return(ir.Lit(U32, 0))])]),
        prog(funcs=[func(params=[ir.Param("v", U32, "in")], ret=U32,
                         body=[ir.Return(ir.Var(Impostor("v")))])]),
        prog(funcs=[func(params=[ir.Param("v", U32, Impostor("in"))])]),
        prog(funcs=[func(ret=U32, body=[
            ir.Return(ir.Binary(Impostor("add"), ir.Lit(U32, 1), ir.Lit(U32, 2)))
        ])]),
    ],
    ids=["a type name", "a variable", "a parameter mode", "an operator"],
)
def test_v042_a_name_that_only_claims_to_be_one(program):
    """Every lookup here is a dictionary lookup, and a dictionary asks only for equality.

    Resolution would succeed and the serializer would then have nothing to
    write, which puts the failure well past the boundary. So the leaves are
    checked for what they are, not for what they answer.
    """
    rejects("V-042", program)


@pytest.mark.parametrize("name", [*sorted(ir.RESERVED), "tir_helper"])
def test_v043_reserved_names_are_refused(name):
    """The whole set, not a sample: a word added to it should not need a test added too."""
    rejects("V-043", prog(funcs=[func(name=name)]))


@pytest.mark.parametrize("name", sorted(ir.RESERVED))
def test_v043_reserves_only_names_something_else_would_have_allowed(name):
    """A reserved word that V-041 refuses anyway is an entry nothing can reach."""
    assert ir.IDENTIFIER.match(name) and len(name) <= ir.MAX_IDENTIFIER
    assert not name.startswith(ir.RESERVED_PREFIX)


def test_v043_covers_every_kind_of_declared_name():
    rejects("V-043", prog(enums=[EnumDecl("E", ("var",))]))
    rejects("V-043", prog(structs=[StructDecl("S", (Field("func", U32),))]))
    rejects("V-043", prog(funcs=[func(params=[ir.Param("class", U32, "in")])]))
    rejects("V-043", prog(funcs=[func(body=[ir.Let("range", U32, ir.Lit(U32, 0))])]))


# --- V-044, the nesting bound ---
#
# Each builder takes a count and nests that many levels. The pair of tests
# below asks the same two questions of every one: that the deepest program the
# rule admits really works, end to end, and that one level more is refused with
# a rule number rather than a RecursionError from whichever walk ran out first.


def nested_expression(n: int) -> ir.Program:
    e: ir.Expr = ir.Lit(U32, 1)
    for _ in range(n):
        e = ir.Unary("bnot", e)
    return prog(funcs=[func(body=[ir.Let("x", U32, e)])])


def nested_statement(n: int) -> ir.Program:
    body: tuple[ir.Stmt, ...] = (ir.Return(),)
    for _ in range(n):
        body = (ir.If(ir.Lit(BOOL, True), body, ()),)
    return prog(funcs=[func(body=body)])


def nested_place(n: int) -> ir.Program:
    struct = StructDecl("S", (Field("v", WORDS), Field("n", U32)))
    place: ir.Place = var("s")
    for _ in range(n):
        place = ir.IndexPlace(ir.FieldPlace(place, "v"), ir.Lit(U32, 0))
    return prog(
        structs=[struct],
        funcs=[
            func(
                params=[ir.Param("s", StructType("S"), "inout")],
                body=[ir.Assign(place, ir.Lit(U32, 0))],
            )
        ],
    )


def struct_chain(n: int) -> ir.Program:
    structs = [
        StructDecl(
            f"S{i:05d}",
            (Field("x", U32),) if i == n - 1 else (Field("n", StructType(f"S{i + 1:05d}")),),
        )
        for i in range(n)
    ]
    # The local is what makes the interpreter build the whole zero value, and
    # the `in` parameter is what asks the head of the chain whether it is
    # linear. Both walk the containment chain to the end.
    head = StructType("S00000")
    return prog(
        structs=structs,
        funcs=[
            func(body=[ir.Let("local", head, None)]),
            func("weigh", params=[ir.Param("s", head, "in")]),
        ],
    )


def call_chain(n: int) -> ir.Program:
    name = ["f"] + [f"f{i:05d}" for i in range(1, n)]
    return prog(
        funcs=[
            func(name[i], body=[ir.Return()] if i == n - 1 else [ir.Call(name[i + 1], (), None)])
            for i in range(n)
        ]
    )


# How many levels of each builder land exactly on the bound. An expression sits
# inside the statement that holds it, so it reaches the bound one level sooner;
# the two declaration chains are counted in declarations and reach it on the
# nose.
AT_THE_BOUND = [
    (nested_expression, ir.MAX_DEPTH - 2),
    (nested_statement, ir.MAX_DEPTH - 1),
    (struct_chain, ir.MAX_DEPTH),
    (call_chain, ir.MAX_DEPTH),
]
BUILDER_IDS = ["expression", "statement", "struct containment", "call graph"]


@pytest.mark.parametrize("build, levels", AT_THE_BOUND, ids=BUILDER_IDS)
def test_v044_admits_a_program_that_reaches_the_bound(build, levels):
    """A bound is worth nothing unless everything downstream survives reaching it.

    Which is the whole argument for having one: the reader, the serializer and
    the interpreter all recurse, and so will the Lean decoder and both
    printers. So the deepest program the rule admits gets run through every
    one of them that exists today.
    """
    from pcretruste.tir import dumps, loads, run

    program = build(levels)
    validate(program)
    assert loads(dumps(program)) == program
    assert run(program, "f", [], fuel=10_000) is None


@pytest.mark.parametrize(
    "build, levels",
    [*AT_THE_BOUND, (nested_place, ir.MAX_DEPTH)],
    ids=[*BUILDER_IDS, "place"],
)
def test_v044_refuses_one_level_more(build, levels):
    """A place never gets a matching case above: `s.v[0]` is a u32, so nothing
    well typed nests one much deeper than the struct it projects. The shape
    pass still has to refuse a deep one, because it reads the tree before
    anything has typed it."""
    rejects("V-044", build(levels + 1))


def test_a_validated_program_can_always_be_written_and_read_back():
    """What V-041 is for: validation is meant to imply the artifact round-trips."""
    from pcretruste.tir import dumps, loads

    program = prog(
        enums=[EnumDecl("E", ("A",))],
        funcs=[func(ret=EnumType("E"), body=[ir.Return(ir.EnumVal("E", "A"))])],
    )
    validate(program)
    assert loads(dumps(program)) == program


@pytest.mark.parametrize(
    "body",
    [
        [ir.Return(ir.Var("nope"))],
        [ir.If(ir.Lit(BOOL, True), (ir.Let("x", U32, ir.Lit(U32, 0)),), ()), ir.Return(ir.Var("x"))],
    ],
    ids=["never declared", "out of scope"],
)
def test_v039_every_variable_resolves(body):
    rejects("V-039", prog(funcs=[func(ret=U32, body=body)]))


# --- the disjointness relation itself ---


@pytest.mark.parametrize(
    "a, b, disjoint",
    [
        (("v", ()), ("w", ()), True),
        (("v", ()), ("v", ()), False),
        (("s", (("field", "a"),)), ("s", (("field", "b"),)), True),
        (("s", (("field", "a"),)), ("s", ()), False),
        (("v", (("index", 0),)), ("v", (("index", 1),)), True),
        (("v", (("index", 0),)), ("v", (("index", 0),)), False),
        (("v", (("index", None),)), ("v", (("index", 0),)), False),
        (("v", (("index", None),)), ("v", (("index", None),)), False),
        # Equal projections settle nothing on their own: the comparison has to
        # carry on to the next pair rather than give up on the whole path.
        (("v", (("index", 0), ("field", "a"))), ("v", (("index", 0), ("field", "b"))), True),
        (("v", (("index", 0), ("field", "a"))), ("v", (("index", 1), ("field", "a"))), True),
        (("v", (("index", 0), ("field", "a"))), ("v", (("index", 0), ("field", "a"))), False),
        (("s", (("field", "a"), ("index", 0))), ("s", (("field", "a"), ("index", 1))), True),
    ],
)
def test_provably_disjoint(a, b, disjoint):
    assert provably_disjoint(a, b) is disjoint
    assert provably_disjoint(b, a) is disjoint


# --- a few shapes that must stay legal ---


def test_a_copyable_field_of_a_linear_struct_is_readable():
    struct = StructDecl("S", (Field("v", BYTES), Field("n", U32)))
    body = [
        ir.Let("s", StructType("S"), None),
        ir.Let("n", U32, ir.FieldRead(ir.Var("s"), "n")),
        ir.Let("size", U32, ir.Len(ir.FieldRead(ir.Var("s"), "v"))),
    ]
    validate(prog(structs=[struct], funcs=[func(body=body)]))


def test_a_frozen_value_travels_by_value():
    body = [
        ir.Let("v", BYTES, None),
        ir.Let("fz", FrozenType(BYTES), None),
        ir.Freeze(var("fz"), var("v")),
        ir.Call("g", (ir.InArg(ir.Var("fz")),), None),
    ]
    callee = func("g", params=[ir.Param("shared", FrozenType(BYTES), "in")])
    validate(prog(funcs=[func(body=body), callee]))


def test_copy_may_read_a_linear_place():
    body = [ir.Let("a", BYTES, None), ir.Let("b", BYTES, None), ir.Copy(var("a"), ir.Var("b"))]
    validate(prog(funcs=[func(body=body)]))


def test_copy_may_unfreeze_into_a_mutable_value():
    body = [
        ir.Let("a", BYTES, None),
        ir.Let("fz", FrozenType(BYTES), None),
        ir.Copy(var("a"), ir.Var("fz")),
    ]
    validate(prog(funcs=[func(body=body)]))
