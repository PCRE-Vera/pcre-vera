"""The authoring DSL: what it builds, and the few mistakes it refuses to build.

The DSL is untrusted by design, so there is little to check here beyond "the
node it emitted is the node it should have emitted". The exceptions are the
block bookkeeping, where a misplaced `with` would silently produce a different
program, and operand coercion, where accepting a bare Python integer would mean
guessing a width.
"""

from __future__ import annotations

import pytest

from pcrevera.dsl import Module, bytes_, counter, frozen, inout, land, lnot, lor, u8, u32, vec
from pcrevera.dsl.builder import Expr
from pcrevera.tir import ir, validate
from pcrevera.tir.types import U32, EnumType, FrozenType, StructType, VecType


def test_a_literal_is_written_through_its_type():
    assert u32(7).node == ir.Lit(U32, 7)


def test_a_bare_integer_is_refused_as_an_operand():
    with pytest.raises(TypeError, match="u32"):
        u32(1) + 1


def test_operators_build_the_nodes_they_name():
    a, b = u32(1), u32(2)
    assert (a + b).node == ir.Binary("add", a.node, b.node)
    assert (a < b).node == ir.Compare("lt", a.node, b.node)
    assert (a ^ b).node == ir.Binary("xor", a.node, b.node)
    assert (~a).node == ir.Unary("bnot", a.node)
    assert (-a).node == ir.Unary("neg", a.node)
    assert a.shl(3).node == ir.Shift("shl", a.node, 3)
    assert a.div(b, u32(0)).node == ir.DivRem("div", a.node, b.node, u32(0).node)
    assert a.cast(u8).node == ir.Cast(u8.t, a.node)


def test_the_boolean_helpers_build_conditionals():
    from pcrevera.dsl import boolean

    t, f = boolean(True), boolean(False)
    assert land(t, f).node == ir.Logical("and", t.node, f.node)
    assert lor(t, f).node == ir.Logical("or", t.node, f.node)
    assert lnot(t).node == ir.Unary("not", t.node)


def test_a_reference_carries_both_a_place_and_an_expression():
    m = Module()
    Pair = m.struct("Pair", [("a", u32), ("b", u32)])
    f = m.func("f", params=[("p", Pair, "inout")])
    p = f["p"]
    assert p.place == ir.VarPlace("p")
    assert p.node == ir.Var("p")
    assert p.field("a").place == ir.FieldPlace(ir.VarPlace("p"), "a")
    assert p.field("a").node == ir.FieldRead(ir.Var("p"), "a")


def test_indexing_a_pure_expression_yields_a_pure_expression():
    m = Module()
    table = m.const("T", frozen(bytes_), b"\x01\x02")
    assert isinstance(table, Expr) and not hasattr(table, "place")
    assert table.at(u32(0)).node == ir.IndexRead(ir.ConstRef("T"), ir.Lit(U32, 0))


def test_enum_and_struct_values():
    m = Module()
    Phase = m.enum("Phase", ["Enter", "Left"])
    Pair = m.struct("Pair", [("a", u32), ("b", u32)])
    assert Phase.Enter.node == ir.EnumVal("Phase", "Enter")
    assert Phase.t == EnumType("Phase")
    assert Pair.of(a=u32(1), b=u32(2)).node == ir.StructVal(
        "Pair", (("a", ir.Lit(U32, 1)), ("b", ir.Lit(U32, 2)))
    )


def test_an_enum_reference_does_not_answer_for_dunder_names():
    m = Module()
    Phase = m.enum("Phase", ["Enter"])
    with pytest.raises(AttributeError):
        Phase.__deepcopy__


def test_type_constructors():
    assert vec(u32, 8).t == VecType(U32, 8)
    assert frozen(bytes_).t == FrozenType(bytes_.t)
    assert counter.t.name == "counter"


@pytest.mark.parametrize(
    "value, expected",
    [
        (b"\x01\x02", ir.BytesConst(b"\x01\x02")),
        ([1, 2], ir.VecConst((1, 2))),
        ("Enter", ir.EnumConst("Enter")),
        (7, 7),
        (True, True),
    ],
)
def test_constant_values_are_recognised_by_shape(value, expected):
    m = Module()
    m.const("C", u32, value)
    assert m.consts[0].value == expected


def test_a_constant_of_an_unknown_shape_is_refused():
    m = Module()
    with pytest.raises(TypeError, match="not a TIR constant value"):
        m.const("C", u32, 1.5)


def test_if_and_else_build_one_statement():
    m = Module()
    f = m.func("f", params=[("n", u32, "inout")])
    with f.if_(f["n"] > u32(0)):
        f.set(f["n"], u32(1))
    with f.else_():
        f.set(f["n"], u32(2))
    built = f.finish()
    assert len(built.body) == 1
    branch = built.body[0]
    assert isinstance(branch, ir.If)
    assert len(branch.then) == 1 and len(branch.otherwise) == 1


def test_else_has_to_follow_an_if():
    m = Module()
    f = m.func("f")
    with pytest.raises(ValueError, match="follow an if_"):
        with f.else_():
            pass


def test_an_unclosed_block_is_caught_when_the_function_is_finished():
    m = Module()
    f = m.func("f")
    f._blocks.append([])
    with pytest.raises(ValueError, match="unclosed block"):
        f.finish()


def test_a_switch_collects_its_arms_and_default():
    m = Module()
    Phase = m.enum("Phase", ["Enter", "Left"])
    f = m.func("f", params=[("p", Phase), ("n", u32, "inout")])
    with f.switch(f["p"]) as phase:
        with phase.case("Enter"):
            f.set(f["n"], u32(1))
        with phase.otherwise():
            f.set(f["n"], u32(2))
    built = f.finish()
    switch = built.body[0]
    assert isinstance(switch, ir.Switch)
    assert [arm.variant for arm in switch.arms] == ["Enter"]
    assert switch.default is not None


def test_a_while_loop_carries_its_variant():
    m = Module()
    f = m.func("f", params=[("i", counter, "inout")])
    i = f["i"]
    with f.while_(i > counter(0), i):
        f.set(i, i - counter(1))
    loop = f.finish().body[0]
    assert isinstance(loop, ir.While)
    assert loop.variant == ir.Var("i")


def test_a_call_marks_its_inout_arguments():
    m = Module()
    f = m.func("f", params=[("v", vec(u32, 4), "inout")])
    m.func("g", params=[("v", vec(u32, 4), "inout"), ("n", u32)])
    f.call("g", [inout(f["v"]), u32(1)])
    call = f.finish().body[0]
    assert isinstance(call, ir.Call)
    assert isinstance(call.args[0], ir.InoutArg)
    assert isinstance(call.args[1], ir.InArg)


def test_a_module_builds_a_program_whose_declarations_are_in_canonical_order():
    m = Module()
    m.enum("Zeta", ["A"])
    m.enum("Alpha", ["A"])
    m.func("second")
    m.func("first")
    program = m.build()
    assert [e.name for e in program.enums] == ["Alpha", "Zeta"]
    assert [f.name for f in program.funcs] == ["first", "second"]


def test_a_small_module_validates_end_to_end():
    m = Module()
    Pair = m.struct("Pair", [("a", u32), ("b", u32)])
    total = m.func("total", params=[("p", Pair)], ret=u32)
    total.ret(total["p"].field("a") + total["p"].field("b"))

    caller = m.func("caller", params=[("out", u32, "inout")])
    caller.let("p", Pair, Pair.of(a=u32(3), b=u32(4)))
    caller.call("total", [caller["p"]], dest=caller["out"])

    program = m.build()
    validate(program)
    assert program.func_map["caller"].params[0].type == U32
    assert program.struct_map["Pair"].fields[0].name == "a"
    assert StructType("Pair") == Pair.t
