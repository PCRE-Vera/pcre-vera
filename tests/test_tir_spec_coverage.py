"""The specification covers every construct the schema admits, checked mechanically.

That sentence is M2's definition of done in DESIGN.md section 9, and it is the
kind of claim that quietly stops being true the first time somebody adds a node
without opening the document. So: every node type in `ir` maps to a JSON tag
here, the map has to be exhaustive over the unions, and every tag has to appear
in TIR-SPEC.md.

The validator rules get the same treatment, though the part that matters —
that each one really is provoked by some test — is watched rather than read,
in `conftest.py`. What is left here is the document's own consistency: the
numbers run without gaps, and no rule is stated in the list and nowhere else.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import get_args

import pytest

from pcrevera.tir import ir, types

SPEC = (Path(__file__).parents[1] / "TIR-SPEC.md").read_text()
SERIALIZE_TESTS = (Path(__file__).parent / "test_tir_serialize.py").read_text()

TYPE_TAGS = {
    "Prim": ("bool", "u8", "i32", "u32", "counter", "bytes"),
    "EnumType": ("enum",),
    "StructType": ("struct",),
    "VecType": ("vec",),
    "FrozenType": ("frozen",),
}

CONST_TAGS = {
    "EnumConst": ("variant",),
    "StructConst": ("fields",),
    "BytesConst": ("bytes",),
    "VecConst": ("elems",),
}

EXPR_TAGS = {
    "Lit": ("bool", "u8", "i32", "u32", "counter"),
    "Var": ("var",),
    "ConstRef": ("constref",),
    "FieldRead": ("field",),
    "IndexRead": ("index",),
    "Len": ("len",),
    "Cap": ("cap",),
    "Unary": ("un",),
    "Binary": ("bin",),
    "Compare": ("cmp",),
    "DivRem": ("div", "rem"),
    "Shift": ("shift",),
    "Cast": ("cast",),
    "Logical": ("and", "or"),
    "EnumVal": ("enumval",),
    "StructVal": ("structval",),
}

PLACE_TAGS = {"VarPlace": ("var",), "FieldPlace": ("field",), "IndexPlace": ("index",)}

STMT_TAGS = {
    "Let": ("let",),
    "Assign": ("assign",),
    "Take": ("take",),
    "Swap": ("swap",),
    "Copy": ("copy",),
    "Freeze": ("freeze",),
    "Push": ("push",),
    "Pop": ("pop",),
    "Truncate": ("truncate",),
    "Reserve": ("reserve",),
    "If": ("if",),
    "While": ("while",),
    "Switch": ("switch",),
    "Break": ("break",),
    "Continue": ("continue",),
    "Return": ("return",),
    "Call": ("call",),
}

ARG_TAGS = {"InArg": ("in",), "InoutArg": ("inout",)}


def named(union) -> set[str]:
    """The class names in a union, leaving out the plain Python types."""
    return {arg.__name__ for arg in get_args(union) if arg.__module__ in (ir.__name__, types.__name__)}


@pytest.mark.parametrize(
    "union, tags",
    [
        (types.Type, TYPE_TAGS),
        (ir.ConstValue, CONST_TAGS),
        (ir.Expr, EXPR_TAGS),
        (ir.Place, PLACE_TAGS),
        (ir.Stmt, STMT_TAGS),
        (ir.Arg, ARG_TAGS),
    ],
    ids=["types", "constants", "expressions", "places", "statements", "arguments"],
)
def test_every_node_of_every_union_has_a_tag(union, tags):
    assert named(union) == set(tags)


@pytest.mark.parametrize(
    "tag",
    sorted(
        {
            tag
            for table in (TYPE_TAGS, CONST_TAGS, EXPR_TAGS, PLACE_TAGS, STMT_TAGS, ARG_TAGS)
            for tags in table.values()
            for tag in tags
        }
    ),
)
def test_the_specification_names_every_tag(tag):
    assert f'"{tag}"' in SPEC, f"TIR-SPEC.md never mentions the {tag!r} form"


@pytest.mark.parametrize("op", sorted({*ir.UNARY_OPS, *ir.BINARY_OPS, *ir.COMPARE_OPS, *ir.SHIFT_OPS}))
def test_the_specification_names_every_operator(op):
    assert f"| {op}" in SPEC or f'"{op}"' in SPEC, f"TIR-SPEC.md never mentions the {op!r} operator"


def test_the_reserved_set_is_the_one_the_specification_lists():
    """Two copies of a list is one copy too many unless something compares them."""
    block = re.search(r"\*\*Reserved names\.\*\*.*?\n```\n(.*?)```", SPEC, re.S)
    assert block, "TIR-SPEC.md section 2 no longer lists the reserved words"
    assert set(block.group(1).split()) == set(ir.RESERVED)


def rules_in_the_specification() -> list[str]:
    listed = re.findall(r"^(V-\d{3})  ", SPEC, flags=re.MULTILINE)
    assert listed, "TIR-SPEC.md section 15 lists no rules at all"
    return listed


def test_the_rule_numbers_are_contiguous_from_one():
    listed = rules_in_the_specification()
    assert listed == [f"V-{n:03d}" for n in range(1, len(listed) + 1)]


@pytest.mark.parametrize("rule", rules_in_the_specification())
def test_every_rule_is_referenced_where_it_applies(rule):
    """A rule stated only in the list is a rule nothing in the document explains."""
    assert SPEC.count(rule) >= 2, f"{rule} appears only in the section 15 list"


def test_the_reader_rule_has_its_own_test():
    """V-001 is the reader's, and a syntax error carries no rule number to watch for.

    Every other rule is checked by watching for it: `conftest.py` records each
    ValidationError the session raises and fails the run over one nobody
    provoked. Grepping a test file for a rule number, which is what this used
    to do, proves only that somebody typed it.
    """
    assert "V-001" in SERIALIZE_TESTS
