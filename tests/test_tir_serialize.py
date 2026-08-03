"""The canonical JSON encoding of TIR-SPEC.md section 14, both directions.

The artifact's SHA-256 is the identity that ties the proofs, the backends and
CI together, so these tests are about bytes, not about structure.
"""

from __future__ import annotations

import json

import pytest

from pcrevera.tir import dumps, ir, is_canonical, loads
from pcrevera.tir.serialize import TirSyntaxError, _render_string
from pcrevera.tir.types import U32, EnumDecl, Field, StructDecl

EMPTY = """{
  "consts": [],
  "enums": [],
  "funcs": [],
  "structs": [],
  "tir": 1
}
"""


def test_an_empty_program_is_this_exact_text():
    assert dumps(ir.Program()) == EMPTY


def test_the_file_ends_in_exactly_one_newline():
    text = dumps(ir.Program())
    assert text.endswith("}\n") and not text.endswith("\n\n")


def test_object_keys_are_sorted_and_indentation_is_two_spaces():
    program = ir.Program(
        funcs=(
            ir.Func(
                name="f",
                params=(ir.Param("n", U32, "in"),),
                ret=U32,
                body=(ir.Return(ir.Var("n")),),
            ),
        )
    )
    text = dumps(program)
    assert '\n  "funcs": [\n' in text
    assert '      "body": [\n        {\n          "return": {\n' in text
    # name, params, ret, body would be the reading order; sorted is the rule.
    keys = [line.split('"')[1] for line in text.splitlines() if line.startswith("      \"")]
    assert keys == sorted(keys)


def test_declarations_are_sorted_by_name_and_variants_are_not():
    program = ir.Program(
        enums=(EnumDecl("Zeta", ("Late", "Early")), EnumDecl("Alpha", ("One",))),
        structs=(StructDecl("Beta", (Field("z", U32), Field("a", U32))),),
    )
    document = json.loads(dumps(program))
    assert [e["name"] for e in document["enums"]] == ["Alpha", "Zeta"]
    assert document["enums"][1]["variants"] == ["Late", "Early"]
    assert [f["name"] for f in document["structs"][0]["fields"]] == ["z", "a"]


def test_a_program_round_trips_through_its_own_text():
    program = ir.Program(
        enums=(EnumDecl("Phase", ("Enter", "Left")),),
        structs=(StructDecl("Frame", (Field("pc", U32),)),),
        consts=(ir.Const("N", U32, 7),),
        funcs=(ir.Func("f", (), None, (ir.Return(None),)),),
    )
    text = dumps(program)
    assert loads(text) == program
    assert dumps(loads(text)) == text


def test_a_reader_takes_any_whitespace_and_canonicity_is_asked_separately():
    """Section 14: parsing does not care about layout; `is_canonical` is the question that does."""
    program = ir.Program(consts=(ir.Const("N", U32, 7),))
    compact = json.dumps(json.loads(dumps(program)), separators=(",", ":"))
    assert loads(compact) == program
    assert not is_canonical(compact, program)
    assert is_canonical(dumps(program), program)


def test_member_order_in_the_text_does_not_reach_the_program():
    reordered = """{"funcs": [], "structs": [], "enums": [], "consts": [], "tir": 1}"""
    assert loads(reordered) == ir.Program()


@pytest.mark.parametrize(
    "text, escaped",
    [
        ("plain", '"plain"'),
        ('a"b', '"a\\"b"'),
        ("a\\b", '"a\\\\b"'),
        ("\n\t\r\b\f", '"\\n\\t\\r\\b\\f"'),
        ("\x00\x1f", '"\\u0000\\u001f"'),
        ("café", '"caf\\u00e9"'),
        ("\U0001f600", '"\\ud83d\\ude00"'),
    ],
)
def test_strings_are_escaped_to_pure_ascii(text, escaped):
    # No program can hold a string that is not an identifier or hex today, but
    # the rule is normative for the Lean printer, so it is pinned here.
    assert _render_string(text) == escaped


def parse(document: object) -> ir.Program:
    return loads(json.dumps(document))


def base(**overrides: object) -> dict:
    document = {"tir": 1, "enums": [], "structs": [], "consts": [], "funcs": []}
    document.update(overrides)
    return document


def test_the_schema_version_is_checked_on_the_way_in():
    """V-001, which lives here because a decoded program has no version left."""
    with pytest.raises(TirSyntaxError, match="schema"):
        parse(base(tir=2))


@pytest.mark.parametrize("version", [True, "1"])
def test_a_schema_version_that_merely_equals_one_is_not_one(version):
    with pytest.raises(TirSyntaxError, match="schema"):
        parse(base(tir=version))


def test_text_nested_past_the_parser_is_a_syntax_error():
    """No program is anywhere near this deep — V-044 caps nesting at 64.

    The point is only that text nobody could have produced from a program still
    leaves through the door marked "does not decode", rather than as whatever
    the JSON parser raises when its own stack runs out.
    """
    with pytest.raises(TirSyntaxError):
        loads("[" * 20_000 + "]" * 20_000)


def test_a_missing_top_level_member_is_an_error():
    document = base()
    del document["structs"]
    with pytest.raises(TirSyntaxError, match="missing"):
        parse(document)


def test_a_top_level_member_nothing_reads_is_an_error():
    with pytest.raises(TirSyntaxError, match="nothing reads"):
        parse(base(engine="please"))


def test_duplicate_keys_are_rejected():
    with pytest.raises(TirSyntaxError, match="duplicate key"):
        loads('{"tir": 1, "tir": 1, "enums": [], "structs": [], "consts": [], "funcs": []}')


def test_floats_are_rejected():
    with pytest.raises(TirSyntaxError, match="no floats"):
        loads('{"tir": 1.0, "enums": [], "structs": [], "consts": [], "funcs": []}')


def test_the_json_constants_javascript_allows_are_rejected():
    with pytest.raises(TirSyntaxError, match="NaN"):
        loads('{"tir": NaN, "enums": [], "structs": [], "consts": [], "funcs": []}')


def test_malformed_json_is_a_tir_error_rather_than_a_json_one():
    with pytest.raises(TirSyntaxError):
        loads("{")


def test_a_name_that_is_not_an_identifier_is_rejected():
    with pytest.raises(TirSyntaxError, match="identifier"):
        parse(base(enums=[{"name": "not a name", "variants": ["A"]}]))


def test_a_name_longer_than_the_limit_is_rejected():
    with pytest.raises(TirSyntaxError, match="identifier"):
        parse(base(enums=[{"name": "a" * 65, "variants": ["A"]}]))


def test_an_unknown_type_is_rejected():
    with pytest.raises(TirSyntaxError, match="unknown type"):
        parse(base(consts=[{"name": "N", "type": "u64", "value": 1}]))


def test_an_unknown_type_form_is_rejected():
    with pytest.raises(TirSyntaxError, match="unknown type form"):
        parse(base(consts=[{"name": "N", "type": {"pointer": "u8"}, "value": 1}]))


@pytest.mark.parametrize("payload", ["0", "0A", "zz", "0x01"])
def test_a_bytes_payload_is_even_length_lowercase_hex(payload):
    document = base(
        consts=[{"name": "B", "type": {"frozen": "bytes"}, "value": {"bytes": payload}}]
    )
    with pytest.raises(TirSyntaxError, match="hex"):
        parse(document)


def test_an_unknown_expression_form_is_rejected():
    document = base(
        funcs=[
            {
                "name": "f",
                "params": [],
                "ret": "u32",
                "body": [{"return": {"value": {"sqrt": {"arg": {"u32": 4}}}}}],
            }
        ]
    )
    with pytest.raises(TirSyntaxError, match="unknown expression form"):
        parse(document)


def test_an_unknown_operator_is_rejected():
    document = base(
        funcs=[
            {
                "name": "f",
                "params": [],
                "ret": "u32",
                "body": [
                    {
                        "return": {
                            "value": {
                                "bin": {"op": "pow", "left": {"u32": 2}, "right": {"u32": 3}}
                            }
                        }
                    }
                ],
            }
        ]
    )
    with pytest.raises(TirSyntaxError, match="unknown operator"):
        parse(document)


def test_a_constant_reference_cannot_stand_where_a_place_belongs():
    document = base(
        funcs=[
            {
                "name": "f",
                "params": [],
                "ret": None,
                "body": [{"assign": {"place": {"constref": "N"}, "value": {"u32": 1}}}],
            }
        ]
    )
    with pytest.raises(TirSyntaxError, match="a place is"):
        parse(document)


def test_a_parameter_mode_is_one_of_two_words():
    document = base(
        funcs=[
            {
                "name": "f",
                "params": [{"name": "n", "type": "u32", "mode": "out"}],
                "ret": None,
                "body": [],
            }
        ]
    )
    with pytest.raises(TirSyntaxError, match="'in' or 'inout'"):
        parse(document)


def test_a_call_argument_carries_its_mode():
    document = base(
        funcs=[
            {
                "name": "f",
                "params": [],
                "ret": None,
                "body": [{"call": {"fn": "g", "args": [{"byref": {"var": "x"}}], "dest": None}}],
            }
        ]
    )
    with pytest.raises(TirSyntaxError, match="'in' or 'inout'"):
        parse(document)
