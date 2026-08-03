"""The engine as a TIR artifact.

The engine is a program in the language TIR-SPEC.md defines, so everything that
document promises about a program has to hold for it: it validates, it survives
the canonical round trip, and it says the same thing the tables in `spec.py`
say, since the backends will read the artifact and never this package.
"""

from __future__ import annotations

import pytest

from pcrevera.engine import program, spec
from pcrevera.tir import dumps, ir, is_canonical, loads, validate


@pytest.fixture(scope="module")
def engine_program() -> ir.Program:
    return program()


def test_the_engine_validates(engine_program: ir.Program) -> None:
    validate(engine_program)


def test_the_engine_round_trips_canonically(engine_program: ir.Program) -> None:
    text = dumps(engine_program)
    decoded = loads(text)
    assert decoded == engine_program
    assert is_canonical(text, decoded)


def test_the_engine_has_the_three_entry_points(engine_program: ir.Program) -> None:
    for name in ("compile", "match", "parse", "generate"):
        assert name in engine_program.func_map


def test_compilation_returns_nothing_and_writes_through_its_argument(
    engine_program: ir.Program,
) -> None:
    """A linear result travels by inout; that is the whole of TIR-SPEC.md section 9."""
    compile_fn = engine_program.func_map["compile"]
    assert compile_fn.ret is None
    modes = {p.name: p.mode for p in compile_fn.params}
    assert modes["out"] == "inout"
    assert modes["pat"] == "in"


def test_matching_takes_the_compiled_pattern_by_value(engine_program: ir.Program) -> None:
    """`Re` is copyable, so one compiled pattern serves any number of calls."""
    match_fn = engine_program.func_map["match"]
    types = engine_program.types
    for param in match_fn.params:
        if param.name == "re":
            assert param.mode == "in"
            assert types.is_copyable(param.type)
            return
    raise AssertionError("match has no re parameter")


def test_the_constant_tables_are_the_ones_spec_computes(engine_program: ir.Program) -> None:
    expected = {
        "SETS": spec.set_table(),
        "POSIX": spec.posix_table(),
        "BITS": spec.bit_table(),
        "LOWER": spec.lower_table(),
        "FLIP": spec.flip_table(),
        "CTYPE": spec.ctype_table(),
    }
    for name, data in expected.items():
        const = engine_program.const_map[name]
        assert isinstance(const.value, ir.BytesConst)
        assert const.value.data == data


def test_every_class_set_is_thirty_two_bytes() -> None:
    table = spec.set_table()
    assert len(table) == 32 * len(spec.SET_ORDER)


def test_the_posix_table_names_only_known_sets() -> None:
    table = spec.posix_table()
    at = 0
    seen = []
    while at < len(table):
        length = table[at]
        name = table[at + 1 : at + 1 + length].decode("ascii")
        index = table[at + 1 + length]
        assert spec.SET_ORDER[index] in spec.SETS
        seen.append(name)
        at += 2 + length
    assert tuple(seen) == spec.POSIX_NAMES


def test_the_case_tables_only_touch_ascii_letters() -> None:
    lower, flip = spec.lower_table(), spec.flip_table()
    for byte in range(256):
        if 0x41 <= byte <= 0x5A:
            assert lower[byte] == byte + 0x20 and flip[byte] == byte + 0x20
        elif 0x61 <= byte <= 0x7A:
            assert lower[byte] == byte and flip[byte] == byte - 0x20
        else:
            assert lower[byte] == byte and flip[byte] == byte
