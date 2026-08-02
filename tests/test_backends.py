"""The generator: what it emits, and that the committed files are still it.

The Go and JavaScript are committed so that the diff is reviewable and the
libraries are usable without running the generator (DESIGN.md section 11). That
only means anything if something checks it, which is what the first test here
does; the rest are about the printers themselves.
"""

from __future__ import annotations

import re

import pytest

from pcretruste import leanexport
from pcretruste.backends import GO_PATH, JS_PATH, PROBE_GO_PATH, PROBE_JS_PATH
from pcretruste.backends import generate, go, js
from pcretruste.dsl import Module, bytes_, counter, frozen, inout, u8, u32, vec
from pcretruste.engine.program import program
from pcretruste.tir import serialize
from pcretruste.tir.types import CAP

import toy


@pytest.fixture(scope="module")
def generated() -> tuple[str, dict]:
    """The generator's output, keyed by path rather than by position."""
    sha256, outputs = generate()
    return sha256, {output.path: output for output in outputs}


def test_the_committed_files_are_what_the_generator_produces(generated) -> None:
    _, outputs = generated
    stale = [str(path) for path, output in outputs.items() if not output.matches()]
    assert not stale, "run `make generate`; these have drifted:\n" + "\n".join(stale)


def test_the_artifact_is_canonical_and_round_trips(generated) -> None:
    sha256, outputs = generated
    text = outputs[leanexport.ARTIFACT_PATH].text
    assert text.endswith("\n") and not text.endswith("\n\n")
    assert text.isascii()
    decoded = serialize.loads(text)
    assert decoded == program()
    assert serialize.is_canonical(text, decoded)
    assert leanexport.digest(text) == sha256


def _stamped(text: str) -> str:
    """The hash a generated file says it came from, read out of its header."""
    stamped = re.search(r"^//   ([0-9a-f]{64})$", text, re.MULTILINE)
    assert stamped is not None, "no artifact hash in the header"
    return stamped.group(1)


def test_every_generated_file_carries_the_artifact_hash(generated) -> None:
    """A header comment and a constant, so CI can refuse files that disagree.

    The probe is a different program, so it carries a different hash — which
    is the point of stamping the file rather than the release.
    """
    sha256, outputs = generated
    engine_go, engine_js = outputs[GO_PATH].text, outputs[JS_PATH].text
    probe_go, probe_js = outputs[PROBE_GO_PATH].text, outputs[PROBE_JS_PATH].text

    for text in (engine_go, engine_js):
        assert _stamped(text) == sha256
    probe_sha = _stamped(probe_go)
    assert _stamped(probe_js) == probe_sha
    assert probe_sha != sha256

    assert f'const ArtifactSHA256 = "{sha256}"' in engine_go
    assert f'export const artifactSha256 = "{sha256}";' in engine_js
    assert f'const ArtifactSHA256 = "{probe_sha}"' in probe_go
    assert f'export const artifactSha256 = "{probe_sha}";' in probe_js


def test_printing_is_a_function_of_the_program() -> None:
    built = program()
    assert go.render(built, "0" * 64) == go.render(built, "0" * 64)
    assert js.render(built, "0" * 64) == js.render(built, "0" * 64)


def test_every_function_reaches_both_backends() -> None:
    built = program()
    go_text = go.render(built, "0" * 64)
    js_text = js.render(built, "0" * 64)
    for func in built.funcs:
        assert f"func {func.name}(" in go_text
        assert f"func Tir_{func.name}(" in go_text
        assert f"export function {func.name}(" in js_text


def test_a_name_the_go_facade_owns_is_refused() -> None:
    m = Module()
    m.func("Tir_thing", ret=u32).ret(u32(0))
    built = m.build()
    with pytest.raises(go.GoError, match="Tir_"):
        go.render(built, "0" * 64)


def test_a_name_that_would_shadow_a_host_global_is_refused() -> None:
    m = Module()
    m.func("Math", ret=u32).ret(u32(0))
    built = m.build()
    with pytest.raises(js.JsError, match="Math"):
        js.render(built, "0" * 64)
    # Go has no such trouble: its own reserved words are already rule V-043's.
    assert "func Math(" in go.render(built, "0" * 64)


def test_the_toy_program_prints_too() -> None:
    """A second program, so the printers are not tuned to one shape."""
    built = toy.build()
    go_text = go.render(built, "0" * 64, package="toy", origin="the toy program")
    js_text = js.render(built, "0" * 64, origin="the toy program")
    assert "package toy" in go_text
    assert "switch " in go_text
    for func in built.funcs:
        assert f"export function {func.name}(" in js_text


def test_go_guards_arithmetic_on_two_literals() -> None:
    """Go refuses `uint32(4e9) + uint32(4e9)`, and TIR says it wraps.

    A constant expression has to be representable in Go, so the printer sends
    one operand through the identity `tir_k` and the whole thing becomes
    ordinary runtime arithmetic.
    """
    m = Module()
    m.func("sum", ret=u32).ret(u32(4_000_000_000) + u32(4_000_000_000))
    text = go.render(m.build(), "0" * 64)
    assert "return (tir_k(uint32(4000000000)) + uint32(4000000000))" in text
    # JavaScript has no such rule, so nothing is inserted there.
    assert "tir_k" not in js.render(m.build(), "0" * 64)


def test_go_guards_arithmetic_on_a_named_constant() -> None:
    """A scalar constant is emitted with `const`, so a use of one folds too.

    Whether a constant is a Go constant is one decision, asked by the code
    that emits it and by the code that guards a use of it; a sequence goes out
    as a package variable and needs no guard.
    """
    m = Module()
    scalar = m.const("BIG", u32, 4_000_000_000)
    table = m.const("TABLE", frozen(bytes_), b"\x01\x02")
    m.func("sum", ret=u32).ret(scalar + u32(4_000_000_000))
    m.func("peek", ret=u8).ret(table.at(u32(0)))
    text = go.render(m.build(), "0" * 64)
    assert "const BIG uint32 = 4000000000" in text
    assert "var TABLE = []byte{" in text
    assert "return (tir_k(BIG) + uint32(4000000000))" in text


def _argument_order_program():
    """A call whose first argument traps before the second one is resolved.

    Section 13 resolves arguments left to right, so the `in` argument's index
    check has to run before the `inout` place's. Both printers would otherwise
    leave the `in` one to be evaluated inside the call, which is afterwards.
    """
    m = Module()
    m.func("sink", params=[("seen", u32), ("slot", u32, "inout")])
    f = m.func("caller", params=[("i", u32), ("j", u32)])
    left = f.let("left", vec(u32, 8))
    right = f.let("right", vec(u32, 8))
    f.push(left, u32(1))
    f.push(right, u32(2))
    f.call("sink", [left.at(f["i"]), inout(right.at(f["j"]))])
    return m.build()


def test_an_in_argument_is_resolved_before_a_later_inout_one() -> None:
    built = _argument_order_program()

    go_text = go.render(built, "0" * 64)
    body = go_text.split("func caller(")[1].split("\nfunc ")[0]
    hoisted = body.index("left[i]")
    checked = body.index("uint32(len(right))")
    assert hoisted < checked, body

    js_text = js.render(built, "0" * 64)
    body = js_text.split("export function caller(")[1].split("\nexport function ")[0]
    assert body.index("tir_at(left, i)") < body.index("tir_bound(right.n"), body


def test_both_backends_saturate_at_the_same_number() -> None:
    """The counter cap is a cross-language number, so it is pinned as one.

    That the arithmetic around it is the pre-checked form of section 6.7 is
    the probe's business: `counter-add` and `counter-mul` ask about it at the
    cap in all three implementations, where grepping a string constant here
    would only pin a spelling.
    """
    assert f"tir_CAP uint64 = {CAP}" in go.SUPPORT
    assert f"const tir_CAP = {CAP};" in js.SUPPORT


def test_javascript_multiplies_through_imul() -> None:
    """The one place a naive lowering is silently wrong rather than slow."""
    text = js.render(program(), "0" * 64)
    assert "Math.imul(" in text
    # Nothing below the helpers multiplies with a bare star: a 32-bit product
    # goes through Math.imul and a counter product through tir_cmul.
    body = text.split("// enum ", 1)[1]
    assert " * " not in body


def test_javascript_clones_a_struct_read_but_not_a_linear_one() -> None:
    text = js.render(program(), "0" * 64)
    assert ".tir_clone()" in text
    # Work is linear, so it has no clone method and never needs one.
    assert "w.v.tir_clone()" not in text
    assert "tir_clone() {" in text


def test_a_counter_literal_at_the_cap_survives_both_printers() -> None:
    m = Module()
    f = m.func("cap", ret=counter)
    f.ret(counter(CAP))
    built = m.build()
    assert f"uint64({CAP})" in go.render(built, "0" * 64)
    assert f"return {CAP};" in js.render(built, "0" * 64)
