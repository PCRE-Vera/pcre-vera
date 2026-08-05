"""Assembling the engine into one TIR program.

`compile` is the only entry point a caller needs for compilation: it parses,
generates code, freezes the result into the copyable `Re` value that `match`
then takes by value, and prices what came out. Freezing is what lets one
compiled pattern serve any number of match calls while every mutable scratch
value stays linear.

Pricing is last because it is about the finished program, and it is two steps
rather than one: the analyzer of DESIGN.md section 5 searches for a bound
certificate, and the checker decides whether the compiled pattern gets to carry
it.
"""

from __future__ import annotations

import functools

from ..dsl import boolean, inout, u32
from ..tir import ir
from . import (
    accessors,
    analyzer,
    bounds,
    certificate,
    compiler,
    context,
    parser,
    pike,
    spec,
    vm,
)
from .layout import Layout


def _entry(L: Layout) -> None:
    f = L.func(
        "compile",
        params=[
            ("pat", L.frozen_bytes),
            ("popts", u32),
            ("nltype", u32),
            ("bsr", u32),
            ("out", L.Out, "inout"),
        ],
    )
    out = f["out"]
    f.set(out.field("err"), u32(0))
    f.set(out.field("erroff"), u32(0))
    n = parser.tmp(f, u32, f["pat"].len())
    with f.if_(n > u32(spec.MAX_PATTERN)):
        f.set(out.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()

    w = f.let("w", L.Work)
    f.call("parse", [f["pat"], f["popts"], f["nltype"], inout(w)])
    with f.if_(w.field("err") != u32(0)):
        f.set(out.field("err"), w.field("err"))
        f.set(out.field("erroff"), w.field("erroff"))
        f.ret()

    endanchored = parser.tmp(
        f, boolean, (f["popts"] & u32(spec.ENDANCHORED)) != u32(0)
    )
    f.call("generate", [inout(w), endanchored])
    with f.if_(w.field("err") != u32(0)):
        f.set(out.field("err"), w.field("err"))
        f.set(out.field("erroff"), w.field("erroff"))
        f.ret()

    # Captures take the low registers, in ovector order; each counted
    # repetition takes two above them, a count and the position its current
    # iteration started at.
    nregs = parser.tmp(
        f,
        u32,
        (w.field("ncap") + u32(1)) * u32(2) + w.field("nrep") * u32(2),
    )
    with f.if_(nregs > u32(spec.MAX_REGS)):
        f.set(out.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()

    f.set(out.field("re").field("ncap"), w.field("ncap"))
    f.set(out.field("re").field("nname"), w.field("nname"))
    f.set(out.field("re").field("nregs"), nregs)
    f.set(out.field("re").field("opts"), f["popts"])
    f.set(out.field("re").field("nltype"), f["nltype"])
    f.set(out.field("re").field("bsr"), f["bsr"])
    f.set(out.field("re").field("hascrlf"), w.field("hascrlf"))
    f.set(out.field("re").field("crfirst"), w.field("crfirst"))
    # What the compiler decided about the quantifier lowering, carried out of
    # the work area so that a report can read it rather than guess at it.
    f.set(out.field("re").field("lowdec"), w.field("lowdec"))
    f.set(out.field("re").field("blockers"), w.field("blockers"))
    f.set(out.field("re").field("lowfits"), w.field("lowfits"))
    f.freeze(out.field("re").field("code"), w.field("code"))
    f.freeze(out.field("re").field("classes"), w.field("classes"))
    f.freeze(out.field("re").field("reps"), w.field("reps"))
    f.freeze(out.field("re").field("regions"), w.field("regions"))
    f.freeze(out.field("re").field("names"), w.field("names"))
    f.freeze(out.field("re").field("nameents"), w.field("nameents"))

    # Whether the Pike VM may run this program, fixed here like everything
    # else about the execution path (DESIGN.md section 4.3). Decided off the
    # frozen bytecode, so the answer is about the program the matchers will
    # actually see.
    eligible = parser.tmp(f, boolean, boolean(False))
    f.call("pike_ok", [out.field("re")], dest=eligible)
    f.set(out.field("re").field("pike"), eligible)

    # And the resource analysis, which is the last phase because it prices the
    # program that came out of everything above it. It writes the last two
    # fields of `re` unconditionally, so a caller who compiled one pattern into
    # this result and then another is never handed the first pattern's
    # certificate for the second pattern's bytecode.
    #
    # A refusal here is not a pattern this release declines. It is the two
    # halves of BOUNDS.md disagreeing about one program, which no pattern can
    # cause and only a bug of ours can.
    cand = f.let("cand", L.Cert)
    has = parser.tmp(f, boolean, boolean(False))
    pcand = f.let("pcand", L.Cert)
    haspike = parser.tmp(f, boolean, boolean(False))
    verdict = parser.tmp(f, L.Cr, L.Cr.CrOk)
    f.call(
        "cert_install",
        [out.field("re"), inout(cand), inout(has), inout(pcand), inout(haspike)],
        dest=verdict,
    )
    with f.if_(verdict != L.Cr.CrOk):
        f.set(out.field("err"), u32(spec.E_INTERNAL))
        f.ret()
    f.set(out.field("re").field("cert"), cand)
    f.set(out.field("re").field("hascert"), has)
    f.set(out.field("re").field("pikecert"), pcand)
    f.set(out.field("re").field("haspikecert"), haspike)


def build() -> ir.Program:
    """The whole engine, as one TIR program."""
    L = Layout()
    parser.build(L)
    compiler.build(L)
    vm.build(L)
    pike.build(L)
    bounds.build(L)
    certificate.build(L)
    analyzer.build(L)
    accessors.build(L)
    context.build(L)
    _entry(L)
    return L.build()


@functools.lru_cache(maxsize=1)
def program() -> ir.Program:
    """The engine, built once per process and validated."""
    from ..tir import validate

    built = build()
    validate(built)
    return built
