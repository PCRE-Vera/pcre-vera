"""The public analysis accessors, written in TIR.

DESIGN.md section 2.4 promises four questions a caller can ask a compiled
pattern before ever running it: its complexity class, and its worst-case cost,
backtrack stack and scratch memory at a given subject length. This is where
those questions are answered, and it is deliberately the only place: the Go and
JavaScript wrappers hand the compiled pattern straight to these functions, so
every language validates the same arguments, reads the same certificate slot,
and refuses the same requests, by construction rather than by review.

What the answers come from is the certificate compilation stored — the one the
checker accepted, never a fresh run of the analyzer, and never the certificate
itself, which no accessor exposes. A pattern that carries none gets the
explicit ExceedsBudget of DESIGN.md section 2.4, because "the analyzer found no
bound of a shape its arithmetic can write down" and "the bound saturated" are
the same news to a caller who has to pick a limit: there is no number here
anyone can budget with.

The configuration argument is the public matchConfig, not the internal `Cfg`
domain. Today the only legal value is the default; a memoization request is
BadInput until M9 activates it, and an ordinal nobody defined is BadInput
forever. The complexity class alone takes no configuration, because the class
is fixed at compilation: memoization is only legal on Pike-eligible patterns
and changes the constants, never the class.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, lnot, u32
from . import spec
from .layout import Layout


def build(L: Layout) -> None:
    _selection(L)
    _bound(L)
    _class(L)
    for name, kind in (
        ("re_cost", "BkCost"),
        ("re_stack", "BkStack"),
        ("re_mem", "BkMem"),
    ):
        _projection(L, name, kind)


def _refusal(L: Layout, status: int):
    return L.Answer.of(status=u32(status), value=counter(0))


def _bound(L: Layout) -> None:
    """One certified bound, as the public contract states it.

    The order of the refusals is part of that contract: a request that is not
    well formed — a configuration the pattern cannot be asked about, a length
    no subject can have — is BadInput before the certificate slot is ever
    looked at, so the same bad request gets the same answer on every pattern.
    """
    f = L.func(
        "re_bound",
        params=[("re", L.Re), ("kind", L.Bk), ("mcfg", u32), ("n", counter)],
        ret=L.Answer,
    )
    with f.if_(f["mcfg"] != u32(spec.MC_DEFAULT)):
        f.ret(_refusal(L, spec.BAD_INPUT))
    with f.if_(f["n"] > counter(spec.MAX_LENGTH)):
        f.ret(_refusal(L, spec.BAD_INPUT))
    picked = f.let("picked", L.Cert)
    ok = f.let("ok", boolean, boolean(False))
    f.call("re_pick", [f["re"], inout(picked)], dest=ok)
    with f.if_(lnot(ok)):
        f.ret(_refusal(L, spec.EXCEEDS_BUDGET))
    out = f.let("out", L.Bound)
    f.call("cert_bound", [picked, f["kind"], f["n"]], dest=out)
    with f.if_(lnot(out.field("ok"))):
        f.ret(_refusal(L, spec.EXCEEDS_BUDGET))
    f.ret(L.Answer.of(status=u32(spec.OK), value=out.field("value")))


def _selection(L: Layout) -> None:
    """The certificate of the path that will actually run.

    Matcher selection is fixed at compilation, and the accessors answer for
    the selected path (DESIGN.md section 2.4): the Pike certificate on a
    Pike-eligible pattern, the backtracking one otherwise. False means the
    selected path carries none, which is the caller's ExceedsBudget.
    """
    f = L.func(
        "re_pick",
        params=[("re", L.Re), ("picked", L.Cert, "inout")],
        ret=boolean,
    )
    with f.if_(f["re"].field("pike")):
        with f.if_(lnot(f["re"].field("haspikecert"))):
            f.ret(boolean(False))
        f.set(f["picked"], f["re"].field("pikecert"))
        f.ret(boolean(True))
    with f.if_(lnot(f["re"].field("hascert"))):
        f.ret(boolean(False))
    f.set(f["picked"], f["re"].field("cert"))
    f.ret(boolean(True))


def _class(L: Layout) -> None:
    f = L.func("re_class", params=[("re", L.Re)], ret=L.Answer)
    picked = f.let("picked", L.Cert)
    ok = f.let("ok", boolean, boolean(False))
    f.call("re_pick", [f["re"], inout(picked)], dest=ok)
    with f.if_(lnot(ok)):
        f.ret(_refusal(L, spec.EXCEEDS_BUDGET))
    value = f.let("value", counter, counter(spec.CLASS_NOT_PROVEN_LINEAR))
    # The switch covers its enum, so it needs no default (TIR-SPEC.md rule
    # V-032); the flag is for a caller of the generated module who hands over
    # a value that names no variant, who has to be told this is not a class
    # rather than handed whatever the initialization happened to say.
    known = f.let("known", boolean, boolean(False))
    with f.switch(picked.field("complexity")) as arm:
        with arm.case("CcNotProvenLinear"):
            f.set(known, boolean(True))
        with arm.case("CcLinear"):
            f.set(value, counter(spec.CLASS_LINEAR))
            f.set(known, boolean(True))
    with f.if_(lnot(known)):
        f.ret(_refusal(L, spec.EXCEEDS_BUDGET))
    f.ret(L.Answer.of(status=u32(spec.OK), value=value))


def _projection(L: Layout, name: str, kind: str) -> None:
    """One public accessor: `re_bound` with its kind filled in.

    Three thin entry points rather than one taking a `Bk`, so the hand-written
    wrappers never spell an internal enum ordinal — the kind is part of the
    question a caller asked, not an argument they supply.
    """
    f = L.func(
        name,
        params=[("re", L.Re), ("mcfg", u32), ("n", counter)],
        ret=L.Answer,
    )
    out = f.let("out", L.Answer)
    f.call(
        "re_bound",
        [f["re"], getattr(L.Bk, kind), f["mcfg"], f["n"]],
        dest=out,
    )
    f.ret(out)
