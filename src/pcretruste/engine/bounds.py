"""The arithmetic a bound is written in, and what one instruction costs.

BOUNDS.md sections 2 and 3, which is the part of the resource analysis the two
halves of DESIGN.md section 5 are meant to have in common. An analyzer searches
for a bound certificate and a small checker decides whether to believe it, and
the two are kept apart so that a mistake in the search cannot become a mistake
in the verification. The cost model is deliberately not kept apart: section 5
asks for one model shared by the analyzer, both matchers and the Lean
accounting, and a second copy of it is the easiest way there is to lose that.

What stays separate is the composition. `analyzer.py` builds a price for a
region out of what its children came to; `certificate.py` reads a claimed one
back against the bytecode. Neither calls the other, and both count in what is
here.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, land, lnot, lor, u32
from ..tir.types import CAP
from . import spec
from .layout import Layout
from .parser import down, tmp

DEGREES = spec.DEGREES

SIMPLE_OPS = (
    "OpChar",
    "OpCharCI",
    "OpClass",
    "OpAny",
    "OpAnyNoNL",
    "OpBsr",
    "OpCirc",
    "OpCircM",
    "OpDoll",
    "OpDollE",
    "OpDollM",
    "OpSod",
    "OpEod",
    "OpEodn",
    "OpWordB",
    "OpNotWordB",
)
"""The opcodes that cost one visit, write no register and never fork.

Each of them either advances the position by what it consumed or fails, and a
failure resumes somewhere a fork already paid for, so none of them adds flow.
"""


def build(L: Layout) -> None:
    _counters(L)
    _polynomials(L)
    _children(L)


def _children(L: Layout) -> None:
    """The children of every region, in the order their code appears.

    Reading a parent array as a child list is neither arithmetic nor a
    composition rule — it is how both halves get at a tree that is stored as
    one array of parents — so it is written once here rather than three times
    between them.

    Walking backwards puts each child at the front of a list that ends up in
    index order, which for a tree that passed the sibling rule is code order.
    Every parent has to come before its own child, which is what makes one
    backwards pass enough; both callers settle that before calling.
    """
    f = L.func(
        "region_kids",
        params=[
            ("regions", L.FrozenRegions),
            ("kids", L.Marks, "inout"),
            ("sibs", L.Marks, "inout"),
        ],
    )
    regions = f["regions"]
    total = f.let("total", u32, regions.len())
    i = f.let("i", u32, u32(0))
    with f.while_(i < total, down(total, i)):
        f.push(f["kids"], u32(spec.NONE))
        f.push(f["sibs"], u32(spec.NONE))
        f.set(i, i + u32(1))
    f.set(i, total)
    with f.while_(i > u32(1), i.cast(counter)):
        f.set(i, i - u32(1))
        parent = tmp(f, u32, regions.at(i).field("parent"))
        f.set(f["sibs"].at(i), f["kids"].at(parent))
        f.set(f["kids"].at(parent), i)


# --- building polynomials from Python ---


def poly(L: Layout, base=None, **coefs):
    fields = {"base": counter(1) if base is None else base}
    for degree in DEGREES:
        name = f"c{degree}"
        fields[name] = coefs.get(name, counter(0))
    return L.Poly.of(**fields)


def zero(L: Layout):
    """The bound that is nothing at every length."""
    return poly(L)


def const(L: Layout, value):
    return poly(L, c0=value)


def step(L: Layout):
    """n + 1, which is what one more starting position costs."""
    return poly(L, c1=counter(1))


def plus(f, L: Layout, a, b, over):
    out = tmp(f, L.Poly)
    f.call("poly_add", [a, b, inout(over)], dest=out)
    return out


def times(f, L: Layout, a, b, over):
    out = tmp(f, L.Poly)
    f.call("poly_mul", [a, b, inout(over)], dest=out)
    return out


def bump(f, L: Layout, acc, quantity, value, over):
    """Charge one more of something to an accumulator."""
    f.set(acc.field(quantity), plus(f, L, acc.field(quantity), value, over))


def fresh(f, L: Layout, acc, flow):
    """Start an accumulator: nothing charged, and this much flow arriving."""
    for quantity in ("work", "stack", "trail"):
        f.set(acc.field(quantity), zero(L))
    f.set(acc.field("flow"), flow)


def _under(p, degree):
    """This bound has no growth and no power above the one named."""
    test = p.field("base") == counter(1)
    for above in DEGREES[degree + 1 :]:
        test = land(test, p.field(f"c{above}") == counter(0))
    return test


def flat(p):
    """This bound is one number, whatever the subject length."""
    return _under(p, 0)


def linear(p):
    """This bound is at most c * (n + 1), which is BOUNDS.md section 6."""
    return _under(p, 1)


def nothing(p):
    test = p.field("c0") == counter(0)
    for degree in DEGREES[1:]:
        test = land(test, p.field(f"c{degree}") == counter(0))
    return test


def exceeds(L: Layout):
    """ExceedsBudget. The value says nothing, which is what `ok` is for."""
    return L.Bound.of(ok=boolean(False), value=counter(0))


def finite(L: Layout, value):
    return L.Bound.of(ok=boolean(True), value=value)


def _counters(L: Layout) -> None:
    """Counter arithmetic that says when it ran out of room.

    TIR's own counter operations saturate silently, which is right for metering
    a run — a charge that reaches the cap has already failed against the budget
    — and wrong for reporting a bound, where the difference between "exactly
    2^53 - 1" and "more than any counter holds" is the difference between a
    number a caller can use and one they cannot. So the saturation point is
    tested for rather than arrived at, once here, and both ways of carrying the
    answer are built on the same two functions.
    """
    f = L.func(
        "sat_add",
        params=[("a", counter), ("b", counter), ("over", boolean, "inout")],
        ret=counter,
    )
    with f.if_(f["a"] > counter(CAP) - f["b"]):
        f.set(f["over"], boolean(True))
        f.ret(counter(CAP))
    f.ret(f["a"] + f["b"])

    f = L.func(
        "sat_mul",
        params=[("a", counter), ("b", counter), ("over", boolean, "inout")],
        ret=counter,
    )
    a = f["a"]
    b = f["b"]
    with f.if_(lor(a == counter(0), b == counter(0))):
        f.ret(counter(0))
    with f.if_(a > counter(CAP).div(b, counter(0))):
        f.set(f["over"], boolean(True))
        f.ret(counter(CAP))
    f.ret(a * b)

    away = exceeds(L)

    f = L.func("bound_add", params=[("a", L.Bound), ("b", L.Bound)], ret=L.Bound)
    with f.if_(lor(lnot(f["a"].field("ok")), lnot(f["b"].field("ok")))):
        f.ret(away)
    over = f.let("over", boolean, boolean(False))
    total = f.let("total", counter)
    f.call(
        "sat_add",
        [f["a"].field("value"), f["b"].field("value"), inout(over)],
        dest=total,
    )
    with f.if_(over):
        f.ret(away)
    f.ret(finite(L, total))

    f = L.func("bound_mul", params=[("a", L.Bound), ("b", L.Bound)], ret=L.Bound)
    with f.if_(lor(lnot(f["a"].field("ok")), lnot(f["b"].field("ok")))):
        f.ret(away)
    over = f.let("over", boolean, boolean(False))
    total = f.let("total", counter)
    f.call(
        "sat_mul",
        [f["a"].field("value"), f["b"].field("value"), inout(over)],
        dest=total,
    )
    with f.if_(over):
        f.ret(away)
    f.ret(finite(L, total))

    f = L.func("bound_pow", params=[("base", counter), ("exp", counter)], ret=L.Bound)
    base = f["base"]
    exp = f["exp"]
    # Both degenerate bases are answered before the loop, which is what bounds
    # it: past here the running product at least doubles every time round, so
    # it reaches the cap within the 53 doublings a counter has room for and the
    # loop stops on its own.
    with f.if_(base == counter(1)):
        f.ret(finite(L, counter(1)))
    with f.if_(base == counter(0)):
        with f.if_(exp == counter(0)):
            f.ret(finite(L, counter(1)))
        f.ret(finite(L, counter(0)))
    out = f.let("out", L.Bound, finite(L, counter(1)))
    i = f.let("i", counter, counter(0))
    one = f.let("one", L.Bound)
    with f.while_(land(i < exp, out.field("ok")), exp - i):
        f.call("bound_mul", [out, finite(L, base)], dest=one)
        f.set(out, one)
        f.set(i, i + counter(1))
    f.ret(out)


def _polynomials(L: Layout) -> None:
    """The algebra of BOUNDS.md section 2, as five small functions.

    A bound is one growth base and one coefficient per power of (n + 1), which
    is closed under everything the composition rules do: adding two bounds adds
    their coefficients, multiplying them multiplies the bases and convolves the
    coefficients, and neither can smuggle in a shape the evaluator has no rule
    for. What it costs is precision — two bounds with different bases are added
    under the larger of the two — and that is a loss the analyzer can afford,
    since the difference only ever shows up between an exponential term and
    something already dwarfed by it.

    Every operation reports saturation through `over` rather than clamping
    quietly, because a coefficient that stopped at the cap is a requirement the
    checker would go on to compare a certificate against and find satisfied.
    """
    f = L.func("poly_norm", params=[("p", L.Poly)], ret=L.Poly)
    # A bound worth nothing carries no growth either, so that a claim of one is
    # not refused for naming a smaller base than a requirement that is zero.
    with f.if_(nothing(f["p"])):
        f.ret(zero(L))
    f.ret(f["p"])

    f = L.func(
        "poly_add",
        params=[("a", L.Poly), ("b", L.Poly), ("over", boolean, "inout")],
        ret=L.Poly,
    )
    a = f["a"]
    b = f["b"]
    over = f["over"]
    out = f.let("out", L.Poly)
    f.set(out.field("base"), a.field("base"))
    with f.if_(b.field("base") > a.field("base")):
        f.set(out.field("base"), b.field("base"))
    for degree in DEGREES:
        name = f"c{degree}"
        one = tmp(f, counter)
        f.call("sat_add", [a.field(name), b.field(name), inout(over)], dest=one)
        f.set(out.field(name), one)
    done = f.let("done", L.Poly)
    f.call("poly_norm", [out], dest=done)
    f.ret(done)

    f = L.func(
        "poly_mul",
        params=[("a", L.Poly), ("b", L.Poly), ("over", boolean, "inout")],
        ret=L.Poly,
    )
    a = f["a"]
    b = f["b"]
    over = f["over"]
    out = f.let("out", L.Poly, zero(L))
    base = f.let("base", counter)
    f.call("sat_mul", [a.field("base"), b.field("base"), inout(over)], dest=base)
    f.set(out.field("base"), base)
    # A term with a zero on either side contributes nothing, and every bound
    # this engine composes is mostly zeros — a constant multiplied by a
    # constant is one term out of twenty-five. So the pair is asked about
    # first, which is the same question the over-degree case below already had
    # to ask, and the two cases become one shape.
    for left in DEGREES:
        for right in DEGREES:
            lname = f"c{left}"
            rname = f"c{right}"
            with f.if_(
                land(a.field(lname) != counter(0), b.field(rname) != counter(0))
            ):
                if left + right > spec.MAX_DEGREE:
                    # No field to put it in, and dropping it would be the one
                    # rounding that goes the wrong way.
                    f.set(over, boolean(True))
                else:
                    name = f"c{left + right}"
                    one = tmp(f, counter)
                    f.call(
                        "sat_mul",
                        [a.field(lname), b.field(rname), inout(over)],
                        dest=one,
                    )
                    running = tmp(f, counter)
                    f.call("sat_add", [out.field(name), one, inout(over)], dest=running)
                    f.set(out.field(name), running)
    done = f.let("done", L.Poly)
    f.call("poly_norm", [out], dest=done)
    f.ret(done)

    f = L.func("poly_ge", params=[("a", L.Poly), ("b", L.Poly)], ret=boolean)
    # Every basis function is nonnegative and grows with its base and its
    # power, so dominating coefficient by coefficient is enough to dominate at
    # every subject length. It is not necessary — n^2 is above n and this says
    # otherwise — and that is the right way round for a checker.
    with f.if_(f["a"].field("base") < f["b"].field("base")):
        f.ret(boolean(False))
    for degree in DEGREES:
        name = f"c{degree}"
        with f.if_(f["a"].field(name) < f["b"].field(name)):
            f.ret(boolean(False))
    f.ret(boolean(True))

    f = L.func("poly_value", params=[("p", L.Poly), ("n", counter)], ret=L.Bound)
    p = f["p"]
    with f.if_(nothing(p)):
        f.ret(finite(L, counter(0)))
    # The powers are built up one at a time and only spent where there is a
    # coefficient to spend them on: (n + 1)^4 saturates long before the subject
    # lengths a caller cares about, and a term that was never in the bound must
    # not be what refuses it.
    rise = f.let("rise", L.Bound)
    f.call("bound_add", [finite(L, f["n"]), finite(L, counter(1))], dest=rise)
    power = f.let("power", L.Bound, finite(L, counter(1)))
    total = f.let("total", L.Bound, finite(L, p.field("c0")))
    for degree in DEGREES[1:]:
        # Nothing above here has a coefficient, so the power that would carry
        # one is not worth raising — and raising it would saturate and refuse a
        # bound the term it belongs to was never in.
        spent = p.field(f"c{degree}") != counter(0)
        for above in DEGREES[degree + 1 :]:
            spent = lor(spent, p.field(f"c{above}") != counter(0))
        with f.if_(spent):
            raised = tmp(f, L.Bound)
            f.call("bound_mul", [power, rise], dest=raised)
            f.set(power, raised)
            with f.if_(p.field(f"c{degree}") != counter(0)):
                one = tmp(f, L.Bound)
                f.call("bound_mul", [finite(L, p.field(f"c{degree}")), power], dest=one)
                running = tmp(f, L.Bound)
                f.call("bound_add", [total, one], dest=running)
                f.set(total, running)
    growth = f.let("growth", L.Bound)
    f.call("bound_pow", [p.field("base"), f["n"]], dest=growth)
    out = f.let("out", L.Bound)
    f.call("bound_mul", [growth, total], dest=out)
    f.ret(out)


__all__ = [
    "DEGREES",
    "SIMPLE_OPS",
    "build",
    "bump",
    "const",
    "exceeds",
    "finite",
    "flat",
    "fresh",
    "linear",
    "nothing",
    "plus",
    "poly",
    "step",
    "times",
    "zero",
]
