"""The bound certificate and its checker, written in TIR.

DESIGN.md section 5 splits the resource analysis in two on purpose. An analyzer
searches for a bound certificate — the compiler's region tree, annotated with
the terms that price each region — and a deliberately small checker decides
whether to believe it. The analyzer needs no proof at all; the checker is what
Lean's layer A proves sound, so an accepted certificate really does bound the
run. Proving a checker is far less work than proving a search, and it is what
keeps the analyzer mechanically connectable to the proofs instead of drifting
into a plausibility argument.

This is the checker half, plus the arithmetic both halves count in. Nothing in
the engine calls any of it yet, and the checker is not finished: what it rules
on is the shape of a certificate, not yet whether the certificate bounds
anything. That distinction is worth keeping in front of the reader, because a
checker that accepts is easy to mistake for a checker that vouches.

One bound is a sum of terms, each of them

    coef * base^n * n^degree

in the subject length n. A base of one is the polynomial case, which is what a
Pike-eligible pattern gets; a base above one is the shape a backtracking bound
takes when structural analysis finds genuine ambiguity, and it saturates within
a few dozen bytes of subject, which is the honest answer rather than a number
nobody could budget for.

Evaluation is counter arithmetic with every step pre-checked, so saturation
comes back as the explicit ExceedsBudget of DESIGN.md section 2.4 instead of
being passed off as a maximum. The two projections that have their own ceiling
apply it here too: a stack bound above what the entry cap allows, or a memory
bound above the section 3 byte ceiling, is ExceedsBudget as well, because a
number no valid limit could match is no use to the caller who has to pick one.

So, precisely: what the checker decides is that the region tree is a tree, that
its ranges nest and its siblings do not overlap, that every bound it names is a
bound this arithmetic can evaluate, and that a certificate calling itself
linear names a bound that is. What it does not decide is whether a region's
terms dominate the per-opcode accounting of what the region contains, which is
the rule the bounds are actually sound under.

Until that rule lands, an accepted certificate says a well-formed thing and
nothing about the run: `codelen` is the only fact about the program the checker
is given, so two programs of the same length are indistinguishable to it, and a
root with three empty sums is accepted while reporting no cost at all. The
composition rules need the code and the repetition table rather than a length,
so the signature grows when they arrive — before an analyzer produces anything
worth believing, not after.
"""

from __future__ import annotations

from ..dsl import boolean, counter, land, lnot, lor, u32
from ..tir.types import CAP, CEILING
from . import spec
from .layout import Layout
from .parser import down, tmp


def build(L: Layout) -> None:
    _arithmetic(L)
    _evaluation(L)
    _check(L)


def _exceeds(L: Layout):
    """ExceedsBudget. The value says nothing, which is what `ok` is for."""
    return L.Bound.of(ok=boolean(False), value=counter(0))


def _finite(L: Layout, value):
    return L.Bound.of(ok=boolean(True), value=value)


def _arithmetic(L: Layout) -> None:
    """Counter arithmetic that says when it ran out of room.

    TIR's own counter operations saturate silently, which is right for metering
    a run — a charge that reaches the cap has already failed against the budget
    — and wrong for reporting a bound, where the difference between "exactly
    2^53 - 1" and "more than any counter holds" is the difference between a
    number a caller can use and one they cannot. So each operation is
    pre-checked here a second time and the answer carries whether it fits.
    """
    exceeds = _exceeds(L)

    f = L.func("bound_add", params=[("a", L.Bound), ("b", L.Bound)], ret=L.Bound)
    with f.if_(lor(lnot(f["a"].field("ok")), lnot(f["b"].field("ok")))):
        f.ret(exceeds)
    left = tmp(f, counter, f["a"].field("value"))
    right = tmp(f, counter, f["b"].field("value"))
    with f.if_(left > counter(CAP) - right):
        f.ret(exceeds)
    f.ret(_finite(L, left + right))

    f = L.func("bound_mul", params=[("a", L.Bound), ("b", L.Bound)], ret=L.Bound)
    with f.if_(lor(lnot(f["a"].field("ok")), lnot(f["b"].field("ok")))):
        f.ret(exceeds)
    left = tmp(f, counter, f["a"].field("value"))
    right = tmp(f, counter, f["b"].field("value"))
    with f.if_(lor(left == counter(0), right == counter(0))):
        f.ret(_finite(L, counter(0)))
    with f.if_(left > counter(CAP).div(right, counter(0))):
        f.ret(exceeds)
    f.ret(_finite(L, left * right))

    f = L.func("bound_pow", params=[("base", counter), ("exp", counter)], ret=L.Bound)
    base = f["base"]
    exp = f["exp"]
    # Both degenerate bases are answered before the loop, which is what bounds
    # it: past here the running product at least doubles every time round, so
    # it reaches the cap within the 53 doublings a counter has room for and the
    # loop stops on its own.
    with f.if_(base == counter(1)):
        f.ret(_finite(L, counter(1)))
    with f.if_(base == counter(0)):
        with f.if_(exp == counter(0)):
            f.ret(_finite(L, counter(1)))
        f.ret(_finite(L, counter(0)))
    out = f.let("out", L.Bound, _finite(L, counter(1)))
    i = f.let("i", counter, counter(0))
    step = f.let("step", L.Bound)
    with f.while_(land(i < exp, out.field("ok")), exp - i):
        f.call("bound_mul", [out, _finite(L, base)], dest=step)
        f.set(out, step)
        f.set(i, i + counter(1))
    f.ret(out)


def _evaluation(L: Layout) -> None:
    """One term, one sum, and the three bounds the accessors of section 2.4 ask for."""
    exceeds = _exceeds(L)

    f = L.func("term_value", params=[("t", L.Term), ("n", counter)], ret=L.Bound)
    t = f["t"]
    # The checker refuses a term with no coefficient, so this is the same kind
    # of guard as the one in `sum_value` below: what an unchecked certificate
    # gets is an answer rather than a refusal about arithmetic its own value
    # never contained.
    with f.if_(t.field("coef") == counter(0)):
        f.ret(_finite(L, counter(0)))
    growth = f.let("growth", L.Bound)
    f.call("bound_pow", [t.field("base").cast(counter), f["n"]], dest=growth)
    power = f.let("power", L.Bound)
    f.call("bound_pow", [f["n"], t.field("degree").cast(counter)], dest=power)
    scaled = f.let("scaled", L.Bound)
    f.call(
        "bound_mul",
        [_finite(L, t.field("coef")), growth],
        dest=scaled,
    )
    total = f.let("total", L.Bound)
    f.call("bound_mul", [scaled, power], dest=total)
    f.ret(total)

    f = L.func(
        "sum_value",
        params=[("terms", L.FrozenTerms), ("s", L.Sum), ("n", counter)],
        ret=L.Bound,
    )
    terms = f["terms"]
    count = f["s"].field("count")
    out = f.let("out", L.Bound, _finite(L, counter(0)))
    i = f.let("i", u32, u32(0))
    with f.while_(land(i < count, out.field("ok")), down(count, i)):
        at = tmp(f, u32, f["s"].field("first") + i)
        # The checker has already refused a sum that reaches past the table, so
        # this only settles what an unchecked certificate answers: a refusal
        # rather than a trap.
        with f.if_(at >= terms.len()):
            f.ret(exceeds)
        one = tmp(f, L.Bound)
        f.call("term_value", [terms.at(at), f["n"]], dest=one)
        running = tmp(f, L.Bound)
        f.call("bound_add", [out, one], dest=running)
        f.set(out, running)
        f.set(i, i + u32(1))
    f.ret(out)

    f = L.func(
        "cert_bound",
        params=[("cert", L.Cert), ("kind", L.Bk), ("n", counter)],
        ret=L.Bound,
    )
    # The whole-pattern bound is the root region's, rather than a fourth copy
    # of the numbers sitting next to the tree that produced them.
    regions = f.let("regions", L.FrozenRegions, f["cert"].field("regions"))
    with f.if_(regions.len() == u32(0)):
        f.ret(exceeds)
    root = f.let("root", L.Region, regions.at(u32(0)))
    which = f.let("which", L.Sum)
    ceiling = f.let("ceiling", counter, counter(CAP))
    with f.switch(f["kind"]) as arm:
        with arm.case("BkCost"):
            f.set(which, root.field("cost"))
        with arm.case("BkStack"):
            f.set(which, root.field("stack"))
            f.set(ceiling, counter(spec.MAX_STACK))
        with arm.case("BkMem"):
            f.set(which, root.field("mem"))
            f.set(ceiling, counter(CEILING))
    out = f.let("out", L.Bound)
    f.call("sum_value", [f["cert"].field("terms"), which, f["n"]], dest=out)
    with f.if_(land(out.field("ok"), out.field("value") > ceiling)):
        f.ret(exceeds)
    f.ret(out)


def _check(L: Layout) -> None:
    """Is this a certificate at all?

    Every answer is one named reason rather than a bare false, because a
    rejection nobody can read is a rejection nobody will believe.
    """
    f = L.func("sum_fits", params=[("s", L.Sum), ("held", u32)], ret=boolean)
    s = f["s"]
    with f.if_(s.field("count") == u32(0)):
        f.ret(boolean(True))
    with f.if_(s.field("first") >= f["held"]):
        f.ret(boolean(False))
    f.ret(s.field("count") <= f["held"] - s.field("first"))

    f = L.func("cert_check", params=[("cert", L.Cert), ("codelen", u32)], ret=L.Cr)
    cert = f["cert"]
    regions = f.let("regions", L.FrozenRegions, cert.field("regions"))
    terms = f.let("terms", L.FrozenTerms, cert.field("terms"))
    total = tmp(f, u32, regions.len())
    held = tmp(f, u32, terms.len())
    with f.if_(total == u32(0)):
        f.ret(L.Cr.CrNoRegions)

    root = f.let("root", L.Region, regions.at(u32(0)))
    with f.if_(root.field("kind") != L.Rk.RkRoot):
        f.ret(L.Cr.CrRootKind)
    with f.if_(root.field("parent") != u32(spec.NONE)):
        f.ret(L.Cr.CrRootParent)
    with f.if_(lor(root.field("lo") != u32(0), root.field("hi") != f["codelen"])):
        f.ret(L.Cr.CrRootRange)

    # Where the last child of each region ended, so that one pass settles both
    # halves of the sibling rule: children arrive in index order, and their
    # ranges do not overlap. A region starts out as its own `lo`, which makes
    # the first child's test the containment test and needs no special case.
    #
    # Requiring the order is deliberate rather than incidental. The compiler
    # emits regions as it flattens the AST, which is already source order, so
    # the rule costs a correct analyzer nothing and saves the checker a sort.
    ends = f.let("ends", L.Ends)
    i = f.let("i", u32, u32(0))
    with f.while_(i < total, down(total, i)):
        f.push(ends, regions.at(i).field("lo"))
        f.set(i, i + u32(1))

    f.set(i, u32(1))
    with f.while_(i < total, down(total, i)):
        here = tmp(f, L.Region, regions.at(i))
        parent = tmp(f, u32, here.field("parent"))
        with f.if_(here.field("kind") == L.Rk.RkRoot):
            f.ret(L.Cr.CrTwoRoots)
        # A parent below its own child is what makes the tree a tree without
        # walking it: every chain of parents strictly descends, so it ends at
        # region 0, and region 0 is the root.
        with f.if_(parent >= i):
            f.ret(L.Cr.CrParentOrder)
        with f.if_(here.field("lo") > here.field("hi")):
            f.ret(L.Cr.CrBackwards)
        outer = tmp(f, L.Region, regions.at(parent))
        with f.if_(
            lor(
                here.field("lo") < outer.field("lo"),
                here.field("hi") > outer.field("hi"),
            )
        ):
            f.ret(L.Cr.CrNotNested)
        with f.if_(here.field("lo") < ends.at(parent)):
            f.ret(L.Cr.CrOverlap)
        f.set(ends.at(parent), here.field("hi"))
        f.set(i, i + u32(1))

    f.set(i, u32(0))
    fits = tmp(f, boolean, boolean(False))
    with f.while_(i < total, down(total, i)):
        priced = tmp(f, L.Region, regions.at(i))
        for quantity in ("cost", "stack", "mem"):
            f.call("sum_fits", [priced.field(quantity), held], dest=fits)
            with f.if_(lnot(fits)):
                f.ret(L.Cr.CrTermRange)
        f.set(i, i + u32(1))

    f.set(i, u32(0))
    with f.while_(i < held, down(held, i)):
        one = tmp(f, L.Term, terms.at(i))
        # A term worth nothing is worth nothing whatever its shape, which would
        # make every rule below conditional on a coefficient — and would let a
        # certificate call itself linear while naming an exponential term that
        # happens to be multiplied by zero. A sum that contributes nothing says
        # so by holding no terms, so refusing here costs an analyzer nothing.
        with f.if_(one.field("coef") == counter(0)):
            f.ret(L.Cr.CrZeroTerm)
        # A base of zero is 0^n, which is 1 at n = 0 and 0 everywhere else. No
        # bound has that shape, and letting one through would make a term that
        # vanishes on longer subjects look like a bound that holds.
        with f.if_(one.field("base") == u32(0)):
            f.ret(L.Cr.CrBase)
        with f.if_(one.field("degree") > u32(spec.MAX_DEGREE)):
            f.ret(L.Cr.CrDegree)
        f.set(i, i + u32(1))

    # The one claim in a certificate that is not a number, held to the shape it
    # names: linear means the cost really is at most c * (n + 1), so no growing
    # base and no power above the first. Classification soundness is a Layer A
    # obligation (DESIGN.md section 6), and this is the part of it the checker
    # can settle by looking. Only the root's cost is asked about, because the
    # class is a claim about the whole pattern and the root is where the whole
    # pattern's bound lives.
    with f.if_(cert.field("complexity") == L.Cc.CcLinear):
        shape = tmp(f, L.Sum, root.field("cost"))
        f.set(i, u32(0))
        with f.while_(i < shape.field("count"), down(shape.field("count"), i)):
            claimed = tmp(f, L.Term, terms.at(shape.field("first") + i))
            with f.if_(
                lor(claimed.field("base") != u32(1), claimed.field("degree") > u32(1))
            ):
                f.ret(L.Cr.CrNotLinear)
            f.set(i, i + u32(1))

    f.ret(L.Cr.CrOk)
