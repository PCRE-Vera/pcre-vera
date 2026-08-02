"""The bound certificate and its checker, written in TIR.

DESIGN.md section 5 splits the resource analysis in two on purpose. An analyzer
searches for a bound certificate — the compiler's region tree, annotated with
what each region costs — and a deliberately small checker decides whether to
believe it. The analyzer needs no proof at all; the checker is what Lean's
layer A proves sound, so an accepted certificate really does bound the run.
Proving a checker is far less work than proving a search, and it is what keeps
the analyzer mechanically connectable to the proofs instead of drifting into a
plausibility argument.

This is the checker half, plus the arithmetic both halves count in. The rules
it applies are BOUNDS.md, which states the cost of every opcode this engine
emits and the composition rule of every region kind, and is the document a
reader should have open beside this one. What is here is the transcription.

The subject is the compiled pattern itself rather than any restatement of it,
so there is nothing that could come to disagree with the bytecode the matcher
will actually run: the code, the repetition table, the capture and register
counts, and the length derived from the code. On top of that comes the
configuration the certificate is being checked for. Only `CfgBacktrack` has
rules today; the Pike VM and the memoized path have their own accounting and
say so rather than borrowing this one.

A bound is `base^n` times a polynomial in `n + 1`, held in a `Poly`. Evaluation
is counter arithmetic with every step pre-checked, so saturation comes back as
the explicit ExceedsBudget of DESIGN.md section 2.4 instead of being passed off
as a maximum. The two projections that have their own ceiling apply it here
too: a stack bound above what the entry cap allows, or a memory bound above the
section 3 byte ceiling, is ExceedsBudget as well, because a number no valid
limit could match is no use to the caller who has to pick one.

So what an accepted certificate now says is the whole of it: for this program,
in this configuration, at every subject length, every start offset and every
combination of match options, the matcher charges no more cost, pushes no more
backtrack entries and reserves no more scratch than the certificate names. The
one thing it does not say is that the numbers are tight — they are an upper
bound and the analyzer is free to be generous — which is why every rule below
is written to refuse rather than to round.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, land, lnot, lor, u32
from ..tir.types import CAP, CEILING
from . import spec
from .layout import Layout
from .parser import down, tmp

DEGREES = tuple(range(spec.MAX_DEGREE + 1))
"""The powers of (n + 1) a bound polynomial carries, as field suffixes."""

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
    _arithmetic(L)
    _polynomials(L)
    _evaluation(L)
    _walk(L)
    _check(L)


# --- building polynomials from Python ---


def _poly(L: Layout, base=None, **coefs):
    fields = {"base": counter(1) if base is None else base}
    for degree in DEGREES:
        name = f"c{degree}"
        fields[name] = coefs.get(name, counter(0))
    return L.Poly.of(**fields)


def _zero(L: Layout):
    """The bound that is nothing at every length."""
    return _poly(L)


def _const(L: Layout, value):
    return _poly(L, c0=value)


def _step(L: Layout):
    """n + 1, which is what one more starting position costs."""
    return _poly(L, c1=counter(1))


def _plus(f, L: Layout, a, b, over):
    out = tmp(f, L.Poly)
    f.call("poly_add", [a, b, inout(over)], dest=out)
    return out


def _times(f, L: Layout, a, b, over):
    out = tmp(f, L.Poly)
    f.call("poly_mul", [a, b, inout(over)], dest=out)
    return out


def _flat(p):
    """This bound is one number, whatever the subject length."""
    test = p.field("base") == counter(1)
    for degree in DEGREES[1:]:
        test = land(test, p.field(f"c{degree}") == counter(0))
    return test


def _nothing(p):
    test = p.field("c0") == counter(0)
    for degree in DEGREES[1:]:
        test = land(test, p.field(f"c{degree}") == counter(0))
    return test


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

    exceeds = _exceeds(L)

    f = L.func("bound_add", params=[("a", L.Bound), ("b", L.Bound)], ret=L.Bound)
    with f.if_(lor(lnot(f["a"].field("ok")), lnot(f["b"].field("ok")))):
        f.ret(exceeds)
    over = f.let("over", boolean, boolean(False))
    total = f.let("total", counter)
    f.call(
        "sat_add",
        [f["a"].field("value"), f["b"].field("value"), inout(over)],
        dest=total,
    )
    with f.if_(over):
        f.ret(exceeds)
    f.ret(_finite(L, total))

    f = L.func("bound_mul", params=[("a", L.Bound), ("b", L.Bound)], ret=L.Bound)
    with f.if_(lor(lnot(f["a"].field("ok")), lnot(f["b"].field("ok")))):
        f.ret(exceeds)
    over = f.let("over", boolean, boolean(False))
    total = f.let("total", counter)
    f.call(
        "sat_mul",
        [f["a"].field("value"), f["b"].field("value"), inout(over)],
        dest=total,
    )
    with f.if_(over):
        f.ret(exceeds)
    f.ret(_finite(L, total))

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
    with f.if_(_nothing(f["p"])):
        f.ret(_zero(L))
    f.ret(f["p"])

    f = L.func(
        "poly_add",
        params=[("a", L.Poly), ("b", L.Poly), ("over", boolean, "inout")],
        ret=L.Poly,
    )
    a = f["a"]
    b = f["b"]
    over = f["over"]
    out = f.let("out", L.Poly, _zero(L))
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
    out = f.let("out", L.Poly, _zero(L))
    base = f.let("base", counter)
    f.call("sat_mul", [a.field("base"), b.field("base"), inout(over)], dest=base)
    f.set(out.field("base"), base)
    for left in DEGREES:
        for right in DEGREES:
            lname = f"c{left}"
            rname = f"c{right}"
            if left + right > spec.MAX_DEGREE:
                # No field to put it in, and dropping it would be the one
                # rounding that goes the wrong way.
                with f.if_(
                    land(a.field(lname) != counter(0), b.field(rname) != counter(0))
                ):
                    f.set(over, boolean(True))
                continue
            name = f"c{left + right}"
            one = tmp(f, counter)
            f.call("sat_mul", [a.field(lname), b.field(rname), inout(over)], dest=one)
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
    with f.if_(_nothing(p)):
        f.ret(_finite(L, counter(0)))
    # The powers are built up one at a time and only spent where there is a
    # coefficient to spend them on: (n + 1)^4 saturates long before the subject
    # lengths a caller cares about, and a term that was never in the bound must
    # not be what refuses it.
    step = f.let("step", L.Bound)
    f.call("bound_add", [_finite(L, f["n"]), _finite(L, counter(1))], dest=step)
    power = f.let("power", L.Bound, _finite(L, counter(1)))
    total = f.let("total", L.Bound, _finite(L, p.field("c0")))
    for degree in DEGREES[1:]:
        raised = tmp(f, L.Bound)
        f.call("bound_mul", [power, step], dest=raised)
        f.set(power, raised)
        with f.if_(p.field(f"c{degree}") != counter(0)):
            one = tmp(f, L.Bound)
            f.call("bound_mul", [_finite(L, p.field(f"c{degree}")), power], dest=one)
            running = tmp(f, L.Bound)
            f.call("bound_add", [total, one], dest=running)
            f.set(total, running)
    growth = f.let("growth", L.Bound)
    f.call("bound_pow", [p.field("base"), f["n"]], dest=growth)
    out = f.let("out", L.Bound)
    f.call("bound_mul", [growth, total], dest=out)
    f.ret(out)


def _evaluation(L: Layout) -> None:
    """The three bounds the accessors of DESIGN.md section 2.4 ask for."""
    f = L.func(
        "cert_bound",
        params=[("cert", L.Cert), ("kind", L.Bk), ("n", counter)],
        ret=L.Bound,
    )
    cert = f["cert"]
    which = f.let("which", L.Poly)
    ceiling = f.let("ceiling", counter, counter(CAP))
    with f.switch(f["kind"]) as arm:
        with arm.case("BkCost"):
            f.set(which, cert.field("cost"))
        with arm.case("BkStack"):
            f.set(which, cert.field("stack"))
            f.set(ceiling, counter(spec.MAX_STACK))
        with arm.case("BkMem"):
            f.set(which, cert.field("mem"))
            f.set(ceiling, counter(CEILING))
    out = f.let("out", L.Bound)
    f.call("poly_value", [which, f["n"]], dest=out)
    with f.if_(land(out.field("ok"), out.field("value") > ceiling)):
        f.ret(_exceeds(L))
    f.ret(out)


def _walk(L: Layout) -> None:
    """What one span of bytecode costs, and what the three shapes cost.

    Each of these fills an accumulator: the visits, the backtrack entries and
    the undo entries charged for one entry into the span, and the flow that
    leaves it going forward. Flow is the whole of the composition — every
    quantity is linear in it — so the accumulator's `flow` field starts as one
    entry and ends as the region's ambiguity.
    """
    _span(L)
    _alt(L)
    _repeat(L)


def _span(L: Layout) -> None:
    f = L.func(
        "scan_span",
        params=[
            ("code", L.FrozenCode),
            ("regions", L.FrozenRegions),
            ("sibs", L.Marks, "inout"),
            ("lo", u32),
            ("hi", u32),
            ("cursor", u32, "inout"),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    regions = f["regions"]
    cursor = f["cursor"]
    acc = f["acc"]
    over = f["over"]
    pc = f.let("pc", u32, f["lo"])

    with f.while_(pc < f["hi"], down(f["hi"], pc)):
        at = tmp(f, u32, cursor)
        with f.if_(at != u32(spec.NONE)):
            kid = tmp(f, L.Region, regions.at(at))
            with f.if_(kid.field("lo") < pc):
                f.ret(L.Cr.CrShape)
            with f.if_(kid.field("lo") == pc):
                # A child covering no instruction would leave the position
                # where it was, and there is nothing for one to say that its
                # parent does not already say.
                with f.if_(lor(kid.field("hi") <= pc, kid.field("hi") > f["hi"])):
                    f.ret(L.Cr.CrShape)
                flow = tmp(f, L.Poly, acc.field("flow"))
                for quantity in ("work", "stack", "trail"):
                    priced = _times(f, L, flow, kid.field(quantity), over)
                    running = _plus(f, L, acc.field(quantity), priced, over)
                    f.set(acc.field(quantity), running)
                onward = _times(f, L, flow, kid.field("outs"), over)
                f.set(acc.field("flow"), onward)
                f.set(pc, kid.field("hi"))
                f.set(cursor, f["sibs"].at(at))
                f.cont()

        visited = _plus(f, L, acc.field("work"), acc.field("flow"), over)
        with f.switch(code.at(pc).field("op")) as arm:
            for name in SIMPLE_OPS:
                with arm.case(name):
                    f.set(acc.field("work"), visited)
            with arm.case("OpSave"):
                f.set(acc.field("work"), visited)
                recorded = _plus(f, L, acc.field("trail"), acc.field("flow"), over)
                f.set(acc.field("trail"), recorded)
            with arm.case("OpAccept"):
                # A match ends the attempt, so nothing after this point is
                # reached by way of it.
                f.set(acc.field("work"), visited)
                f.set(acc.field("flow"), _zero(L))
            with arm.otherwise():
                # Every instruction that forks, jumps or drives a repetition
                # belongs to a region whose kind says how to price it. Meeting
                # one loose is the tree failing to explain the program.
                f.ret(L.Cr.CrOpcode)
        f.set(pc, pc + u32(1))

    f.ret(L.Cr.CrOk)


def _alt(L: Layout) -> None:
    f = L.func(
        "scan_alt",
        params=[
            ("code", L.FrozenCode),
            ("regions", L.FrozenRegions),
            ("kids", L.Marks, "inout"),
            ("sibs", L.Marks, "inout"),
            ("at", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    regions = f["regions"]
    acc = f["acc"]
    over = f["over"]
    here = f.let("here", L.Region, regions.at(f["at"]))
    hi = f.let("hi", u32, here.field("hi"))
    total = f.let("total", u32, regions.len())
    # An alternation compiles to `split branch jump split branch jump ...
    # branch`, with every jump patched to the end and every split's other arm
    # pointing at the next one, so walking the branches walks the code.
    p = f.let("p", u32, here.field("lo"))
    c = f.let("c", u32, f["kids"].at(f["at"]))
    seen = f.let("seen", u32, u32(0))
    k = f.let("k", u32, u32(0))
    for quantity in ("work", "stack", "trail", "flow"):
        f.set(acc.field(quantity), _zero(L))

    with f.while_(land(k < total, c != u32(spec.NONE)), down(total, k)):
        kid = tmp(f, L.Region, regions.at(c))
        with f.if_(kid.field("kind") != L.Rk.RkBranch):
            f.ret(L.Cr.CrChildren)
        nxt = tmp(f, u32, f["sibs"].at(c))
        with f.if_(nxt != u32(spec.NONE)):
            with f.if_(p >= hi):
                f.ret(L.Cr.CrShape)
            fork = tmp(f, L.Inst, code.at(p))
            with f.if_(fork.field("op") != L.Op.OpSplit):
                f.ret(L.Cr.CrShape)
            with f.if_(fork.field("arg") != p + u32(1)):
                f.ret(L.Cr.CrShape)
            with f.if_(kid.field("lo") != p + u32(1)):
                f.ret(L.Cr.CrShape)
            end = tmp(f, u32, kid.field("hi"))
            with f.if_(end >= hi):
                f.ret(L.Cr.CrShape)
            leave = tmp(f, L.Inst, code.at(end))
            with f.if_(
                lor(leave.field("op") != L.Op.OpJump, leave.field("arg") != hi)
            ):
                f.ret(L.Cr.CrShape)
            with f.if_(fork.field("alt") != end + u32(1)):
                f.ret(L.Cr.CrShape)
            # The split is visited once, and the jump once per way the branch
            # found to succeed.
            extra = _plus(f, L, _const(L, counter(1)), kid.field("outs"), over)
            f.set(acc.field("work"), _plus(f, L, acc.field("work"), extra, over))
            f.set(
                acc.field("stack"),
                _plus(f, L, acc.field("stack"), _const(L, counter(1)), over),
            )
            f.set(p, end + u32(1))
        with f.else_():
            with f.if_(lor(kid.field("lo") != p, kid.field("hi") != hi)):
                f.ret(L.Cr.CrShape)
        # Backtracking works its way along the chain of splits, so every branch
        # is entered, once.
        for quantity, claimed in (
            ("work", "work"),
            ("stack", "stack"),
            ("trail", "trail"),
            ("flow", "outs"),
        ):
            f.set(
                acc.field(quantity),
                _plus(f, L, acc.field(quantity), kid.field(claimed), over),
            )
        f.set(seen, seen + u32(1))
        f.set(c, nxt)
        f.set(k, k + u32(1))

    with f.if_(c != u32(spec.NONE)):
        f.ret(L.Cr.CrChildren)
    # One branch is not an alternation: the compiler emits no split for it, so
    # a region claiming to be one is pricing instructions that are not there.
    with f.if_(seen < u32(2)):
        f.ret(L.Cr.CrShape)
    f.ret(L.Cr.CrOk)


def _body(f, L: Layout, lo, hi, cursor, acc, over, verdict) -> None:
    """Price the span a repetition repeats, whichever of the two shapes it is.

    Every child of a repeat region lies in that span; one left over is a region
    covering part of the machinery around it, which no rule prices.
    """
    f.call(
        "scan_span",
        [
            f["code"],
            f["regions"],
            inout(f["sibs"]),
            lo,
            hi,
            inout(cursor),
            inout(acc),
            inout(over),
        ],
        dest=verdict,
    )
    with f.if_(verdict != L.Cr.CrOk):
        f.ret(verdict)
    with f.if_(cursor != u32(spec.NONE)):
        f.ret(L.Cr.CrChildren)


def _repeat(L: Layout) -> None:
    f = L.func(
        "scan_repeat",
        params=[
            ("code", L.FrozenCode),
            ("reps", L.FrozenReps),
            ("regions", L.FrozenRegions),
            ("kids", L.Marks, "inout"),
            ("sibs", L.Marks, "inout"),
            ("at", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    acc = f["acc"]
    over = f["over"]
    here = f.let("here", L.Region, f["regions"].at(f["at"]))
    lo = f.let("lo", u32, here.field("lo"))
    hi = f.let("hi", u32, here.field("hi"))
    with f.if_(hi <= lo):
        f.ret(L.Cr.CrShape)
    cursor = f.let("cursor", u32, f["kids"].at(f["at"]))
    verdict = f.let("verdict", L.Cr, L.Cr.CrOk)
    head = f.let("head", L.Inst, code.at(lo))
    for quantity in ("work", "stack", "trail"):
        f.set(acc.field(quantity), _zero(L))
    f.set(acc.field("flow"), _const(L, counter(1)))

    with f.if_(head.field("op") == L.Op.OpSplit):
        # An optional item: one split whose arms are the body and what follows,
        # in whichever order the greediness asks for.
        greedy = tmp(
            f,
            boolean,
            land(head.field("arg") == lo + u32(1), head.field("alt") == hi),
        )
        lazy = tmp(
            f,
            boolean,
            land(head.field("arg") == hi, head.field("alt") == lo + u32(1)),
        )
        with f.if_(lnot(lor(greedy, lazy))):
            f.ret(L.Cr.CrShape)
        _body(f, L, lo + u32(1), hi, cursor, acc, over, verdict)
        one = _const(L, counter(1))
        f.set(acc.field("work"), _plus(f, L, acc.field("work"), one, over))
        f.set(acc.field("stack"), _plus(f, L, acc.field("stack"), one, over))
        # Skipping the body is a way out of the region too.
        f.set(acc.field("flow"), _plus(f, L, acc.field("flow"), one, over))
        f.ret(L.Cr.CrOk)

    with f.if_(head.field("op") != L.Op.OpRepZero):
        f.ret(L.Cr.CrShape)
    # A counted repetition: the counter is zeroed, the head decides whether to
    # go round again, the body is entered, and the tail counts and jumps back.
    with f.if_(hi - lo < u32(4)):
        f.ret(L.Cr.CrShape)
    which = f.let("which", u32, head.field("arg"))
    with f.if_(which >= f["reps"].len()):
        f.ret(L.Cr.CrShape)
    for offset, op in ((1, L.Op.OpRepLoop), (2, L.Op.OpRepEnter)):
        inst = tmp(f, L.Inst, code.at(lo + u32(offset)))
        with f.if_(lor(inst.field("op") != op, inst.field("arg") != which)):
            f.ret(L.Cr.CrShape)
    tail = f.let("tail", L.Inst, code.at(hi - u32(1)))
    with f.if_(
        lor(tail.field("op") != L.Op.OpRepNext, tail.field("arg") != which)
    ):
        f.ret(L.Cr.CrShape)
    rep = f.let("rep", L.Rep, f["reps"].at(which))
    # The repetition the code names has to be the one that drives this range,
    # or the iteration count below would be read off some other quantifier.
    # Between the four opcodes and these three offsets there is nothing left
    # for a region to choose, which is why a repeat needs no witness field
    # beyond its range (BOUNDS.md section 4).
    with f.if_(
        lor(
            rep.field("head") != lo + u32(1),
            lor(rep.field("body") != lo + u32(2), rep.field("after") != hi),
        )
    ):
        f.ret(L.Cr.CrShape)

    _body(f, L, lo + u32(3), hi - u32(1), cursor, acc, over, verdict)

    # The body's ambiguity is what one iteration hands the next, so the flow
    # through the head is its powers summed. A body that grows more ambiguous
    # with the subject raises that to a power of n, and no closed form here has
    # that shape — an honest refusal rather than a bound nobody can write down.
    branching = f.let("branching", L.Poly, acc.field("flow"))
    with f.if_(lnot(_flat(branching))):
        f.ret(L.Cr.CrAmbiguous)
    ways = f.let("ways", counter, branching.field("c0"))

    bounded = f.let("bounded", boolean, rep.field("hi") != u32(spec.NONE))
    ceiling = f.let("ceiling", counter, rep.field("lo").cast(counter))
    with f.if_(land(bounded, rep.field("hi").cast(counter) > ceiling)):
        f.set(ceiling, rep.field("hi").cast(counter))
    # Bounded above, the count is what stops it. Unbounded, the empty-match
    # rule is: past the minimum, an iteration that consumed nothing is the last
    # one, so all but the first `lo` of them eat a byte.
    #
    # One more than either, because what is counted here is passes through the
    # head rather than iterations, and the pass that finds the count spent is
    # a pass: it reads the counter, decides, and leaves.
    rounds = f.let("rounds", L.Poly, _const(L, ceiling + counter(1)))
    with f.if_(lnot(bounded)):
        f.set(
            rounds,
            _poly(L, c0=rep.field("lo").cast(counter) + counter(1), c1=counter(1)),
        )

    flow = f.let("flow", L.Poly, rounds)
    with f.if_(ways > counter(1)):
        exponent = tmp(f, counter, ceiling + counter(1))
        with f.if_(lnot(bounded)):
            f.set(exponent, rep.field("lo").cast(counter) + counter(2))
        raised = tmp(f, L.Bound)
        f.call("bound_pow", [ways, exponent], dest=raised)
        with f.if_(lnot(raised.field("ok"))):
            f.set(over, boolean(True))
        f.set(flow, _const(L, raised.field("value")))
        with f.if_(lnot(bounded)):
            f.set(flow, _poly(L, base=ways, c0=raised.field("value")))

    body = f.let("body", L.Acc, acc)
    per = f.let("per", L.Poly, _const(L, ways))
    one = _const(L, counter(1))

    # One pass through the head costs the head itself, the enter, the body, and
    # one tail per way the body found to finish. Zeroing the counter happens
    # once however many passes there are, which is the constant outside.
    each = _plus(f, L, _const(L, counter(2)), _plus(f, L, body.field("work"), per, over), over)
    f.set(acc.field("work"), _plus(f, L, one, _times(f, L, flow, each, over), over))

    # The head forks at most once a pass.
    forks = _plus(f, L, one, body.field("stack"), over)
    f.set(acc.field("stack"), _times(f, L, flow, forks, over))

    # The enter remembers a position and every tail counts, both through the
    # trail, and the zeroing outside is on the trail too.
    writes = _plus(f, L, _plus(f, L, one, per, over), body.field("trail"), over)
    f.set(acc.field("trail"), _plus(f, L, one, _times(f, L, flow, writes, over), over))

    # Leaving happens at the head, when the count is spent, and at the tail,
    # when an empty iteration ends it.
    f.set(acc.field("flow"), _times(f, L, flow, _plus(f, L, one, per, over), over))
    f.ret(L.Cr.CrOk)


def _check(L: Layout) -> None:
    """Does this certificate bound this program?

    Every answer is one named reason rather than a bare false, because a
    rejection nobody can read is a rejection nobody will believe.
    """
    f = L.func(
        "cert_check",
        params=[("re", L.Re), ("config", L.Cfg), ("cert", L.Cert)],
        ret=L.Cr,
    )
    re = f["re"]
    cert = f["cert"]
    over = f.let("over", boolean, boolean(False))

    # The Pike VM and the memoized path charge differently enough that
    # borrowing these rules for them would be a guess, so they wait for their
    # own (DESIGN.md section 5, M5 and M9).
    with f.if_(f["config"] != L.Cfg.CfgBacktrack):
        f.ret(L.Cr.CrNoRules)
    with f.if_(cert.field("config") != f["config"]):
        f.ret(L.Cr.CrConfig)

    code = f.let("code", L.FrozenCode, re.field("code"))
    regions = f.let("regions", L.FrozenRegions, cert.field("regions"))
    total = f.let("total", u32, regions.len())
    with f.if_(total == u32(0)):
        f.ret(L.Cr.CrNoRegions)

    root = f.let("root", L.Region, regions.at(u32(0)))
    with f.if_(root.field("kind") != L.Rk.RkRoot):
        f.ret(L.Cr.CrRootKind)
    with f.if_(root.field("parent") != u32(spec.NONE)):
        f.ret(L.Cr.CrRootParent)
    with f.if_(lor(root.field("lo") != u32(0), root.field("hi") != code.len())):
        f.ret(L.Cr.CrRootRange)

    # Where the last child of each region ended, so that one pass settles both
    # halves of the sibling rule: children arrive in index order, and their
    # ranges do not overlap. A region starts out as its own `lo`, which makes
    # the first child's test the containment test and needs no special case.
    #
    # Requiring the order is deliberate rather than incidental. The compiler
    # emits regions as it flattens the AST, which is already source order, so
    # the rule costs a correct analyzer nothing and saves the checker a sort.
    ends = f.let("ends", L.Marks)
    kids = f.let("kids", L.Marks)
    sibs = f.let("sibs", L.Marks)
    i = f.let("i", u32, u32(0))
    with f.while_(i < total, down(total, i)):
        f.push(ends, regions.at(i).field("lo"))
        f.push(kids, u32(spec.NONE))
        f.push(sibs, u32(spec.NONE))
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

    # A base of zero is 0^n, which is 1 at n = 0 and 0 everywhere else. No
    # bound has that shape, and letting one through would make a claim that
    # vanishes on longer subjects look like a claim that holds.
    for quantity in ("cost", "stack", "mem"):
        with f.if_(cert.field(quantity).field("base") == counter(0)):
            f.ret(L.Cr.CrBase)
    f.set(i, u32(0))
    with f.while_(i < total, down(total, i)):
        claimed = tmp(f, L.Region, regions.at(i))
        for quantity in ("work", "outs", "stack", "trail"):
            with f.if_(claimed.field(quantity).field("base") == counter(0)):
                f.ret(L.Cr.CrBase)
        f.set(i, i + u32(1))

    # The children of each region, in the order their code appears. Walking
    # backwards means each one is put at the front of a list that ends up in
    # index order, which the sibling rule above has already tied to code order.
    f.set(i, total)
    with f.while_(i > u32(1), i.cast(counter)):
        f.set(i, i - u32(1))
        parent = tmp(f, u32, regions.at(i).field("parent"))
        f.set(sibs.at(i), kids.at(parent))
        f.set(kids.at(parent), i)

    # Each region is priced from what its children claim, so the induction that
    # makes the whole tree sound is one step deep and entirely local, and the
    # order regions are visited in does not enter into it. Outermost first is
    # the one that answers a badly built tree with what is wrong with the tree
    # rather than with the first number that came out too small.
    f.set(i, u32(0))
    with f.while_(i < total, down(total, i)):
        one = tmp(f, L.Region, regions.at(i))
        acc = tmp(f, L.Acc)
        cursor = tmp(f, u32, kids.at(i))
        verdict = tmp(f, L.Cr, L.Cr.CrOk)
        with f.switch(one.field("kind")) as arm:
            for name in ("RkRoot", "RkGroup", "RkBranch"):
                with arm.case(name):
                    for quantity in ("work", "stack", "trail"):
                        f.set(acc.field(quantity), _zero(L))
                    f.set(acc.field("flow"), _const(L, counter(1)))
                    f.call(
                        "scan_span",
                        [
                            code,
                            regions,
                            inout(sibs),
                            one.field("lo"),
                            one.field("hi"),
                            inout(cursor),
                            inout(acc),
                            inout(over),
                        ],
                        dest=verdict,
                    )
                    with f.if_(land(verdict == L.Cr.CrOk, cursor != u32(spec.NONE))):
                        f.set(verdict, L.Cr.CrChildren)
            with arm.case("RkAlt"):
                f.call(
                    "scan_alt",
                    [
                        code,
                        regions,
                        inout(kids),
                        inout(sibs),
                        i,
                        inout(acc),
                        inout(over),
                    ],
                    dest=verdict,
                )
            with arm.case("RkRepeat"):
                f.call(
                    "scan_repeat",
                    [
                        code,
                        re.field("reps"),
                        regions,
                        inout(kids),
                        inout(sibs),
                        i,
                        inout(acc),
                        inout(over),
                    ],
                    dest=verdict,
                )
        with f.if_(verdict != L.Cr.CrOk):
            f.ret(verdict)
        # Before the comparison rather than after it: a requirement that
        # stopped at the cap is one a certificate would be found to satisfy.
        with f.if_(over):
            f.ret(L.Cr.CrOverflow)
        holds = tmp(f, boolean, boolean(False))
        for quantity, needed, refusal in (
            ("work", "work", L.Cr.CrRegionWork),
            ("outs", "flow", L.Cr.CrRegionOuts),
            ("stack", "stack", L.Cr.CrRegionStack),
            ("trail", "trail", L.Cr.CrRegionTrail),
        ):
            f.call("poly_ge", [one.field(quantity), acc.field(needed)], dest=holds)
            with f.if_(lnot(holds)):
                f.ret(refusal)
        f.set(i, i + u32(1))

    # What a whole call costs, on top of what the tree prices. The register
    # file and the ovector are sized and zeroed once, a match copies the
    # ovector back out once, every starting position pays for clearing the
    # registers again, and the two growing arrays are charged for the buffers
    # they hold and the ones they held while copying.
    novec = f.let(
        "novec", counter, (re.field("ncap").cast(counter) + counter(1)) * counter(2)
    )
    setup = f.let(
        "setup", counter, (re.field("nregs").cast(counter) + novec) * counter(4)
    )
    deliver = f.let("deliver", counter, novec * counter(4))
    reset = f.let("reset", counter, re.field("nregs").cast(counter) * counter(4))

    capacity = f.let("capacity", L.Poly, _zero(L))
    scratch = f.let("scratch", L.Poly, _zero(L))
    for quantity, esize in (("stack", spec.BT_SIZE), ("trail", spec.UNDO_SIZE)):
        claimed = tmp(f, L.Poly, root.field(quantity))
        f.set(capacity, _zero(L))
        # The growth schedule doubles from four, so a run that holds at most k
        # entries never reserves more than 2k of them, and one that never
        # pushes never allocates at all.
        with f.if_(lnot(_nothing(claimed))):
            doubled = _times(f, L, claimed, _const(L, counter(2)), over)
            f.set(capacity, _plus(f, L, _const(L, counter(4)), doubled, over))
        weighed = _times(f, L, capacity, _const(L, counter(esize)), over)
        f.set(scratch, _plus(f, L, scratch, weighed, over))

    # An undo entry put back costs four units, and one can only be put back if
    # something recorded it, so the trail bound prices the replay too.
    replay = _times(f, L, root.field("trail"), _const(L, counter(4)), over)
    attempt = _plus(
        f, L, _const(L, reset), _plus(f, L, root.field("work"), replay, over), over
    )
    cost = _plus(
        f,
        L,
        _const(L, setup + deliver),
        _plus(
            f,
            L,
            _times(f, L, attempt, _step(L), over),
            _times(f, L, scratch, _const(L, counter(3)), over),
            over,
        ),
        over,
    )
    memory = _plus(
        f, L, _const(L, setup), _times(f, L, scratch, _const(L, counter(2)), over), over
    )

    holds = f.let("holds", boolean, boolean(False))
    with f.if_(over):
        f.ret(L.Cr.CrOverflow)
    for claim, needed, refusal in (
        ("cost", cost, L.Cr.CrTotalCost),
        ("stack", root.field("stack"), L.Cr.CrTotalStack),
        ("mem", memory, L.Cr.CrTotalMem),
    ):
        f.call("poly_ge", [cert.field(claim), needed], dest=holds)
        with f.if_(lnot(holds)):
            f.ret(refusal)

    # The one claim in a certificate that is not a number, held to the shape it
    # names: linear means the cost really is at most c * (n + 1), so no growing
    # base and no power above the first. Classification soundness is a Layer A
    # obligation (DESIGN.md section 6), and this is the part of it the checker
    # can settle by looking.
    with f.if_(cert.field("complexity") == L.Cc.CcLinear):
        shape = tmp(f, L.Poly, cert.field("cost"))
        test = shape.field("base") != counter(1)
        for degree in DEGREES[2:]:
            test = lor(test, shape.field(f"c{degree}") != counter(0))
        with f.if_(test):
            f.ret(L.Cr.CrNotLinear)
    f.ret(L.Cr.CrOk)
