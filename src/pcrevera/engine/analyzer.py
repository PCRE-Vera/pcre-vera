"""The bound-certificate analyzer for the backtracking configuration.

The other half of the split DESIGN.md section 5 draws. `certificate.py` reads a
claimed price back against the bytecode and refuses it if it is short; this
searches for a price to claim in the first place. It is untrusted, and it is
untrusted in the way that matters: compilation runs the checker over what comes
out of here before any of it is stored, so a bug in this file can lose a bound
and cannot invent one.

Which is why the composition below is written out again rather than shared with
the checker. Both state the rules of BOUNDS.md section 4, and both count in the
arithmetic of `bounds.py`, but a single implementation of the recurrence would
make the checker's verdict a restatement of the analyzer's own opinion. What
they do share is the cost model, deliberately: DESIGN.md section 5 asks for one
model behind the analyzer, both matchers and the Lean accounting.

The walk is the tree in reverse emission order. The compiler emits a region
before its children, so counting down from the end reaches every child before
its parent, and a region is priced from prices that are already there. That is
the same induction the checker walks and the same one Layer A will.

There are two answers other than a certificate, and they are different in kind.
A pattern whose ambiguity grows with the subject, or whose numbers run past
what a counter holds, has no bound of the shape section 2 can write down: that
is `ArAmbiguous` or `ArOverflow`, the pattern compiles, and the accessors
report ExceedsBudget. `ArShape` is not that. It means this file met something
in the tree it had no rule for, which for a tree the compiler emitted is a bug
of ours and is reported as one.

`ArOk` is not a claim that the tree was well formed. This file stops only where
it would otherwise have to guess or read past the end of the program; deciding
whether a tree describes the bytecode is the checker's whole job, and a
malformed one may well be priced here and refused there. That refusal is a bug
of ours too, and compilation says so rather than dropping the bound.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, land, lnot, lor, u32
from . import spec
from .bounds import (
    SIMPLE_OPS,
    bump,
    const,
    flat,
    fresh,
    linear,
    nothing,
    plus,
    poly,
    step,
    times,
    zero,
)
from .layout import Layout
from .parser import down, tmp


def build(L: Layout) -> None:
    _span(L)
    _alt(L)
    _repeat(L)
    _whole(L)
    _search(L)
    _install(L)


def _install(L: Layout) -> None:
    """Price a finished program, and say whether the answer may be kept.

    The whole of the resource analysis as compilation sees it, which is one
    phase rather than three calls: the tree, then the search, then the check.
    Order is the point. Whether the tree describes the bytecode is a question
    about the program, with the same answer whether or not the rules can price
    it, so it is asked first and on its own — otherwise a compiler that emitted
    a bad tree would go unreported for exactly the patterns the analyzer gives
    up on.

    `CrOk` with the flag down is the honest "no bound of a shape this
    arithmetic can write down": the pattern is fine and the accessors report
    ExceedsBudget. Anything else means the two halves of BOUNDS.md disagree
    about one program, which no pattern can cause and only a bug of ours can.
    """
    f = L.func(
        "cert_install",
        params=[
            ("re", L.Re),
            ("cert", L.Cert, "inout"),
            ("has", boolean, "inout"),
            ("pcert", L.Cert, "inout"),
            ("haspike", boolean, "inout"),
        ],
        ret=L.Cr,
    )
    f.set(f["has"], boolean(False))
    f.set(f["haspike"], boolean(False))
    shape = f.let("shape", L.Cr, L.Cr.CrOk)
    f.call("cert_shape", [f["re"]], dest=shape)
    with f.if_(shape != L.Cr.CrOk):
        f.ret(shape)

    # The Pike configuration first, on the patterns routed to it: its closed
    # form either fits counter arithmetic or there is honestly no certificate,
    # and a checker refusing what the pricer just built is the same
    # two-halves-disagreeing bug as on the backtracking side.
    with f.if_(f["re"].field("pike")):
        priced = tmp(f, boolean, boolean(False))
        f.call("pike_price", [f["re"], inout(f["pcert"])], dest=priced)
        with f.if_(priced):
            pv = tmp(f, L.Cr, L.Cr.CrOk)
            f.call(
                "cert_check", [f["re"], L.Cfg.CfgPike, f["pcert"]], dest=pv
            )
            with f.if_(pv != L.Cr.CrOk):
                f.ret(pv)
            f.set(f["haspike"], boolean(True))

    found = f.let("found", L.Ar, L.Ar.ArShape)
    f.call("cert_build", [f["re"], inout(f["cert"])], dest=found)
    with f.if_(found == L.Ar.ArShape):
        # The analyzer met something in the compiler's own tree that it had no
        # rule for, which `cert_shape` has just said there is none of.
        f.ret(L.Cr.CrShape)
    with f.if_(found != L.Ar.ArOk):
        f.ret(L.Cr.CrOk)

    verdict = f.let("verdict", L.Cr, L.Cr.CrOk)
    f.call("cert_check", [f["re"], L.Cfg.CfgBacktrack, f["cert"]], dest=verdict)
    with f.if_(verdict != L.Cr.CrOk):
        f.ret(verdict)
    f.set(f["has"], boolean(True))
    f.ret(L.Cr.CrOk)


def _blank(L: Layout):
    """A price that claims nothing, which is what a slot holds until it is filled.

    Written out rather than left to the zero value, because the zero of a
    `Poly` names a growth base of zero and no bound has that shape.
    """
    return L.Price.of(work=zero(L), outs=zero(L), stack=zero(L), trail=zero(L))


def _span(L: Layout) -> None:
    """BOUNDS.md section 4.1: read the range left to right, carrying the flow."""
    f = L.func(
        "price_span",
        params=[
            ("code", L.FrozenCode),
            ("regions", L.FrozenRegions),
            ("prices", L.Prices, "inout"),
            ("sibs", L.Marks, "inout"),
            ("lo", u32),
            ("hi", u32),
            ("first", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Ar,
    )
    code = f["code"]
    regions = f["regions"]
    acc = f["acc"]
    over = f["over"]
    cursor = f.let("cursor", u32, f["first"])
    pc = f.let("pc", u32, f["lo"])

    with f.while_(pc < f["hi"], down(f["hi"], pc)):
        at = tmp(f, u32, cursor)
        with f.if_(at != u32(spec.NONE)):
            kid = tmp(f, L.Region, regions.at(at))
            with f.if_(kid.field("lo") == pc):
                # The walk has to leave this instruction behind, or it would
                # meet the same child for ever. The compiler drops a region
                # that covers nothing rather than emitting one, so meeting one
                # here is the tree failing to describe the program.
                with f.if_(kid.field("hi") <= pc):
                    f.ret(L.Ar.ArShape)
                priced = tmp(f, L.Price, f["prices"].at(at))
                flow = tmp(f, L.Poly, acc.field("flow"))
                for quantity in ("work", "stack", "trail"):
                    bump(
                        f,
                        L,
                        acc,
                        quantity,
                        times(f, L, flow, priced.field(quantity), over),
                        over,
                    )
                f.set(acc.field("flow"), times(f, L, flow, priced.field("outs"), over))
                f.set(pc, kid.field("hi"))
                f.set(cursor, f["sibs"].at(at))
                f.cont()

        visited = plus(f, L, acc.field("work"), acc.field("flow"), over)
        with f.switch(code.at(pc).field("op")) as arm:
            for name in SIMPLE_OPS:
                with arm.case(name):
                    f.set(acc.field("work"), visited)
            with arm.case("OpSave"):
                f.set(acc.field("work"), visited)
                bump(f, L, acc, "trail", acc.field("flow"), over)
            with arm.case("OpAccept"):
                # A match ends the attempt, so nothing after this point is
                # reached by way of it.
                f.set(acc.field("work"), visited)
                f.set(acc.field("flow"), zero(L))
            with arm.otherwise():
                f.ret(L.Ar.ArShape)
        f.set(pc, pc + u32(1))
    f.ret(L.Ar.ArOk)


def _alt(L: Layout) -> None:
    """BOUNDS.md section 4.2: every branch is entered, and all but the last jump.

    The shape of the splits and the jumps is the checker's business. What this
    needs from the code is nothing at all: an alternation costs what its
    branches cost, plus the fork before each of them and the jump after.
    """
    f = L.func(
        "price_alt",
        params=[
            ("prices", L.Prices, "inout"),
            ("sibs", L.Marks, "inout"),
            ("first", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Ar,
    )
    acc = f["acc"]
    over = f["over"]
    # One price per region, so this is the region count, and it is only here to
    # bound the walk: the chain of siblings is what it really follows.
    total = f.let("total", u32, f["prices"].len())
    c = f.let("c", u32, f["first"])
    k = f.let("k", u32, u32(0))
    fresh(f, L, acc, zero(L))

    with f.while_(land(k < total, c != u32(spec.NONE)), down(total, k)):
        priced = tmp(f, L.Price, f["prices"].at(c))
        nxt = tmp(f, u32, f["sibs"].at(c))
        with f.if_(nxt != u32(spec.NONE)):
            # The split is visited once, and the jump that closes the branch
            # once per way the branch found to succeed.
            extra = plus(f, L, const(L, counter(1)), priced.field("outs"), over)
            bump(f, L, acc, "work", extra, over)
            bump(f, L, acc, "stack", const(L, counter(1)), over)
        for quantity, came in (
            ("work", "work"),
            ("stack", "stack"),
            ("trail", "trail"),
            ("flow", "outs"),
        ):
            bump(f, L, acc, quantity, priced.field(came), over)
        f.set(c, nxt)
        f.set(k, k + u32(1))
    f.ret(L.Ar.ArOk)


def _inside(f, L: Layout, lo, hi) -> None:
    """Price the span a repetition repeats, and give up if it does not price."""
    f.call(
        "price_span",
        [
            f["code"],
            f["regions"],
            inout(f["prices"]),
            inout(f["sibs"]),
            lo,
            hi,
            f["first"],
            inout(f["acc"]),
            inout(f["over"]),
        ],
        dest=f["verdict"],
    )
    with f.if_(f["verdict"] != L.Ar.ArOk):
        f.ret(f["verdict"])


def _repeat(L: Layout) -> None:
    """BOUNDS.md sections 4.3 and 4.4: an optional item, or a counted repetition."""
    f = L.func(
        "price_repeat",
        params=[
            ("code", L.FrozenCode),
            ("reps", L.FrozenReps),
            ("regions", L.FrozenRegions),
            ("prices", L.Prices, "inout"),
            ("sibs", L.Marks, "inout"),
            ("at", u32),
            ("first", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Ar,
    )
    code = f["code"]
    acc = f["acc"]
    over = f["over"]
    here = f.let("here", L.Region, f["regions"].at(f["at"]))
    lo = f.let("lo", u32, here.field("lo"))
    hi = f.let("hi", u32, here.field("hi"))
    with f.if_(hi <= lo):
        f.ret(L.Ar.ArShape)
    verdict = f.let("verdict", L.Ar, L.Ar.ArOk)
    head = f.let("head", L.Inst, code.at(lo))
    fresh(f, L, acc, const(L, counter(1)))

    with f.if_(head.field("op") == L.Op.OpSplit):
        _inside(f, L, lo + u32(1), hi)
        one = const(L, counter(1))
        bump(f, L, acc, "work", one, over)
        bump(f, L, acc, "stack", one, over)
        # Skipping the body is a way out of the region too.
        bump(f, L, acc, "flow", one, over)
        f.ret(L.Ar.ArOk)

    with f.if_(head.field("op") != L.Op.OpRepZero):
        f.ret(L.Ar.ArShape)
    with f.if_(hi - lo < u32(4)):
        f.ret(L.Ar.ArShape)
    which = f.let("which", u32, head.field("arg"))
    with f.if_(which >= f["reps"].len()):
        f.ret(L.Ar.ArShape)
    rep = f.let("rep", L.Rep, f["reps"].at(which))

    _inside(f, L, lo + u32(3), hi - u32(1))

    # What one iteration hands the next. A body that grows more ambiguous with
    # the subject would raise a polynomial to a power of n, and no bound of the
    # shape BOUNDS.md section 2 writes down has that form.
    branching = f.let("branching", L.Poly, acc.field("flow"))
    with f.if_(lnot(flat(branching))):
        f.ret(L.Ar.ArAmbiguous)
    ways = f.let("ways", counter, branching.field("c0"))

    bounded = f.let("bounded", boolean, rep.field("hi") != u32(spec.NONE))
    ceiling = f.let("ceiling", counter, rep.field("lo").cast(counter))
    with f.if_(land(bounded, rep.field("hi").cast(counter) > ceiling)):
        f.set(ceiling, rep.field("hi").cast(counter))
    # Passes through the head, which is one more than the iteration count: the
    # pass that finds the count spent reads the counter, decides, and leaves.
    # Bounded above, the declared maximum is what stops it; unbounded, the
    # empty-match rule does, since past the minimum an iteration that consumed
    # nothing is the last one.
    rounds = f.let("rounds", L.Poly, const(L, ceiling + counter(1)))
    with f.if_(lnot(bounded)):
        f.set(
            rounds,
            poly(L, c0=rep.field("lo").cast(counter) + counter(1), c1=counter(1)),
        )

    flow = f.let("flow", L.Poly, rounds)
    with f.if_(ways > counter(1)):
        exponent = tmp(f, counter, ceiling + counter(1))
        with f.if_(lnot(bounded)):
            f.set(exponent, rep.field("lo").cast(counter) + counter(2))
        raised = tmp(f, L.Bound)
        f.call("bound_pow", [ways, exponent], dest=raised)
        with f.if_(lnot(raised.field("ok"))):
            f.ret(L.Ar.ArOverflow)
        f.set(flow, const(L, raised.field("value")))
        with f.if_(lnot(bounded)):
            f.set(flow, poly(L, base=ways, c0=raised.field("value")))

    body = f.let("body", L.Acc, acc)
    per = f.let("per", L.Poly, const(L, ways))
    one = const(L, counter(1))

    # One pass through the head costs the head itself, the enter, the body, and
    # one tail per way the body found to finish. Zeroing the counter happens
    # once however many passes there are, which is the constant outside.
    each = plus(
        f, L, const(L, counter(2)), plus(f, L, body.field("work"), per, over), over
    )
    f.set(acc.field("work"), plus(f, L, one, times(f, L, flow, each, over), over))

    # The head forks at most once a pass.
    forks = plus(f, L, one, body.field("stack"), over)
    f.set(acc.field("stack"), times(f, L, flow, forks, over))

    # The enter remembers a position and every tail counts, both through the
    # trail, and the zeroing outside is on the trail too.
    leaves = f.let("leaves", L.Poly, plus(f, L, one, per, over))
    writes = plus(f, L, leaves, body.field("trail"), over)
    f.set(acc.field("trail"), plus(f, L, one, times(f, L, flow, writes, over), over))

    # Leaving happens at the head, when the count is spent, and at the tail,
    # when an empty iteration ends it.
    f.set(acc.field("flow"), times(f, L, flow, leaves, over))
    f.ret(L.Ar.ArOk)


def _whole(L: Layout) -> None:
    """BOUNDS.md section 5: what a call pays on top of the tree.

    The register file and the ovector are sized and zeroed once, a match copies
    the ovector back out once, every starting position pays for clearing the
    registers again, and the two growing arrays are charged for the buffers
    they hold and the ones they held while copying.
    """
    f = L.func(
        "price_call",
        params=[
            ("re", L.Re),
            ("whole", L.Price),
            ("cert", L.Cert, "inout"),
            ("over", boolean, "inout"),
        ],
    )
    re = f["re"]
    whole = f["whole"]
    cert = f["cert"]
    over = f["over"]
    novec = f.let(
        "novec", counter, (re.field("ncap").cast(counter) + counter(1)) * counter(2)
    )
    setup = f.let(
        "setup",
        counter,
        (re.field("nregs").cast(counter) + novec) * counter(spec.REG_SIZE),
    )
    deliver = f.let("deliver", counter, novec * counter(spec.REG_SIZE))
    reset = f.let(
        "reset", counter, re.field("nregs").cast(counter) * counter(spec.REG_SIZE)
    )

    capacity = f.let("capacity", L.Poly)
    scratch = f.let("scratch", L.Poly, zero(L))
    for quantity, esize in (("stack", spec.BT_SIZE), ("trail", spec.UNDO_SIZE)):
        held = tmp(f, L.Poly, whole.field(quantity))
        f.set(capacity, zero(L))
        # The growth schedule doubles from its floor, so a run that holds at
        # most k entries never reserves more than twice that, and one that
        # never pushes never allocates at all.
        with f.if_(lnot(nothing(held))):
            grown = times(f, L, held, const(L, counter(spec.GROW_FACTOR)), over)
            f.set(capacity, plus(f, L, const(L, counter(spec.GROW_MIN)), grown, over))
        weighed = times(f, L, capacity, const(L, counter(esize)), over)
        f.set(scratch, plus(f, L, scratch, weighed, over))

    # An undo entry put back costs one unit per IR byte of the register, and
    # one can only be put back if something recorded it, so the trail bound
    # prices the replay too.
    replay = times(f, L, whole.field("trail"), const(L, counter(spec.REG_SIZE)), over)
    attempt = plus(
        f, L, const(L, reset), plus(f, L, whole.field("work"), replay, over), over
    )
    # The 3 and the 2 below are the two bounds BOUNDS.md section 5 derives from
    # the growth schedule rather than numbers the matcher holds: the buffers a
    # doubling run allocates come to twice its final reservation and the ones
    # it copies out of to one more, and holding both at once is what makes the
    # memory peak twice the reservation.
    positions = times(f, L, attempt, step(L), over)
    growth = times(f, L, scratch, const(L, counter(3)), over)
    f.set(
        cert.field("cost"),
        plus(
            f, L, const(L, setup + deliver), plus(f, L, positions, growth, over), over
        ),
    )
    f.set(cert.field("stack"), whole.field("stack"))
    f.set(cert.field("trail"), whole.field("trail"))
    # The delivered answer is resident too: a caller holds the copied-out
    # ovector alongside the scratch, and a context materializes that store
    # at creation, so the memory bound pays for it.
    f.set(
        cert.field("mem"),
        plus(
            f,
            L,
            const(L, setup + deliver),
            times(f, L, scratch, const(L, counter(2)), over),
            over,
        ),
    )


def _search(L: Layout) -> None:
    f = L.func(
        "cert_build", params=[("re", L.Re), ("cert", L.Cert, "inout")], ret=L.Ar
    )
    re = f["re"]
    cert = f["cert"]
    over = f.let("over", boolean, boolean(False))
    regions = f.let("regions", L.FrozenRegions, re.field("regions"))
    total = f.let("total", u32, regions.len())
    with f.if_(total == u32(0)):
        f.ret(L.Ar.ArShape)

    prices = f.let("prices", L.Prices)
    kids = f.let("kids", L.Marks)
    sibs = f.let("sibs", L.Marks)
    stop = f.let("stop", u32, re.field("code").len())
    i = f.let("i", u32, u32(0))
    with f.while_(i < total, down(total, i)):
        # Every range is inside the program. That is not the tree being
        # validated — deciding whether a tree describes a program is the
        # checker's whole job, and doing it twice would be the duplication this
        # split exists to avoid. It is the one thing that has to be settled
        # before anything below indexes the bytecode, because this file is
        # untrusted in both directions: it may not be believed, and it may not
        # read past the end of the code on the way to being disbelieved.
        one = tmp(f, L.Region, regions.at(i))
        with f.if_(lor(one.field("lo") > one.field("hi"), one.field("hi") > stop)):
            f.ret(L.Ar.ArShape)
        # And reverse emission order is only an induction if every parent
        # really does come before its child. It is the compiler that promises
        # so, and `region_kids` below is written to that promise.
        with f.if_(land(i > u32(0), one.field("parent") >= i)):
            f.ret(L.Ar.ArShape)
        f.push(prices, _blank(L))
        f.set(i, i + u32(1))

    f.call("region_kids", [regions, inout(kids), inout(sibs)])

    f.set(i, total)
    with f.while_(i > u32(0), i.cast(counter)):
        f.set(i, i - u32(1))
        one = tmp(f, L.Region, regions.at(i))
        acc = tmp(f, L.Acc)
        first = tmp(f, u32, kids.at(i))
        # A switch that covers its enum may carry no default (TIR-SPEC.md rule
        # V-032). This one needs none for the tree the compiler emits, and
        # starting at a refusal is what a caller of the generated module who
        # made a kind up gets instead of a region priced at nothing.
        verdict = tmp(f, L.Ar, L.Ar.ArShape)
        with f.switch(one.field("kind")) as arm:
            for name in ("RkRoot", "RkGroup", "RkBranch"):
                with arm.case(name):
                    fresh(f, L, acc, const(L, counter(1)))
                    f.call(
                        "price_span",
                        [
                            re.field("code"),
                            regions,
                            inout(prices),
                            inout(sibs),
                            one.field("lo"),
                            one.field("hi"),
                            first,
                            inout(acc),
                            inout(over),
                        ],
                        dest=verdict,
                    )
            with arm.case("RkAlt"):
                f.call(
                    "price_alt",
                    [inout(prices), inout(sibs), first, inout(acc), inout(over)],
                    dest=verdict,
                )
            with arm.case("RkRepeat"):
                f.call(
                    "price_repeat",
                    [
                        re.field("code"),
                        re.field("reps"),
                        regions,
                        inout(prices),
                        inout(sibs),
                        i,
                        first,
                        inout(acc),
                        inout(over),
                    ],
                    dest=verdict,
                )
        with f.if_(verdict != L.Ar.ArOk):
            f.ret(verdict)
        with f.if_(over):
            f.ret(L.Ar.ArOverflow)
        f.set(
            prices.at(i),
            L.Price.of(
                work=acc.field("work"),
                outs=acc.field("flow"),
                stack=acc.field("stack"),
                trail=acc.field("trail"),
            ),
        )

    root = f.let("root", L.Price, prices.at(u32(0)))
    f.call("price_call", [re, root, inout(cert), inout(over)])
    with f.if_(over):
        f.ret(L.Ar.ArOverflow)

    f.set(cert.field("config"), L.Cfg.CfgBacktrack)
    # Linear means the cost really is at most c * (n + 1), which for the
    # backtracking path is a thing to read off the bound rather than a thing to
    # decide about the pattern. The checker holds the claim to the same shape,
    # and to the same predicate.
    f.set(cert.field("complexity"), L.Cc.CcNotProvenLinear)
    with f.if_(linear(cert.field("cost"))):
        f.set(cert.field("complexity"), L.Cc.CcLinear)

    f.freeze(cert.field("prices"), prices)
    f.ret(L.Ar.ArOk)
