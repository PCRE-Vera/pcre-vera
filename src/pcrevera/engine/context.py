"""The preallocated match context, written in TIR.

DESIGN.md section 2.4 promises that a caller who plans ahead can pay for a
match before running one: name the longest subject there will be, and get back
an object that owns every byte a match on it could touch. This is that object.
Creation is the section 5 memory bound made physical, and it takes that number
from the accessor a caller would ask rather than computing it a second time:
`re_mem` at the declared length is what gets reserved, down to the byte. Each
scratch array is reserved at the growth schedule's final capacity for its own
term of the bound, the two result stores each wrapper materializes beside the
context are the ovector the run cores fill and the converted view a match
answers through, and the ballast is everything else the bound charges for —
the growth-overlap copy, and whatever the polynomial arithmetic of BOUNDS.md
section 2 rounds up when a bound has growth and carries its constants at the
larger base. A call on the context then allocates nothing: the run cores
truncate what is already there, and a push that stays under a reservation
never grows anything.

Both configurations are served, sized differently. A Pike-eligible pattern
needs capacities read straight off the program — the section 9 counts — and a
backtracking one needs the certificate's stack and trail claims evaluated at
the declared length, which is why those two claims are held to equality by the
checker: this file sizes real arrays from them while the memory bound was
priced from the same numbers, and any daylight between the two would have one
of them lying.

Creation answers in the outcome vocabulary of `match`, and the order of the
refusals is the frozen contract — the accessor's own order, since the accessor
is what is asked first. A configuration that is not the default and a length
past MAX_LENGTH are BadInput before anything else is looked at; a pattern
whose selected path carries no certificate, whose bound is past the section 3
byte ceiling, or whose arrays have no representable size, is the same
ExceedsBudget the accessors report; and a reservation the caller's memory
limit does not cover, or whose zeroing the cost limit does not pay for at one
unit per IR byte, is ResourceExceeded. The
limits handed to creation are also the baked ceilings: a call on the context
may lower the cost and stack limits and may not raise them, the configuration
cannot be changed, and a subject longer than the declared maximum is refused
— all BadInput, because they are requests the context was never sized for.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, lnot, u32
from . import spec
from .bounds import growth_cap, sat
from .layout import Layout
from .parser import tmp


def build(L: Layout) -> None:
    _create(L)
    _match(L)


def _create(L: Layout) -> None:
    f = L.func(
        "ctx_create",
        params=[
            ("re", L.Re),
            ("mcfg", u32),
            ("maxlen", u32),
            ("costlimit", counter),
            ("stacklimit", u32),
            ("memlimit", counter),
            ("ctx", L.Ctx, "inout"),
        ],
        ret=u32,
    )
    re = f["re"]
    ctx = f["ctx"]
    # First, so that a refused creation leaves a context that refuses to
    # match, whatever the slots held before.
    f.set(ctx.field("ready"), boolean(False))
    # What a call on a subject this long may hold, asked of the very accessor
    # a caller would ask. That is the point of DESIGN.md section 2.4's promise
    # that creation can be planned from the accessors: the reservation is
    # their number rather than a second computation of it that has to agree
    # with them. It brings creation's first two refusals with it, in the order
    # the contract fixes — a configuration this release cannot be asked about
    # and a length no subject can have are BadInput, a pattern with no
    # certificate on its selected path and a bound past the section 3 byte
    # ceiling are ExceedsBudget.
    answered = f.let("answered", L.Answer)
    f.call("re_mem", [re, f["mcfg"], f["maxlen"].cast(counter)], dest=answered)
    with f.if_(answered.field("status") != u32(spec.OK)):
        f.ret(answered.field("status"))
    resident = f.let("resident", counter, answered.field("value"))
    picked = f.let("picked", L.Cert)
    has = f.let("has", boolean, boolean(False))
    f.call("re_pick", [re, inout(picked)], dest=has)
    with f.if_(lnot(has)):
        f.ret(u32(spec.EXCEEDS_BUDGET))

    over = f.let("over", boolean, boolean(False))
    novec = f.let("novec", u32, (re.field("ncap") + u32(1)) * u32(2))
    # The delivered answer's share of the setup term: the memory bound pays
    # for the result store a caller holds, and the wrapper materializes it
    # beside the context.
    answer = f.let(
        "answer", counter, novec.cast(counter) * counter(spec.REG_SIZE)
    )

    # Every capacity, settled before anything is reserved, so a refusal
    # reserves nothing. The arrays of the path not selected stay at zero.
    setup = f.let("setup", counter, counter(0))
    ballast = f.let("ballast", counter, counter(0))
    nregs = f.let("nregs", u32, u32(0))
    cbt = f.let("cbt", counter, counter(0))
    ctrail = f.let("ctrail", counter, counter(0))
    clists = f.let("clists", counter, counter(0))
    cstk = f.let("cstk", counter, counter(0))
    ctab = f.let("ctab", counter, counter(0))
    cpool = f.let("cpool", counter, counter(0))
    words = f.let("words", u32, u32(0))

    with f.if_(re.field("pike")):
        # The section 9 capacities, from the one function that also prices
        # them: `pike_room` is what makes the certificate's memory bound and
        # this reservation the same number rather than two transcriptions.
        room = f.let("room", L.Room)
        f.call("pike_room", [re, inout(room), inout(over)])
        f.set(words, room.field("words"))
        f.set(clists, room.field("lists"))
        f.set(cstk, room.field("stk"))
        f.set(ctab, room.field("tables"))
        f.set(cpool, room.field("pool"))
        f.set(ballast, room.field("reserved"))
        f.set(
            setup,
            novec.cast(counter) * counter(spec.REG_SIZE) + words.cast(counter),
        )
    with f.else_():
        # The certificate's stack and trail claims at the declared length,
        # which the checker held to equality with the walk for exactly this
        # read: the two arrays are sized from the claims while the memory
        # bound was priced from the walk.
        deep = tmp(f, L.Bound)
        f.call("poly_value", [picked.field("stack"), f["maxlen"].cast(counter)], dest=deep)
        long = tmp(f, L.Bound)
        f.call("poly_value", [picked.field("trail"), f["maxlen"].cast(counter)], dest=long)
        with f.if_(lnot(deep.field("ok"))):
            f.ret(u32(spec.EXCEEDS_BUDGET))
        with f.if_(lnot(long.field("ok"))):
            f.ret(u32(spec.EXCEEDS_BUDGET))
        f.set(cbt, growth_cap(f, deep.field("value"), over))
        f.set(ctrail, growth_cap(f, long.field("value"), over))
        scratch = sat(f, "sat_mul", cbt, counter(spec.BT_SIZE), over)
        weighed = sat(f, "sat_mul", ctrail, counter(spec.UNDO_SIZE), over)
        f.set(scratch, sat(f, "sat_add", scratch, weighed, over))
        f.set(ballast, scratch)
        f.set(nregs, re.field("nregs"))
        f.set(setup, (nregs + novec).cast(counter) * counter(spec.REG_SIZE))

    # What the arrays themselves come to: the section 5 memory line without
    # the growth-overlap copy, since that is the one term no array holds.
    held = tmp(
        f,
        counter,
        sat(f, "sat_add", sat(f, "sat_add", setup, answer, over), ballast, over),
    )
    with f.if_(over):
        f.ret(u32(spec.EXCEEDS_BUDGET))
    # A bound that does not cover the arrays its own claims size is one no
    # context can be built from, since reserving the arrays would hold more
    # than the number the caller was told. The checker holds the stack and
    # trail claims to the walk the memory bound was priced from, so this is
    # unreachable rather than unlikely — and a refusal is what an unreachable
    # case is worth.
    with f.if_(held > resident):
        f.ret(u32(spec.EXCEEDS_BUDGET))
    with f.if_(resident > f["memlimit"]):
        f.ret(u32(spec.RESOURCE_EXCEEDED))
    # Zeroing the reservation is work, at one unit per IR byte, the same rate
    # every other zeroing in the engine charges.
    with f.if_(resident > f["costlimit"]):
        f.ret(u32(spec.RESOURCE_EXCEEDED))

    # Whatever context lived here before is replaced wholesale, capacity
    # included: `reserve` never shrinks (TIR-SPEC.md section 11.3), so
    # recreating a small context over a large one would otherwise keep the
    # large one's arrays and break the equality everything above just
    # established. Swapping the whole struct for a blank is the linear way
    # to let them go, covers any array a later change adds, and costs
    # nothing extra: every scalar field is written below.
    blank = f.let("blank", L.Ctx)
    f.swap(ctx, blank)

    f.reserve(ctx.field("regs"), nregs)
    f.reserve(ctx.field("bt"), cbt.cast(u32))
    f.reserve(ctx.field("trail"), ctrail.cast(u32))
    f.reserve(ctx.field("clist"), clists.cast(u32))
    f.reserve(ctx.field("nlist"), clists.cast(u32))
    f.reserve(ctx.field("stk"), cstk.cast(u32))
    f.reserve(ctx.field("seen"), words)
    f.reserve(ctx.field("rc"), ctab.cast(u32))
    f.reserve(ctx.field("free"), ctab.cast(u32))
    f.reserve(ctx.field("pool"), cpool.cast(u32))
    # The ballast, which is what makes the reservation the accessor's number
    # exactly: the growth-overlap copy the memory bound charges for, and
    # whatever the polynomial arithmetic of BOUNDS.md section 2 rounded up on
    # the way there — nothing at all when the bound has no growth, and a real
    # number of bytes when it does, since a constant added to an exponential
    # bound is carried at the larger base.
    f.reserve(ctx.field("slack"), (resident - held).cast(u32))

    f.set(ctx.field("re"), re)
    f.set(ctx.field("maxlen"), f["maxlen"])
    f.set(ctx.field("costcap"), f["costlimit"])
    f.set(ctx.field("stackcap"), f["stacklimit"])
    f.set(ctx.field("memcap"), resident)
    f.set(ctx.field("ready"), boolean(True))
    f.ret(u32(spec.OK))


def _match(L: Layout) -> None:
    f = L.func(
        "ctx_match",
        params=[
            ("ctx", L.Ctx, "inout"),
            ("subj", L.frozen_bytes),
            ("start", u32),
            ("mopts", u32),
            ("costlimit", counter),
            ("stacklimit", u32),
            ("ov", L.Ovec, "inout"),
            ("use", L.Usage, "inout"),
        ],
        ret=u32,
    )
    ctx = f["ctx"]
    f.set(f["use"].field("cost"), counter(0))
    f.set(f["use"].field("stack"), u32(0))
    f.set(f["use"].field("mem"), counter(0))
    with f.if_(lnot(ctx.field("ready"))):
        f.ret(u32(spec.BAD_INPUT))
    with f.if_(f["subj"].len() > ctx.field("maxlen")):
        f.ret(u32(spec.BAD_INPUT))
    # Lower is a caller spending less of what it already paid for; higher is
    # a budget the reservation was never sized against.
    with f.if_(f["costlimit"] > ctx.field("costcap")):
        f.ret(u32(spec.BAD_INPUT))
    with f.if_(f["stacklimit"] > ctx.field("stackcap")):
        f.ret(u32(spec.BAD_INPUT))
    out = tmp(f, u32, u32(spec.NO_MATCH))
    with f.if_(ctx.field("re").field("pike")):
        f.call(
            "pike_run",
            [
                ctx.field("re"),
                f["subj"],
                f["start"],
                f["mopts"],
                f["costlimit"],
                f["stacklimit"],
                ctx.field("memcap"),
                inout(ctx.field("clist")),
                inout(ctx.field("nlist")),
                inout(ctx.field("stk")),
                inout(ctx.field("seen")),
                inout(ctx.field("pool")),
                inout(ctx.field("rc")),
                inout(ctx.field("free")),
                inout(f["ov"]),
                inout(f["use"]),
            ],
            dest=out,
        )
    with f.else_():
        f.call(
            "bt_run",
            [
                ctx.field("re"),
                f["subj"],
                f["start"],
                f["mopts"],
                f["costlimit"],
                f["stacklimit"],
                ctx.field("memcap"),
                inout(ctx.field("regs")),
                inout(ctx.field("bt")),
                inout(ctx.field("trail")),
                inout(f["ov"]),
                inout(f["use"]),
            ],
            dest=out,
        )
    # The run cores report the transient peak a plain call would have
    # charged, and on a context that is not what the memory question means:
    # the reservation is resident for the call's whole life whatever the
    # subject was, which is the constant DESIGN.md section 2.4 pins the
    # context's memory component to.
    f.set(f["use"].field("mem"), ctx.field("memcap"))
    f.ret(out)
