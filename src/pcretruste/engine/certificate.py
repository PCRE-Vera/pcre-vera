"""The bound certificate checker, written in TIR.

DESIGN.md section 5 splits the resource analysis in two on purpose. An analyzer
searches for a bound certificate — one price per region of the compiler's tree
— and a deliberately small checker decides whether to believe it. The analyzer
needs no proof at all; the checker is what Lean's layer A proves sound, so an
accepted certificate really does bound the run. Proving a checker is far less
work than proving a search, and it is what keeps the analyzer mechanically
connectable to the proofs instead of drifting into a plausibility argument.

This is the checker half. `analyzer.py` is the other one, and the two share
`bounds.py` and nothing else: the arithmetic and the cost model are meant to be
one thing, and the composition is meant to be stated twice. The rules both
state are BOUNDS.md, which gives the cost of every opcode this engine emits and
the composition rule of every region kind, and is the document a reader should
have open beside this one. What is here is the transcription.

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

So what an accepted certificate says is the whole of it: for this program, in
this configuration, at every subject length, every start offset and every
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
from .bounds import (
    SIMPLE_OPS,
    bump,
    const,
    exceeds,
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
    _evaluation(L)
    _walk(L)
    _charge(L)
    _shape(L)
    _check(L)


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
    # A switch that covers its enum may carry no default (TIR-SPEC.md rule
    # V-032), and it needs none: an enum value is one of the variants it
    # declares. Printed, though, it is an integer like any other, and a caller
    # of the generated module who invents one has to be told this is not a
    # bound rather than handed the zero an untouched slot holds.
    known = f.let("known", boolean, boolean(False))
    with f.switch(f["kind"]) as arm:
        with arm.case("BkCost"):
            f.set(which, cert.field("cost"))
            f.set(known, boolean(True))
        with arm.case("BkStack"):
            f.set(which, cert.field("stack"))
            f.set(ceiling, counter(spec.MAX_STACK))
            f.set(known, boolean(True))
        with arm.case("BkMem"):
            f.set(which, cert.field("mem"))
            f.set(ceiling, counter(CEILING))
            f.set(known, boolean(True))
    with f.if_(lnot(known)):
        f.ret(exceeds(L))
    out = f.let("out", L.Bound)
    f.call("poly_value", [which, f["n"]], dest=out)
    with f.if_(land(out.field("ok"), out.field("value") > ceiling)):
        f.ret(exceeds(L))
    f.ret(out)


def _walk(L: Layout) -> None:
    """What one span of bytecode costs, and what the three shapes cost.

    Each of these fills an accumulator: the visits, the backtrack entries and
    the undo entries charged for one entry into the span, and the flow that
    leaves it going forward. Flow is the whole of the composition — every
    quantity is linear in it — so the accumulator's `flow` field starts as one
    entry and ends as the region's ambiguity.

    None of them asks whether the tree describes the program. `cert_shape` has
    settled that before any of these runs, and stating those rules twice would
    put them where they could drift. What is left here is the arithmetic, plus
    the two or three comparisons each one needs to stay total on its own: not a
    read past the end of an array, and not a walk that fails to advance.
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
            ("prices", L.FrozenPrices),
            ("sibs", L.Marks, "inout"),
            ("lo", u32),
            ("hi", u32),
            ("first", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    regions = f["regions"]
    cursor = f.let("cursor", u32, f["first"])
    acc = f["acc"]
    over = f["over"]
    pc = f.let("pc", u32, f["lo"])

    with f.while_(pc < f["hi"], down(f["hi"], pc)):
        at = tmp(f, u32, cursor)
        with f.if_(at != u32(spec.NONE)):
            kid = tmp(f, L.Region, regions.at(at))
            with f.if_(kid.field("lo") == pc):
                # The one comparison here that is not arithmetic: a child
                # covering no instruction would leave the walk where it was,
                # and a loop that does not advance is not a loop. `shape_span`
                # is where that is a rule rather than a guard.
                with f.if_(kid.field("hi") <= pc):
                    f.ret(L.Cr.CrShape)
                claim = tmp(f, L.Price, f["prices"].at(at))
                flow = tmp(f, L.Poly, acc.field("flow"))
                for quantity in ("work", "stack", "trail"):
                    bump(
                        f,
                        L,
                        acc,
                        quantity,
                        times(f, L, flow, claim.field(quantity), over),
                        over,
                    )
                onward = times(f, L, flow, claim.field("outs"), over)
                f.set(acc.field("flow"), onward)
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
                # `shape_span` has already refused every opcode that is not one
                # of these, so this arm is what makes the switch total rather
                # than a rule of its own.
                f.ret(L.Cr.CrOpcode)
        f.set(pc, pc + u32(1))
    f.ret(L.Cr.CrOk)


def _alt(L: Layout) -> None:
    f = L.func(
        "scan_alt",
        params=[
            ("prices", L.FrozenPrices),
            ("sibs", L.Marks, "inout"),
            ("first", u32),
            ("acc", L.Acc, "inout"),
            ("over", boolean, "inout"),
        ],
        ret=L.Cr,
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
        claim = tmp(f, L.Price, f["prices"].at(c))
        nxt = tmp(f, u32, f["sibs"].at(c))
        with f.if_(nxt != u32(spec.NONE)):
            # Every branch but the last is guarded by a split and leaves by a
            # jump: the split is visited once, and the jump once per way the
            # branch found to succeed.
            extra = plus(f, L, const(L, counter(1)), claim.field("outs"), over)
            bump(f, L, acc, "work", extra, over)
            bump(f, L, acc, "stack", const(L, counter(1)), over)
        # Backtracking works its way along the chain of splits, so every branch
        # is entered, once.
        for quantity, claimed in (
            ("work", "work"),
            ("stack", "stack"),
            ("trail", "trail"),
            ("flow", "outs"),
        ):
            bump(f, L, acc, quantity, claim.field(claimed), over)
        f.set(c, nxt)
        f.set(k, k + u32(1))
    f.ret(L.Cr.CrOk)


def _body(f, L: Layout, lo, hi) -> None:
    """Price the span a repetition repeats, whichever of the two shapes it is.

    This emits a return: a span that does not price is a repeat that does not,
    and there is nothing after it for `scan_repeat` to do.
    """
    f.call(
        "scan_span",
        [
            f["code"],
            f["regions"],
            f["prices"],
            inout(f["sibs"]),
            lo,
            hi,
            f["first"],
            inout(f["acc"]),
            inout(f["over"]),
        ],
        dest=f["verdict"],
    )
    with f.if_(f["verdict"] != L.Cr.CrOk):
        f.ret(f["verdict"])


def _repeat(L: Layout) -> None:
    f = L.func(
        "scan_repeat",
        params=[
            ("code", L.FrozenCode),
            ("reps", L.FrozenReps),
            ("regions", L.FrozenRegions),
            ("prices", L.FrozenPrices),
            ("sibs", L.Marks, "inout"),
            ("at", u32),
            ("first", u32),
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
    verdict = f.let("verdict", L.Cr, L.Cr.CrOk)
    head = f.let("head", L.Inst, code.at(lo))
    fresh(f, L, acc, const(L, counter(1)))

    # Which of the two rules applies is read off the head, and `shape_repeat`
    # has already held the rest of the range to whichever one that is.
    with f.if_(head.field("op") == L.Op.OpSplit):
        # An optional item: one split whose arms are the body and what follows.
        _body(f, L, lo + u32(1), hi)
        one = const(L, counter(1))
        bump(f, L, acc, "work", one, over)
        bump(f, L, acc, "stack", one, over)
        # Skipping the body is a way out of the region too.
        bump(f, L, acc, "flow", one, over)
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
    rep = f.let("rep", L.Rep, f["reps"].at(which))

    _body(f, L, lo + u32(3), hi - u32(1))

    # The body's ambiguity is what one iteration hands the next, so the flow
    # through the head is its powers summed. A body that grows more ambiguous
    # with the subject raises that to a power of n, and no closed form here has
    # that shape — an honest refusal rather than a bound nobody can write down.
    branching = f.let("branching", L.Poly, acc.field("flow"))
    with f.if_(lnot(flat(branching))):
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
            f.set(over, boolean(True))
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
    f.ret(L.Cr.CrOk)


def _charge(L: Layout) -> None:
    """What a whole call costs, from BOUNDS.md section 5.

    The register file and the ovector are sized and zeroed once, a match copies
    the ovector back out once, every starting position pays for clearing the
    registers again, and the two growing arrays are charged for the buffers
    they hold and the ones they held while copying. None of it belongs to a
    region, which is why the three numbers a caller reads sit on the
    certificate rather than on the root.
    """
    f = L.func(
        "charge_call",
        params=[
            ("re", L.Re),
            ("cert", L.Cert),
            ("whole", L.Price),
            ("over", boolean, "inout"),
        ],
        ret=L.Cr,
    )
    re = f["re"]
    whole = f["whole"]
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
        claimed = tmp(f, L.Poly, whole.field(quantity))
        f.set(capacity, zero(L))
        # The growth schedule doubles from its floor, so a run that holds at
        # most k entries never reserves more than twice that, and one that
        # never pushes never allocates at all.
        with f.if_(lnot(nothing(claimed))):
            grown = times(f, L, claimed, const(L, counter(spec.GROW_FACTOR)), over)
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
    cost = plus(
        f, L, const(L, setup + deliver), plus(f, L, positions, growth, over), over
    )
    held = times(f, L, scratch, const(L, counter(2)), over)
    memory = plus(f, L, const(L, setup), held, over)

    with f.if_(over):
        f.ret(L.Cr.CrOverflow)
    holds = f.let("holds", boolean, boolean(False))
    for claim, needed, refusal in (
        ("cost", cost, L.Cr.CrTotalCost),
        ("stack", whole.field("stack"), L.Cr.CrTotalStack),
        ("mem", memory, L.Cr.CrTotalMem),
    ):
        f.call("poly_ge", [f["cert"].field(claim), needed], dest=holds)
        with f.if_(lnot(holds)):
            f.ret(refusal)
    f.ret(L.Cr.CrOk)


def _shape(L: Layout) -> None:
    """Does this program's region tree describe this program?

    Everything the checker can settle without looking at a certificate, which
    is the half of it that has to run whether or not the analyzer found a bound
    to check. A pattern the composition rules cannot price still has a tree,
    and a compiler that emitted a bad one is a bug of ours either way; gating
    this on a certificate arriving would leave that bug hidden behind exactly
    the patterns the analyzer gives up on.

    So `cert_check` starts here, and so does compilation, before it asks the
    analyzer for anything. Which means it has to be the whole of the structural
    contract rather than the easy part of it: not only that the tree is a tree
    and its ranges nest, but that every instruction is accounted for by a
    region whose kind has a rule for it, and that the bytecode under each kind
    is the shape that kind is a name for.
    """
    _shape_span(L)
    _shape_alt(L)
    _shape_repeat(L)
    _shape_tree(L)


def _shape_span(L: Layout) -> None:
    """BOUNDS.md section 4.1, minus the pricing: what a straight-line region holds."""
    f = L.func(
        "shape_span",
        params=[
            ("code", L.FrozenCode),
            ("regions", L.FrozenRegions),
            ("sibs", L.Marks, "inout"),
            ("lo", u32),
            ("hi", u32),
            ("first", u32),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    regions = f["regions"]
    cursor = f.let("cursor", u32, f["first"])
    pc = f.let("pc", u32, f["lo"])

    with f.while_(pc < f["hi"], down(f["hi"], pc)):
        at = tmp(f, u32, cursor)
        with f.if_(at != u32(spec.NONE)):
            kid = tmp(f, L.Region, regions.at(at))
            # Children arrive in code order, so one behind the walk is one the
            # walk has already priced as part of its parent.
            with f.if_(kid.field("lo") < pc):
                f.ret(L.Cr.CrShape)
            with f.if_(kid.field("lo") == pc):
                # A child covering no instruction would leave the walk where it
                # was, and there is nothing for one to say that its parent does
                # not already say.
                with f.if_(lor(kid.field("hi") <= pc, kid.field("hi") > f["hi"])):
                    f.ret(L.Cr.CrShape)
                f.set(pc, kid.field("hi"))
                f.set(cursor, f["sibs"].at(at))
                f.cont()
        # The first five rows of BOUNDS.md section 3 are the whole of what a
        # region may hold loose. Everything else forks, jumps or drives a
        # repetition and belongs to a region whose kind says how to price it,
        # so meeting one here is the tree failing to explain the program.
        with f.switch(code.at(pc).field("op")) as arm:
            for name in SIMPLE_OPS + ("OpSave", "OpAccept"):
                with arm.case(name):
                    f.set(pc, pc + u32(1))
            with arm.otherwise():
                f.ret(L.Cr.CrOpcode)

    # A child the walk never reached is one covering code this span does not,
    # which no rule prices.
    with f.if_(cursor != u32(spec.NONE)):
        f.ret(L.Cr.CrChildren)
    f.ret(L.Cr.CrOk)


def _shape_alt(L: Layout) -> None:
    """BOUNDS.md section 4.2: the splits, the branches and the jumps line up."""
    f = L.func(
        "shape_alt",
        params=[
            ("code", L.FrozenCode),
            ("regions", L.FrozenRegions),
            ("sibs", L.Marks, "inout"),
            ("at", u32),
            ("first", u32),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    regions = f["regions"]
    here = f.let("here", L.Region, regions.at(f["at"]))
    hi = f.let("hi", u32, here.field("hi"))
    total = f.let("total", u32, regions.len())
    # An alternation compiles to `split branch jump split branch jump ...
    # branch`, with every jump patched to the end and every split's other arm
    # pointing at the next one, so walking the branches walks the code.
    p = f.let("p", u32, here.field("lo"))
    c = f.let("c", u32, f["first"])
    k = f.let("k", u32, u32(0))

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
            f.set(p, end + u32(1))
        with f.else_():
            with f.if_(lor(kid.field("lo") != p, kid.field("hi") != hi)):
                f.ret(L.Cr.CrShape)
        f.set(c, nxt)
        f.set(k, k + u32(1))

    with f.if_(c != u32(spec.NONE)):
        f.ret(L.Cr.CrChildren)
    # One branch is not an alternation: the compiler emits no split for it, so
    # a region claiming to be one is pricing instructions that are not there.
    with f.if_(k < u32(2)):
        f.ret(L.Cr.CrShape)
    f.ret(L.Cr.CrOk)


def _shape_repeat(L: Layout) -> None:
    """BOUNDS.md sections 4.3 and 4.4: an optional item, or the five-part header."""
    f = L.func(
        "shape_repeat",
        params=[
            ("code", L.FrozenCode),
            ("reps", L.FrozenReps),
            ("regions", L.FrozenRegions),
            ("sibs", L.Marks, "inout"),
            ("at", u32),
            ("first", u32),
        ],
        ret=L.Cr,
    )
    code = f["code"]
    here = f.let("here", L.Region, f["regions"].at(f["at"]))
    lo = f.let("lo", u32, here.field("lo"))
    hi = f.let("hi", u32, here.field("hi"))
    with f.if_(hi <= lo):
        f.ret(L.Cr.CrShape)
    head = f.let("head", L.Inst, code.at(lo))
    body = f.let("body", L.Cr, L.Cr.CrOk)

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
        _inside(f, lo + u32(1), hi, body)
        f.ret(body)

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
    # or the iteration count would be read off some other quantifier. Between
    # the four opcodes and these three offsets there is nothing left for a
    # region to choose, which is why a repeat needs no witness field beyond its
    # range (BOUNDS.md section 4).
    with f.if_(
        lor(
            rep.field("head") != lo + u32(1),
            lor(rep.field("body") != lo + u32(2), rep.field("after") != hi),
        )
    ):
        f.ret(L.Cr.CrShape)
    _inside(f, lo + u32(3), hi - u32(1), body)
    f.ret(body)


def _inside(f, lo, hi, dest) -> None:
    """Read the span a repetition repeats, whichever of the two shapes it is."""
    f.call(
        "shape_span",
        [f["code"], f["regions"], inout(f["sibs"]), lo, hi, f["first"]],
        dest=dest,
    )


def _shape_tree(L: Layout) -> None:
    f = L.func("cert_shape", params=[("re", L.Re)], ret=L.Cr)
    re = f["re"]
    code = f.let("code", L.FrozenCode, re.field("code"))
    regions = f.let("regions", L.FrozenRegions, re.field("regions"))
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
        # A branch is one arm of an alternation and means nothing anywhere
        # else. `shape_alt` refuses a child of an alternation that is not one;
        # this is the same rule read from the other end, so the two together
        # say that branches and alternations only ever come in pairs.
        with f.if_(
            land(
                here.field("kind") == L.Rk.RkBranch,
                outer.field("kind") != L.Rk.RkAlt,
            )
        ):
            f.ret(L.Cr.CrChildren)
        f.set(ends.at(parent), here.field("hi"))
        f.set(i, i + u32(1))

    # Then the code under each region, which is what makes the kinds mean
    # something. The parent order settled above is what lets the child lists be
    # built in one backwards pass.
    kids = f.let("kids", L.Marks)
    sibs = f.let("sibs", L.Marks)
    f.call("region_kids", [regions, inout(kids), inout(sibs)])

    # Outermost first, which is what answers a badly built tree with the
    # outermost thing wrong with it rather than with whatever the walk reached
    # first.
    f.set(i, u32(0))
    with f.while_(i < total, down(total, i)):
        one = tmp(f, L.Region, regions.at(i))
        first = tmp(f, u32, kids.at(i))
        # A switch that covers its enum may carry no default (TIR-SPEC.md rule
        # V-032), and it needs none: an enum value is one of the variants it
        # declares. Printed, though, it is an integer like any other, so the
        # verdict starts as the refusal a caller who invented one has earned,
        # and every arm that recognises its kind writes over it.
        verdict = tmp(f, L.Cr, L.Cr.CrShape)
        with f.switch(one.field("kind")) as arm:
            for name in ("RkRoot", "RkGroup", "RkBranch"):
                with arm.case(name):
                    f.call(
                        "shape_span",
                        [
                            code,
                            regions,
                            inout(sibs),
                            one.field("lo"),
                            one.field("hi"),
                            first,
                        ],
                        dest=verdict,
                    )
            with arm.case("RkAlt"):
                f.call(
                    "shape_alt",
                    [code, regions, inout(sibs), i, first],
                    dest=verdict,
                )
            with arm.case("RkRepeat"):
                f.call(
                    "shape_repeat",
                    [code, re.field("reps"), regions, inout(sibs), i, first],
                    dest=verdict,
                )
        with f.if_(verdict != L.Cr.CrOk):
            f.ret(verdict)
        f.set(i, i + u32(1))
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

    # The tree first, and on its own: whether it describes the program is a
    # question about the program, and answering it before looking at a claim is
    # what lets compilation ask the same question when there is no claim.
    shape = f.let("shape", L.Cr, L.Cr.CrOk)
    f.call("cert_shape", [re], dest=shape)
    with f.if_(shape != L.Cr.CrOk):
        f.ret(shape)

    code = f.let("code", L.FrozenCode, re.field("code"))
    # The tree is the compiler's, emitted while it still had the AST in hand,
    # and the certificate says what each of its regions costs. One price per
    # region, in the same order, so a claim cannot be about a region nobody
    # emitted and no region can go unpriced.
    regions = f.let("regions", L.FrozenRegions, re.field("regions"))
    prices = f.let("prices", L.FrozenPrices, cert.field("prices"))
    total = f.let("total", u32, regions.len())
    with f.if_(prices.len() != total):
        f.ret(L.Cr.CrPrices)

    # A base of zero is 0^n, which is 1 at n = 0 and 0 everywhere else. No
    # bound has that shape, and letting one through would make a claim that
    # vanishes on longer subjects look like a claim that holds.
    for quantity in ("cost", "stack", "mem"):
        with f.if_(cert.field(quantity).field("base") == counter(0)):
            f.ret(L.Cr.CrBase)
    # The one claim in a certificate that is not a number, held to the shape it
    # names: linear means the cost really is at most c * (n + 1), so no growing
    # base and no power above the first. Classification soundness is a Layer A
    # obligation (DESIGN.md section 6), and this is the part of it the checker
    # can settle by looking.
    with f.if_(
        land(
            cert.field("complexity") != L.Cc.CcNotProvenLinear,
            cert.field("complexity") != L.Cc.CcLinear,
        )
    ):
        f.ret(L.Cr.CrShape)
    with f.if_(cert.field("complexity") == L.Cc.CcLinear):
        with f.if_(lnot(linear(cert.field("cost")))):
            f.ret(L.Cr.CrNotLinear)

    i = f.let("i", u32, u32(0))
    with f.while_(i < total, down(total, i)):
        claimed = tmp(f, L.Price, prices.at(i))
        for quantity in ("work", "outs", "stack", "trail"):
            with f.if_(claimed.field(quantity).field("base") == counter(0)):
                f.ret(L.Cr.CrBase)
        f.set(i, i + u32(1))

    kids = f.let("kids", L.Marks)
    sibs = f.let("sibs", L.Marks)
    f.call("region_kids", [regions, inout(kids), inout(sibs)])

    # Each region is priced from what its children claim, so the induction that
    # makes the whole tree sound is one step deep and entirely local, and the
    # order regions are visited in does not enter into it.
    f.set(i, u32(0))
    with f.while_(i < total, down(total, i)):
        one = tmp(f, L.Region, regions.at(i))
        acc = tmp(f, L.Acc)
        first = tmp(f, u32, kids.at(i))
        # `cert_shape` has already refused a kind that names no variant, so
        # what this default is for is keeping the switch total.
        verdict = tmp(f, L.Cr, L.Cr.CrShape)
        with f.switch(one.field("kind")) as arm:
            for name in ("RkRoot", "RkGroup", "RkBranch"):
                with arm.case(name):
                    fresh(f, L, acc, const(L, counter(1)))
                    f.call(
                        "scan_span",
                        [
                            code,
                            regions,
                            prices,
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
                    "scan_alt",
                    [prices, inout(sibs), first, inout(acc), inout(over)],
                    dest=verdict,
                )
            with arm.case("RkRepeat"):
                f.call(
                    "scan_repeat",
                    [
                        code,
                        re.field("reps"),
                        regions,
                        prices,
                        inout(sibs),
                        i,
                        first,
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
        mine = tmp(f, L.Price, prices.at(i))
        for quantity, needed, refusal in (
            ("work", "work", L.Cr.CrRegionWork),
            ("outs", "flow", L.Cr.CrRegionOuts),
            ("stack", "stack", L.Cr.CrRegionStack),
            ("trail", "trail", L.Cr.CrRegionTrail),
        ):
            f.call("poly_ge", [mine.field(quantity), acc.field(needed)], dest=holds)
            with f.if_(lnot(holds)):
                f.ret(refusal)
        f.set(i, i + u32(1))

    # What the call costs on top of what the tree prices, which is the one
    # part of these rules that will differ most between configurations.
    whole = f.let("whole", L.Price, prices.at(u32(0)))
    charged = f.let("charged", L.Cr, L.Cr.CrOk)
    f.call("charge_call", [re, cert, whole, inout(over)], dest=charged)
    with f.if_(charged != L.Cr.CrOk):
        f.ret(charged)

    f.ret(L.Cr.CrOk)
