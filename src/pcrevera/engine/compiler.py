"""The bytecode compiler, written in TIR.

The AST is walked with an explicit job stack rather than by recursion, which TIR
does not have: a job carries the node it is on and how far through it the walk
has got, so a construct that has to emit something after its children — a
group's closing Save, an alternation's jump patches — simply gets revisited.

There is one bytecode and both matchers read it, so a counted repetition is
lowered to star form here rather than compiled twice (DESIGN.md section 4.3).
What is left after the lowering is the four Rep opcodes of a pure star, which
the Pike VM reads as epsilon forks; what the lowering declines to touch keeps
its counter and its place on the backtracking matcher.

The decision is taken once for the whole pattern, before a single instruction
is emitted, because one retained counter already makes a program ineligible
and partial lowering would buy nothing. `plan_lowering` is where it is taken:
a pre-check for the two semantic blockers, and a dry run that prices the fully
lowered candidate in closed form against every cap the emitter would hit.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, land, lnot, lor, u8, u32
from . import spec
from .layout import Layout
from .parser import down, tmp

# How many times the walk may revisit a job before we call it a bug of ours
# rather than a pattern's fault.
#
# In counter form every node is entered once and revisited once per child, so
# three times the arena is already an over-estimate and this is generous. The
# lowering breaks that argument on purpose — a repeat job is revisited once per
# copy it emits — so on that path this stops being a slack bound and becomes a
# cap like any other, priced by the dry run before anything is emitted.
WALK_FUEL = 8 * spec.MAX_NODES


def build(L: Layout) -> None:
    _emit(L)
    _plan(L)
    _walk(L)


def _emit(L: Layout) -> None:
    f = L.func(
        "emit",
        params=[("w", L.Work, "inout"), ("op", L.Op), ("arg", u32), ("alt", u32)],
        ret=u32,
    )
    w = f["w"]
    pc = tmp(f, u32, w.field("code").len())
    with f.if_(pc >= u32(spec.MAX_CODE)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret(u32(0))
    f.push(w.field("code"), L.Inst.of(op=f["op"], arg=f["arg"], alt=f["alt"]))
    f.ret(pc)

    f = L.func(
        "push_job", params=[("w", L.Work, "inout"), ("node", u32), ("here", u32)]
    )
    w = f["w"]
    with f.if_(w.field("jobs").len() >= u32(spec.MAX_JOBS)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()
    f.push(
        w.field("jobs"),
        L.Job.of(
            node=f["node"],
            phase=u32(0),
            cur=u32(0),
            mark=u32(0),
            base=u32(0),
            here=f["here"],
            arm=u32(spec.NONE),
        ),
    )
    # How deep the stack really got, so the dry run's prediction has something
    # to be compared against rather than believed.
    with f.if_(w.field("jobs").len() > w.field("peakjobs")):
        f.set(w.field("peakjobs"), w.field("jobs").len())

    # The region table of DESIGN.md section 5, emitted while the AST is still
    # in hand. A region opens where its first instruction is about to go and
    # closes where the next one will, so both ends are just the code length at
    # the right moment.
    f = L.func(
        "open_region",
        params=[("w", L.Work, "inout"), ("kind", L.Rk), ("parent", u32)],
        ret=u32,
    )
    w = f["w"]
    at = tmp(f, u32, w.field("regions").len())
    with f.if_(at >= u32(spec.MAX_REGIONS)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret(u32(0))
    f.push(
        w.field("regions"),
        L.Region.of(
            kind=f["kind"],
            parent=f["parent"],
            lo=w.field("code").len(),
            hi=w.field("code").len(),
        ),
    )
    f.ret(at)

    f = L.func("close_region", params=[("w", L.Work, "inout"), ("at", u32)])
    w = f["w"]
    at = tmp(f, u32, f["at"])
    with f.if_(at >= w.field("regions").len()):
        f.ret()
    f.set(w.field("regions").at(at).field("hi"), w.field("code").len())

    f = L.func("drop_empty_region", params=[("w", L.Work, "inout"), ("at", u32)])
    # A construct that compiled to nothing prices nothing, and a region of zero
    # width is one the composition rules have no use for. Everything inside it
    # compiled to nothing too, so it was dropped in its turn and this one is
    # back on top of the table.
    w = f["w"]
    at = tmp(f, u32, f["at"])
    with f.if_(at >= w.field("regions").len()):
        f.ret()
    with f.if_(w.field("regions").at(at).field("lo") == w.field("code").len()):
        f.truncate(w.field("regions"), at)

    f = L.func("push_patch", params=[("w", L.Work, "inout"), ("pc", u32)])
    w = f["w"]
    with f.if_(w.field("patches").len() >= u32(spec.MAX_PATCHES)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()
    f.push(w.field("patches"), f["pc"])
    with f.if_(w.field("patches").len() > w.field("peakpatch")):
        f.set(w.field("peakpatch"), w.field("patches").len())

    f = L.func("new_rep", params=[("w", L.Work, "inout")], ret=u32)
    w = f["w"]
    r = tmp(f, u32, w.field("nrep"))
    with f.if_(r >= u32(spec.MAX_REPS)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret(u32(0))
    f.push(
        w.field("reps"),
        L.Rep.of(
            lo=u32(0),
            hi=u32(0),
            greedy=boolean(True),
            head=u32(0),
            body=u32(0),
            after=u32(0),
        ),
    )
    f.set(w.field("nrep"), r + u32(1))
    f.ret(r)


def _plan(L: Layout) -> None:
    """What the lowered candidate would come to, without building any of it.

    One row per arena slot, filled children first, holding both halves of the
    decision: the sizes the fully lowered form would reach, and what the
    pre-check found under that node. Both are folded into one pass because
    they read the same tree and neither is worth a second walk of it.

    Every size is a saturating counter on purpose. A quantifier may name 65535
    and quantifiers nest, so the product is exactly the number that has to
    saturate rather than wrap — and a saturated count is past every cap, which
    is the answer that keeps the pattern in counter form.
    """
    f = L.func("size_node", params=[("w", L.Work, "inout"), ("at", u32)])
    w = f["w"]
    nodes = w.field("nodes")
    sizes = w.field("sizes")
    at = tmp(f, u32, f["at"])
    nd = tmp(f, L.Node, nodes.at(at))
    out = tmp(f, L.Size)
    f.set(out.field("code"), counter(0))
    f.set(out.field("regions"), counter(0))
    f.set(out.field("reps"), counter(0))
    f.set(out.field("visits"), counter(1))
    f.set(out.field("depth"), u32(1))
    f.set(out.field("patches"), u32(0))
    f.set(out.field("nullable"), boolean(False))
    f.set(out.field("blockers"), u32(0))
    f.set(out.field("needs"), boolean(False))

    def child_loop(alt: bool) -> None:
        """The sibling list, folded left to right.

        `kids` counts the children already folded, which for an alternation is
        also how many closing jumps are waiting to be patched while the next
        branch compiles — the one place the two kinds differ in more than
        their totals.
        """
        child = tmp(f, u32, nd.field("first"))
        kids = tmp(f, u32, u32(0))
        fuel = tmp(f, counter, counter(spec.MAX_NODES))
        f.set(out.field("depth"), u32(0))
        f.set(out.field("nullable"), boolean(not alt))
        with f.while_(land(child != u32(0), fuel > counter(0)), fuel):
            f.set(fuel, fuel - counter(1))
            cs = tmp(f, L.Size, sizes.at(child))
            for name in ("code", "regions", "reps", "visits"):
                f.set(out.field(name), out.field(name) + cs.field(name))
            with f.if_(cs.field("depth") > out.field("depth")):
                f.set(out.field("depth"), cs.field("depth"))
            held = tmp(
                f,
                u32,
                kids + cs.field("patches") if alt else cs.field("patches"),
            )
            with f.if_(held > out.field("patches")):
                f.set(out.field("patches"), held)
            if alt:
                with f.if_(cs.field("nullable")):
                    f.set(out.field("nullable"), boolean(True))
            else:
                with f.if_(lnot(cs.field("nullable"))):
                    f.set(out.field("nullable"), boolean(False))
            f.set(out.field("blockers"), out.field("blockers") | cs.field("blockers"))
            with f.if_(cs.field("needs")):
                f.set(out.field("needs"), boolean(True))
            f.set(kids, kids + u32(1))
            f.set(child, nodes.at(child).field("nxt"))
        # One visit per child to push it, and one more to find the list ended.
        f.set(out.field("visits"), out.field("visits") + kids.cast(counter))
        f.set(out.field("depth"), out.field("depth") + u32(1))
        if alt:
            # A single branch compiles to no split and no jump, so there is no
            # alternation there and no region claiming there is one.
            with f.if_(kids > u32(1)):
                f.set(
                    out.field("code"),
                    out.field("code") + (kids - u32(1)).cast(counter) * counter(2),
                )
                f.set(
                    out.field("regions"),
                    out.field("regions") + kids.cast(counter) + counter(1),
                )

    with f.switch(nd.field("kind")) as arm:
        with arm.case("NdNil"):
            f.set(out.field("nullable"), boolean(True))
        for name in ("NdChar", "NdCharCI", "NdClass", "NdAny", "NdAnyNoNL"):
            with arm.case(name):
                f.set(out.field("code"), counter(1))
        with arm.case("NdBsr"):
            f.set(out.field("code"), counter(1))
            f.set(out.field("blockers"), u32(spec.LB_BSR))
        for name in (
            "NdCirc",
            "NdCircM",
            "NdDoll",
            "NdDollE",
            "NdDollM",
            "NdSod",
            "NdEod",
            "NdEodn",
            "NdWordB",
            "NdNotWordB",
        ):
            with arm.case(name):
                # An assertion consumes nothing, and `pike_hollow` reads the
                # bytecode the same way, which is what keeps the pre-check and
                # the eligibility predicate answering about the same thing.
                f.set(out.field("code"), counter(1))
                f.set(out.field("nullable"), boolean(True))

        with arm.case("NdConcat"):
            child_loop(alt=False)

        with arm.case("NdAlt"):
            child_loop(alt=True)

        with arm.case("NdGroup"):
            body = tmp(f, u32, nd.field("first"))
            f.set(out.field("nullable"), boolean(True))
            f.set(out.field("visits"), counter(2))
            with f.if_(body != u32(0)):
                bs = tmp(f, L.Size, sizes.at(body))
                for name in ("code", "regions", "reps", "patches", "blockers"):
                    f.set(out.field(name), bs.field(name))
                f.set(out.field("visits"), counter(2) + bs.field("visits"))
                f.set(out.field("depth"), u32(1) + bs.field("depth"))
                f.set(out.field("nullable"), bs.field("nullable"))
                f.set(out.field("needs"), bs.field("needs"))
            with f.if_(nd.field("val") != u32(0)):
                f.set(out.field("code"), out.field("code") + counter(2))
            # A group that compiled to nothing has its region taken back off.
            with f.if_(out.field("code") != counter(0)):
                f.set(out.field("regions"), out.field("regions") + counter(1))

        with arm.case("NdRepeat"):
            body = tmp(f, u32, nd.field("first"))
            bs = tmp(f, L.Size, sizes.at(body))
            lo = tmp(f, u32, nd.field("val"))
            hi = tmp(f, u32, nd.field("aux"))
            # Repeated zero times, the body is not compiled at all, so nothing
            # under it is reachable — no code, no blockers, nothing to lower.
            f.set(out.field("nullable"), boolean(True))
            with f.if_(hi != u32(0)):
                f.set(out.field("depth"), u32(1) + bs.field("depth"))
                f.set(out.field("patches"), bs.field("patches"))
                f.set(out.field("needs"), bs.field("needs"))
                f.set(out.field("blockers"), bs.field("blockers"))
                f.set(out.field("nullable"), lor(lo == u32(0), bs.field("nullable")))
                with f.if_(land(hi == u32(spec.NONE), bs.field("nullable"))):
                    # The star this lowers to would keep the nullable body,
                    # which is the one thing lowering cannot fix.
                    f.set(
                        out.field("blockers"),
                        out.field("blockers") | u32(spec.LB_NULLABLE),
                    )
                # How many times the body is emitted, what the quantifier's own
                # scaffolding adds, and how many visits the repeat job takes.
                copies = tmp(f, counter, counter(1))
                extra = tmp(f, counter, counter(0))
                opened = tmp(f, counter, counter(0))
                counters = tmp(f, counter, counter(0))
                own = tmp(f, counter, counter(2))
                exact = tmp(f, boolean, land(lo == u32(1), hi == u32(1)))
                option = tmp(f, boolean, land(lo == u32(0), hi == u32(1)))
                star = tmp(f, boolean, land(lo == u32(0), hi == u32(spec.NONE)))
                with f.if_(option):
                    f.set(extra, counter(1))
                    f.set(opened, counter(1))
                with f.if_(star):
                    f.set(extra, counter(4))
                    f.set(opened, counter(1))
                    f.set(counters, counter(1))
                with f.if_(lnot(lor(exact, lor(option, star)))):
                    f.set(out.field("needs"), boolean(True))
                    with f.if_(hi == u32(spec.NONE)):
                        # m copies and then the native star.
                        f.set(copies, lo.cast(counter) + counter(1))
                        f.set(extra, counter(4))
                        f.set(opened, counter(1))
                        f.set(counters, counter(1))
                        f.set(own, lo.cast(counter) + counter(3))
                    with f.else_():
                        # m copies and then n - m nested optionals, one split
                        # and one region each.
                        f.set(copies, hi.cast(counter))
                        f.set(extra, (hi - lo).cast(counter))
                        f.set(opened, (hi - lo).cast(counter))
                        f.set(own, hi.cast(counter) + counter(2))
                f.set(out.field("code"), copies * bs.field("code") + extra)
                f.set(out.field("regions"), copies * bs.field("regions") + opened)
                f.set(out.field("reps"), copies * bs.field("reps") + counters)
                f.set(out.field("visits"), own + copies * bs.field("visits"))

    f.set(sizes.at(at), out)

    _decide(L)


def _decide(L: Layout) -> None:
    f = L.func(
        "plan_lowering", params=[("w", L.Work, "inout"), ("endanchored", boolean)]
    )
    w = f["w"]
    total = tmp(f, u32, w.field("nodes").len())
    blank = L.Size.of(
        code=counter(0),
        regions=counter(0),
        reps=counter(0),
        visits=counter(0),
        depth=u32(0),
        patches=u32(0),
        nullable=boolean(False),
        blockers=u32(0),
        needs=boolean(False),
    )
    k = tmp(f, u32, u32(0))
    with f.while_(k < total, down(total, k)):
        f.push(w.field("sizes"), blank)
        f.set(k, k + u32(1))

    # Every reachable node, each one appended after its parent. Walking the
    # list backwards then reaches every child before the parent that needs it,
    # which the arena's own index order does not guarantee.
    f.push(w.field("order"), w.field("root"))
    i = tmp(f, u32, u32(0))
    fuel = tmp(f, counter, counter(spec.MAX_NODES))
    with f.while_(
        land(i < w.field("order").len(), fuel > counter(0)), fuel
    ):
        f.set(fuel, fuel - counter(1))
        child = tmp(f, u32, w.field("nodes").at(w.field("order").at(i)).field("first"))
        kids = tmp(f, counter, counter(spec.MAX_NODES))
        with f.while_(land(child != u32(0), kids > counter(0)), kids):
            f.set(kids, kids - counter(1))
            with f.if_(w.field("order").len() >= u32(spec.MAX_NODES)):
                f.set(w.field("err"), u32(spec.E_INTERNAL))
                f.ret()
            f.push(w.field("order"), child)
            f.set(child, w.field("nodes").at(child).field("nxt"))
        with f.if_(kids == counter(0)):
            f.set(w.field("err"), u32(spec.E_INTERNAL))
            f.ret()
        f.set(i, i + u32(1))
    with f.if_(fuel == counter(0)):
        f.set(w.field("err"), u32(spec.E_INTERNAL))
        f.ret()

    j = tmp(f, u32, w.field("order").len())
    with f.while_(j > u32(0), j.cast(counter)):
        f.set(j, j - u32(1))
        node = tmp(f, u32, w.field("order").at(j))
        f.call("size_node", [inout(w), node])

    root = tmp(f, L.Size, w.field("sizes").at(w.field("root")))
    code = tmp(f, counter, root.field("code") + counter(1))
    with f.if_(f["endanchored"]):
        f.set(code, code + counter(1))
    regions = tmp(f, counter, root.field("regions") + counter(1))
    reps = tmp(f, counter, root.field("reps"))
    # The one entry of the vector the emitter does not hold in an array of its
    # own: registers are allocated after the walk, from the capture and
    # repetition counts. Priced here in saturating arithmetic because a
    # candidate the caps are about to refuse can want more of them than a u32
    # holds.
    regs = tmp(
        f,
        counter,
        (w.field("ncap") + u32(1)).cast(counter) * counter(2) + reps * counter(2),
    )
    f.set(w.field("fitcode"), code)
    f.set(w.field("fitregion"), regions)
    f.set(w.field("fitrep"), reps)
    f.set(w.field("fitregs"), regs)
    f.set(w.field("fitvisit"), root.field("visits"))
    f.set(w.field("fitjobs"), root.field("depth"))
    f.set(w.field("fitpatch"), root.field("patches"))

    # Exactly at a cap is a fit, one past it is the fallback: every array
    # refuses the entry that would take it past its declared maximum, so the
    # maximum itself is a length the emitter reaches.
    fits = tmp(f, boolean, boolean(True))
    for value, limit in (
        (code, spec.MAX_CODE),
        (regions, spec.MAX_REGIONS),
        (reps, spec.MAX_REPS),
        (regs, spec.MAX_REGS),
        (root.field("visits"), WALK_FUEL),
    ):
        with f.if_(value > counter(limit)):
            f.set(fits, boolean(False))
    for value, limit in (
        (root.field("depth"), spec.MAX_JOBS),
        (root.field("patches"), spec.MAX_PATCHES),
    ):
        with f.if_(value > u32(limit)):
            f.set(fits, boolean(False))
    f.set(w.field("lowfits"), fits)
    f.set(w.field("blockers"), root.field("blockers"))

    # The order is the report's: a pattern with nothing to lower says so even
    # when it carries a blocker, because the blocker is not why it kept its
    # shape. `predicted` is the separate question of whether the numbers above
    # describe the program about to be emitted.
    f.set(w.field("lowdec"), u32(spec.LOW_NOT_NEEDED))
    f.set(w.field("lowering"), boolean(False))
    with f.if_(root.field("needs")):
        with f.if_(root.field("blockers") != u32(0)):
            f.set(w.field("lowdec"), u32(spec.LOW_BLOCKED))
        with f.else_():
            with f.if_(fits):
                f.set(w.field("lowdec"), u32(spec.LOW_LOWERED))
                f.set(w.field("lowering"), boolean(True))
            with f.else_():
                f.set(w.field("lowdec"), u32(spec.LOW_CAPPED))
    f.set(
        w.field("predicted"),
        lor(w.field("lowering"), lnot(root.field("needs"))),
    )

    _fit(L)


def _fit(L: Layout) -> None:
    """The dry run's numbers against the emitter's, entry by entry.

    The two are computed by different walks over the same tree — one folds a
    list of sizes, the other mutates real storage — and they share only their
    caps and their saturating arithmetic. Which is the point: two calculations
    of one number drift exactly at the cap boundary, and that is where the
    fallback decision lives.
    """
    # Captures take the low registers, in ovector order; each counted
    # repetition takes two above them, a count and the position its current
    # iteration started at. Written once and called from both places that need
    # it, since the dry run approving a candidate the register allocation then
    # refuses is exactly the drift the fit vector exists to catch.
    f = L.func("count_regs", params=[("ncap", u32), ("nrep", u32)], ret=u32)
    f.ret((f["ncap"] + u32(1)) * u32(2) + f["nrep"] * u32(2))

    f = L.func("check_fit", params=[("w", L.Work, "inout"), ("used", counter)])
    w = f["w"]
    bad = tmp(f, boolean, boolean(False))
    allocated = tmp(f, u32, u32(0))
    f.call("count_regs", [w.field("ncap"), w.field("nrep")], dest=allocated)
    for field, actual in (
        ("fitcode", w.field("code").len().cast(counter)),
        ("fitregion", w.field("regions").len().cast(counter)),
        ("fitrep", w.field("nrep").cast(counter)),
        ("fitregs", allocated.cast(counter)),
        ("fitvisit", f["used"]),
    ):
        with f.if_(w.field(field) != actual):
            f.set(bad, boolean(True))
    for field, actual in (
        ("fitjobs", w.field("peakjobs")),
        ("fitpatch", w.field("peakpatch")),
    ):
        with f.if_(w.field(field) != actual):
            f.set(bad, boolean(True))
    with f.if_(bad):
        f.set(w.field("err"), u32(spec.E_INTERNAL))


def _walk(L: Layout) -> None:
    f = L.func(
        "generate", params=[("w", L.Work, "inout"), ("endanchored", boolean)]
    )
    w = f["w"]
    # Whether to lower, decided for the whole pattern before anything is
    # emitted, since one retained counter would make the rest pointless.
    f.call("plan_lowering", [inout(w), f["endanchored"]])
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    root = tmp(f, u32, w.field("root"))
    whole = tmp(f, u32, u32(0))
    f.call("open_region", [inout(w), L.Rk.RkRoot, u32(spec.NONE)], dest=whole)
    f.call("push_job", [inout(w), root, whole])
    fuel = tmp(f, counter, counter(WALK_FUEL))
    pc = tmp(f, u32, u32(0))

    with f.while_(
        land(
            land(w.field("jobs").len() > u32(0), fuel > counter(0)),
            w.field("err") == u32(0),
        ),
        fuel,
    ):
        f.set(fuel, fuel - counter(1))
        top = tmp(f, u32, w.field("jobs").len() - u32(1))
        job = tmp(f, L.Job, w.field("jobs").at(top))
        nd = tmp(f, L.Node, w.field("nodes").at(job.field("node")))
        done = tmp(f, L.Job)

        def leaf(op) -> None:
            f.call("emit", [inout(w), op, nd.field("val"), u32(0)], dest=pc)
            f.pop(w.field("jobs"), done)

        with f.switch(nd.field("kind")) as arm:
            with arm.case("NdNil"):
                f.pop(w.field("jobs"), done)
            with arm.case("NdChar"):
                leaf(L.Op.OpChar)
            with arm.case("NdCharCI"):
                leaf(L.Op.OpCharCI)
            with arm.case("NdClass"):
                leaf(L.Op.OpClass)
            with arm.case("NdAny"):
                leaf(L.Op.OpAny)
            with arm.case("NdAnyNoNL"):
                leaf(L.Op.OpAnyNoNL)
            with arm.case("NdBsr"):
                leaf(L.Op.OpBsr)
            with arm.case("NdCirc"):
                leaf(L.Op.OpCirc)
            with arm.case("NdCircM"):
                leaf(L.Op.OpCircM)
            with arm.case("NdDoll"):
                leaf(L.Op.OpDoll)
            with arm.case("NdDollE"):
                leaf(L.Op.OpDollE)
            with arm.case("NdDollM"):
                leaf(L.Op.OpDollM)
            with arm.case("NdSod"):
                leaf(L.Op.OpSod)
            with arm.case("NdEod"):
                leaf(L.Op.OpEod)
            with arm.case("NdEodn"):
                leaf(L.Op.OpEodn)
            with arm.case("NdWordB"):
                leaf(L.Op.OpWordB)
            with arm.case("NdNotWordB"):
                leaf(L.Op.OpNotWordB)

            with arm.case("NdConcat"):
                child = tmp(f, u32, nd.field("first"))
                with f.if_(job.field("phase") != u32(0)):
                    f.set(child, w.field("nodes").at(job.field("cur")).field("nxt"))
                with f.if_(child == u32(0)):
                    f.pop(w.field("jobs"), done)
                with f.else_():
                    f.set(w.field("jobs").at(top).field("phase"), u32(1))
                    f.set(w.field("jobs").at(top).field("cur"), child)
                    f.call("push_job", [inout(w), child, job.field("here")])

            with arm.case("NdGroup"):
                with f.if_(job.field("phase") == u32(0)):
                    mine = tmp(f, u32, u32(0))
                    f.call(
                        "open_region",
                        [inout(w), L.Rk.RkGroup, job.field("here")],
                        dest=mine,
                    )
                    f.set(w.field("jobs").at(top).field("here"), mine)
                    with f.if_(nd.field("val") != u32(0)):
                        slot = tmp(f, u32, nd.field("val") * u32(2))
                        f.call("emit", [inout(w), L.Op.OpSave, slot, u32(0)], dest=pc)
                    f.set(w.field("jobs").at(top).field("phase"), u32(1))
                    body = tmp(f, u32, nd.field("first"))
                    with f.if_(body != u32(0)):
                        f.call("push_job", [inout(w), body, mine])
                with f.else_():
                    with f.if_(nd.field("val") != u32(0)):
                        slot = tmp(f, u32, nd.field("val") * u32(2) + u32(1))
                        f.call("emit", [inout(w), L.Op.OpSave, slot, u32(0)], dest=pc)
                    f.call("close_region", [inout(w), job.field("here")])
                    f.call("drop_empty_region", [inout(w), job.field("here")])
                    f.pop(w.field("jobs"), done)

            with arm.case("NdAlt"):
                f.call("walk_alt", [inout(w), top, job, nd])

            with arm.case("NdRepeat"):
                f.call("walk_repeat", [inout(w), top, job, nd])

    with f.if_(w.field("err") != u32(0)):
        f.ret()
    # A walk that ran out of fuel is one with jobs still on the stack, which is
    # the thing to test: a walk needing exactly WALK_FUEL turns finishes on its
    # last one and leaves the counter at zero, and reading that as exhaustion
    # would refuse a program the generator had just finished emitting.
    with f.if_(w.field("jobs").len() > u32(0)):
        f.set(w.field("err"), u32(spec.E_INTERNAL))
        f.ret()
    with f.if_(f["endanchored"]):
        f.call("emit", [inout(w), L.Op.OpEod, u32(0), u32(0)], dest=pc)
    f.call("emit", [inout(w), L.Op.OpAccept, u32(0), u32(0)], dest=pc)
    # The root covers the whole program, the trailing accept included, so it
    # closes after the last instruction rather than after the last construct.
    f.call("close_region", [inout(w), whole])
    with f.if_(land(w.field("err") == u32(0), w.field("predicted"))):
        f.call("check_fit", [inout(w), counter(WALK_FUEL) - fuel])
    with f.if_(w.field("err") == u32(0)):
        f.call("scan_first", [inout(w)])

    _alt(L)
    _repeat(L)
    _first(L)


def _alt(L: Layout) -> None:
    """One alternation branch per visit, splits and jumps patched as we go."""
    f = L.func(
        "walk_alt",
        params=[
            ("w", L.Work, "inout"),
            ("top", u32),
            ("job", L.Job),
            ("nd", L.Node),
        ],
    )
    w = f["w"]
    job = f["job"]
    top = tmp(f, u32, f["top"])
    done = tmp(f, L.Job)
    pc = tmp(f, u32, u32(0))

    with f.if_(job.field("phase") == u32(2)):
        stop = tmp(f, u32, w.field("code").len())
        with f.while_(
            w.field("patches").len() > job.field("base"),
            w.field("patches").len().cast(counter),
        ):
            p = tmp(f, u32, u32(0))
            f.pop(w.field("patches"), p)
            f.set(w.field("code").at(p).field("arg"), stop)
        # The last branch and the alternation itself end where the jumps land.
        f.call("close_region", [inout(w), job.field("arm")])
        f.call("close_region", [inout(w), job.field("here")])
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(3)):
        f.pop(w.field("jobs"), done)
        f.ret()

    branch = tmp(f, u32, f["nd"].field("first"))
    with f.if_(job.field("phase") == u32(0)):
        f.set(w.field("jobs").at(top).field("base"), w.field("patches").len())
    with f.else_():
        # The branch just compiled ends where its jump to the end sits, and
        # the split that guarded it now knows where the next one starts.
        f.call("close_region", [inout(w), job.field("arm")])
        f.call("emit", [inout(w), L.Op.OpJump, u32(0), u32(0)], dest=pc)
        f.call("push_patch", [inout(w), pc])
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("code").at(job.field("mark")).field("alt"), w.field("code").len())
        f.set(branch, w.field("nodes").at(job.field("cur")).field("nxt"))

    last = tmp(f, boolean, w.field("nodes").at(branch).field("nxt") == u32(0))
    # One branch compiles to no split and no jump, so there is no alternation
    # to price and no region to claim there is one.
    single = tmp(f, boolean, land(job.field("phase") == u32(0), last))

    # The alternation opens where its first split will go, so before it goes.
    inside = tmp(f, u32, job.field("here"))
    with f.if_(lnot(single)):
        with f.if_(job.field("phase") == u32(0)):
            f.call(
                "open_region", [inout(w), L.Rk.RkAlt, job.field("here")], dest=inside
            )
            f.set(w.field("jobs").at(top).field("here"), inside)

    with f.if_(last):
        f.set(w.field("jobs").at(top).field("phase"), u32(2))
        with f.if_(single):
            f.set(w.field("jobs").at(top).field("phase"), u32(3))
    with f.else_():
        f.call("emit", [inout(w), L.Op.OpSplit, u32(0), u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("code").at(pc).field("arg"), pc + u32(1))
        f.set(w.field("jobs").at(top).field("mark"), pc)
        f.set(w.field("jobs").at(top).field("phase"), u32(1))

    # And a branch opens after the split that guards it, or after the jump the
    # branch before it left by.
    with f.if_(lnot(single)):
        opened = tmp(f, u32, u32(0))
        f.call("open_region", [inout(w), L.Rk.RkBranch, inside], dest=opened)
        f.set(w.field("jobs").at(top).field("arm"), opened)
        f.set(inside, opened)
    f.set(w.field("jobs").at(top).field("cur"), branch)
    f.call("push_job", [inout(w), branch, inside])


def _repeat(L: Layout) -> None:
    f = L.func(
        "walk_repeat",
        params=[
            ("w", L.Work, "inout"),
            ("top", u32),
            ("job", L.Job),
            ("nd", L.Node),
        ],
    )
    w = f["w"]
    job = f["job"]
    nd = f["nd"]
    top = tmp(f, u32, f["top"])
    done = tmp(f, L.Job)
    pc = tmp(f, u32, u32(0))
    greedy = tmp(f, boolean, nd.field("opts") != u32(0))

    with f.if_(job.field("phase") == u32(1)):
        # An optional item: the split's two arms are the body and what follows.
        sp = tmp(f, u32, job.field("mark"))
        stop = tmp(f, u32, w.field("code").len())
        with f.if_(greedy):
            f.set(w.field("code").at(sp).field("arg"), sp + u32(1))
            f.set(w.field("code").at(sp).field("alt"), stop)
        with f.else_():
            f.set(w.field("code").at(sp).field("arg"), stop)
            f.set(w.field("code").at(sp).field("alt"), sp + u32(1))
        f.call("close_region", [inout(w), job.field("here")])
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(2)):
        r = tmp(f, u32, job.field("mark"))
        f.call("emit", [inout(w), L.Op.OpRepNext, r, u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("reps").at(r).field("after"), w.field("code").len())
        f.call("close_region", [inout(w), job.field("here")])
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(3)):
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(4)):
        f.call("walk_lowered", [inout(w), top, job, nd])
        f.ret()

    lo = tmp(f, u32, nd.field("val"))
    hi = tmp(f, u32, nd.field("aux"))
    body = tmp(f, u32, nd.field("first"))

    with f.if_(hi == u32(0)):
        f.pop(w.field("jobs"), done)
        f.ret()
    # Repeated once is the body and nothing else, so it is priced as the body.
    with f.if_(land(lo == u32(1), hi == u32(1))):
        f.set(w.field("jobs").at(top).field("phase"), u32(3))
        f.call("push_job", [inout(w), body, job.field("here")])
        f.ret()

    # The three spellings that are already in star form keep their own
    # emission: the one-split optional, and the native pure star. Everything
    # else is what the lowering is for, and on a pattern the pre-check and the
    # dry run cleared it goes to `walk_lowered` without opening a region of its
    # own — the copies are a concatenation, and a concatenation opens none.
    with f.if_(
        land(
            w.field("lowering"),
            lnot(
                lor(
                    land(lo == u32(0), hi == u32(1)),
                    land(lo == u32(0), hi == u32(spec.NONE)),
                )
            ),
        )
    ):
        f.set(w.field("jobs").at(top).field("cur"), u32(0))
        f.set(w.field("jobs").at(top).field("phase"), u32(4))
        f.ret()

    # Everything below opens a region, and it opens before the first
    # instruction of the shape BOUNDS.md section 4.4 will read back.
    mine = tmp(f, u32, u32(0))
    f.call("open_region", [inout(w), L.Rk.RkRepeat, job.field("here")], dest=mine)
    f.set(w.field("jobs").at(top).field("here"), mine)

    with f.if_(land(lo == u32(0), hi == u32(1))):
        f.call("emit", [inout(w), L.Op.OpSplit, u32(0), u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("jobs").at(top).field("mark"), pc)
        f.set(w.field("jobs").at(top).field("phase"), u32(1))
        f.call("push_job", [inout(w), body, mine])
        f.ret()

    r = tmp(f, u32, u32(0))
    f.call("new_rep", [inout(w)], dest=r)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    f.call("emit", [inout(w), L.Op.OpRepZero, r, u32(0)], dest=pc)
    head = tmp(f, u32, u32(0))
    f.call("emit", [inout(w), L.Op.OpRepLoop, r, u32(0)], dest=head)
    f.call("emit", [inout(w), L.Op.OpRepEnter, r, u32(0)], dest=pc)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    f.set(w.field("reps").at(r).field("lo"), lo)
    f.set(w.field("reps").at(r).field("hi"), hi)
    f.set(w.field("reps").at(r).field("greedy"), greedy)
    f.set(w.field("reps").at(r).field("head"), head)
    f.set(w.field("reps").at(r).field("body"), head + u32(1))
    f.set(w.field("jobs").at(top).field("mark"), r)
    f.set(w.field("jobs").at(top).field("phase"), u32(2))
    f.call("push_job", [inout(w), body, mine])

    _lowered(L)


def _lowered(L: Layout) -> None:
    """A counted repetition in star form, one copy per visit.

    The copies are emitted into the parent's region, side by side, and the
    trailing optionals nest so that the k-th copy's presence is decided before
    the (k+1)-th's — which is what makes the count preference pcre2's. They all
    end at the same instruction, and each one's region opens exactly where its
    own split goes, so the innermost region's chain of parents is the stack of
    splits waiting to be patched and of regions waiting to be closed. No second
    array holds it.
    """
    f = L.func(
        "walk_lowered",
        params=[
            ("w", L.Work, "inout"),
            ("top", u32),
            ("job", L.Job),
            ("nd", L.Node),
        ],
    )
    w = f["w"]
    job = f["job"]
    nd = f["nd"]
    top = tmp(f, u32, f["top"])
    done = tmp(f, L.Job)
    pc = tmp(f, u32, u32(0))
    greedy = tmp(f, boolean, nd.field("opts") != u32(0))
    lo = tmp(f, u32, nd.field("val"))
    hi = tmp(f, u32, nd.field("aux"))
    body = tmp(f, u32, nd.field("first"))
    cur = tmp(f, u32, job.field("cur"))

    # The copies the minimum demands, each one an ordinary child of whatever
    # region the quantifier itself sits in.
    with f.if_(cur < lo):
        f.set(w.field("jobs").at(top).field("cur"), cur + u32(1))
        f.call("push_job", [inout(w), body, job.field("here")])
        f.ret()

    # No maximum: what is left is the native pure star, counter and all, which
    # is the one form `pike_ok` admits.
    with f.if_(hi == u32(spec.NONE)):
        mine = tmp(f, u32, u32(0))
        f.call("open_region", [inout(w), L.Rk.RkRepeat, job.field("here")], dest=mine)
        r = tmp(f, u32, u32(0))
        f.call("new_rep", [inout(w)], dest=r)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("jobs").at(top).field("here"), mine)
        f.call("emit", [inout(w), L.Op.OpRepZero, r, u32(0)], dest=pc)
        head = tmp(f, u32, u32(0))
        f.call("emit", [inout(w), L.Op.OpRepLoop, r, u32(0)], dest=head)
        f.call("emit", [inout(w), L.Op.OpRepEnter, r, u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("reps").at(r).field("lo"), u32(0))
        f.set(w.field("reps").at(r).field("hi"), u32(spec.NONE))
        f.set(w.field("reps").at(r).field("greedy"), greedy)
        f.set(w.field("reps").at(r).field("head"), head)
        f.set(w.field("reps").at(r).field("body"), head + u32(1))
        f.set(w.field("jobs").at(top).field("mark"), r)
        f.set(w.field("jobs").at(top).field("phase"), u32(2))
        f.call("push_job", [inout(w), body, mine])
        f.ret()

    # One more optional copy: its split, then the copy inside it.
    with f.if_(cur < hi):
        mine = tmp(f, u32, u32(0))
        f.call("open_region", [inout(w), L.Rk.RkRepeat, job.field("here")], dest=mine)
        f.call("emit", [inout(w), L.Op.OpSplit, u32(0), u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("jobs").at(top).field("here"), mine)
        f.set(w.field("jobs").at(top).field("cur"), cur + u32(1))
        f.call("push_job", [inout(w), body, mine])
        f.ret()

    # Every copy is placed. Each optional's split takes the body first when the
    # quantifier is greedy and the exit first when it is lazy, and every one of
    # them exits here.
    stop = tmp(f, u32, w.field("code").len())
    at = tmp(f, u32, job.field("here"))
    left = tmp(f, u32, hi - lo)
    with f.while_(left > u32(0), left.cast(counter)):
        f.set(left, left - u32(1))
        sp = tmp(f, u32, w.field("regions").at(at).field("lo"))
        with f.if_(greedy):
            f.set(w.field("code").at(sp).field("arg"), sp + u32(1))
            f.set(w.field("code").at(sp).field("alt"), stop)
        with f.else_():
            f.set(w.field("code").at(sp).field("arg"), stop)
            f.set(w.field("code").at(sp).field("alt"), sp + u32(1))
        f.call("close_region", [inout(w), at])
        f.set(at, w.field("regions").at(at).field("parent"))
    f.pop(w.field("jobs"), done)


def _first(L: Layout) -> None:
    """Can a match begin by consuming a CR?

    Only one bit of the classic start-of-match analysis is needed here, and it
    is needed for correctness rather than for speed: pcre2 declines to start a
    match between a CR and a LF (DESIGN.md section 4.3), but only when it has
    actually attempted the CR position, and its own start-code-unit filter may
    have jumped straight past it. So the bumpalong rule asks this question, and
    the answer is deliberately conservative — an unknown is a yes, which is the
    same answer pcre2 reaches when its filter is not built at all.

    The walk is a worklist over the bytecode reachable without consuming a
    byte, with a visited bit per instruction, so it terminates on any program.
    """
    f = L.func("scan_first", params=[("w", L.Work, "inout")])
    w = f["w"]
    total = tmp(f, u32, w.field("code").len())
    k = tmp(f, u32, u32(0))
    words = tmp(f, u32, total.shr(3) + u32(1))
    with f.while_(k < words, down(words, k)):
        f.push(w.field("seen"), u8(0))
        f.set(k, k + u32(1))
    f.call("mark_seen", [inout(w), u32(0)])
    fuel = tmp(f, counter, counter(2 * spec.MAX_CODE))

    with f.while_(
        land(w.field("pending").len() > u32(0), fuel > counter(0)), fuel
    ):
        f.set(fuel, fuel - counter(1))
        pc = tmp(f, u32, u32(0))
        f.pop(w.field("pending"), pc)
        inst = tmp(f, L.Inst, w.field("code").at(pc))
        arg = tmp(f, u32, inst.field("arg"))

        with f.switch(inst.field("op")) as arm:
            with arm.case("OpChar"):
                with f.if_(arg == u32(0x0D)):
                    f.set(w.field("crfirst"), u32(1))
            with arm.case("OpCharCI"):
                with f.if_(arg == u32(0x0D)):
                    f.set(w.field("crfirst"), u32(1))
            with arm.case("OpClass"):
                at = tmp(f, u32, arg * u32(32) + u32(0x0D // 8))
                with f.if_((w.field("classes").at(at) & u8(1 << (0x0D % 8))) != u8(0)):
                    f.set(w.field("crfirst"), u32(1))
            with arm.case("OpSplit"):
                f.call("mark_seen", [inout(w), arg])
                f.call("mark_seen", [inout(w), inst.field("alt")])
            with arm.case("OpJump"):
                f.call("mark_seen", [inout(w), arg])
            with arm.case("OpRepLoop"):
                rep = tmp(f, L.Rep, w.field("reps").at(arg))
                f.call("mark_seen", [inout(w), rep.field("body")])
                with f.if_(rep.field("lo") == u32(0)):
                    f.call("mark_seen", [inout(w), rep.field("after")])
            with arm.case("OpRepNext"):
                rep = tmp(f, L.Rep, w.field("reps").at(arg))
                f.call("mark_seen", [inout(w), rep.field("head")])
                f.call("mark_seen", [inout(w), rep.field("after")])
            # A pattern that can reach its own end, or one whose first byte
            # this walk cannot enumerate, gets the conservative answer.
            for name in ("OpAny", "OpAnyNoNL", "OpBsr", "OpAccept"):
                with arm.case(name):
                    f.set(w.field("crfirst"), u32(1))
            for name in (
                "OpSave",
                "OpRepZero",
                "OpRepEnter",
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
            ):
                with arm.case(name):
                    f.call("mark_seen", [inout(w), pc + u32(1)])

    with f.if_(fuel == counter(0)):
        f.set(w.field("crfirst"), u32(1))

    f = L.func("mark_seen", params=[("w", L.Work, "inout"), ("pc", u32)])
    w = f["w"]
    pc = tmp(f, u32, f["pc"])
    with f.if_(pc >= w.field("code").len()):
        f.ret()
    at = tmp(f, u32, pc.shr(3))
    bit = tmp(f, u8, L.BITS.at(pc & u32(7)))
    with f.if_((w.field("seen").at(at) & bit) != u8(0)):
        f.ret()
    f.set(w.field("seen").at(at), w.field("seen").at(at) | bit)
    f.push(w.field("pending"), pc)
