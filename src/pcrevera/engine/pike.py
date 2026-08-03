"""The Pike VM: the lockstep matcher, written in TIR.

DESIGN.md section 4.3 spells out what this has to be: a breadth-first
simulation whose thread list is kept in priority order, so that list order is
exactly the backtracking matcher's preference order and the two agree answer
for answer on every pattern both may run. The epsilon closure at each position
is expanded depth-first in split order; the per-position visited set is keyed
by pc, and the first thread to reach a pc wins and keeps its captures; a
thread that reaches Accept records its match and kills everything below it,
while the threads above it keep running and may overwrite it.

Keying the visited set by pc alone is only sound when pc determines a
thread's future, which is what `pike_ok` decides. Every repetition must be a
pure star — lower bound zero, no upper bound — because then the four Rep
opcodes never read their counter to decide anything; nothing may consume a
variable number of bytes, which rules out \\R until it learns to compile as an
alternation; and no star's body may be able to complete without consuming.

The last condition is not about termination but about captures, and it is
where a first try went wrong. With a nullable body the backtracking matcher
runs one last empty iteration and keeps its Saves — `(a?)*` on "a" reports
the group at the empty (1,1), not the consuming (0,1) — and that preferred
path re-executes body instructions the closure has already marked, since the
thread it grows from was suspended mid-body. A visited set keyed by pc kills
it and hands the answer to the wrong path. When every completed iteration
consumes, the non-consuming transition graph is acyclic, each closure reaches
every pc at most once, and depth-first order in split order really is the
backtracking preference order, first arrival winning exactly. Nullable-body
stars stay on the backtracking matcher until they get a mechanism of their
own, which is a smaller loss than it sounds: the empty-match rule makes such
patterns quadratic-at-best there anyway.

On an eligible program this matcher reads the same bytecode the backtracking
VM runs, treating RepZero and RepEnter as epsilons and RepLoop and RepNext as
the fork their control flow amounts to — one more iteration first or the exit
first, by greediness.

Capture slots use the pooled copy-on-write scheme of DESIGN.md section 4.3:
one flat slot pool, a refcount per block, a free list, and each thread holding
an integer handle, so forking a thread is a handle copy and a refcount bump.
A Save through a shared handle first copies the block, charged per slot under
the section 5 cost model like every other piece of work here: one unit per
instruction visit, one per IR byte initialized or copied, growth charged
before it happens through the same `charge_grow` the backtracking VM uses.

The backtrack stack does not exist on this path, so the stack-entry limit can
never be exceeded and the reported stack usage is zero; the thread lists, the
closure stack, the pool and the visited set are all scratch, accounted against
the memory limit.
"""

from __future__ import annotations

from ..dsl import boolean, bytes_, counter, inout, land, lnot, lor, u32, u8
from . import spec
from .bounds import const, linear, poly, zero
from .layout import Layout
from .parser import down, tmp

# The five accounting parameters every charging helper threads through, spelled
# once so a sixth would land everywhere at once.
CHARGE = (
    ("mem", counter, "inout"),
    ("peak", counter, "inout"),
    ("cost", counter, "inout"),
    ("memlimit", counter),
    ("costlimit", counter),
)


def build(L: Layout) -> None:
    _eligibility(L)
    _pool(L)
    _pushes(L)
    _closure(L)
    _match(L)
    _certificate(L)


def _eligibility(L: Layout) -> None:
    f = L.func("pike_ok", params=[("re", L.Re)], ret=boolean)
    reps = f["re"].field("reps")
    code = f["re"].field("code")
    i = tmp(f, u32, u32(0))
    with f.while_(i < reps.len(), down(reps.len(), i)):
        r = tmp(f, L.Rep, reps.at(i))
        with f.if_(
            lor(r.field("lo") != u32(0), r.field("hi") != u32(spec.NONE))
        ):
            f.ret(boolean(False))
        empty = tmp(f, boolean, boolean(True))
        f.call("pike_hollow", [f["re"], i], dest=empty)
        with f.if_(empty):
            f.ret(boolean(False))
        f.set(i, i + u32(1))
    pc = tmp(f, u32, u32(0))
    with f.while_(pc < code.len(), down(code.len(), pc)):
        with f.if_(code.at(pc).field("op") == L.Op.OpBsr):
            f.ret(boolean(False))
        f.set(pc, pc + u32(1))
    f.ret(boolean(True))

    # Whether one star's body can complete an iteration without consuming a
    # byte: a worklist over the non-consuming transitions from the body's
    # first instruction, asking whether its own RepNext is reachable.
    # Assertions count as non-consuming, which errs toward "it can" — the
    # safe direction, since a pattern this refuses merely stays on the
    # backtracking matcher. The answer defaults the same way: a walk that
    # meets anything unexpected reports hollow rather than eligible.
    f = L.func("pike_hollow", params=[("re", L.Re), ("which", u32)], ret=boolean)
    code = f["re"].field("code")
    reps = f["re"].field("reps")
    mine = tmp(f, L.Rep, reps.at(f["which"]))
    goal = tmp(f, u32, mine.field("after") - u32(1))
    total = tmp(f, u32, code.len())
    seen = f.let("seen", bytes_)
    words = tmp(f, u32, total.shr(3) + u32(1))
    k = tmp(f, u32, u32(0))
    f.reserve(seen, words)
    with f.while_(k < words, down(words, k)):
        f.push(seen, u8(0))
        f.set(k, k + u32(1))
    pending = f.let("pending", L.Steps)
    f.push(pending, mine.field("body"))
    slack = tmp(f, counter, total.cast(counter) * counter(2))

    with f.while_(
        pending.len() > u32(0), pending.len().cast(counter) + slack
    ):
        pc = tmp(f, u32, u32(0))
        f.pop(pending, pc)
        with f.if_(pc >= total):
            f.ret(boolean(True))
        with f.if_(pc == goal):
            f.ret(boolean(True))
        at = tmp(f, u32, pc.shr(3))
        bit = tmp(f, u8, L.BITS.at(pc & u32(7)))
        with f.if_((seen.at(at) & bit) != u8(0)):
            f.cont()
        f.set(seen.at(at), seen.at(at) | bit)
        f.set(slack, slack - counter(2))
        inst = tmp(f, L.Inst, code.at(pc))
        with f.switch(inst.field("op")) as arm:
            for name in (
                "OpChar",
                "OpCharCI",
                "OpClass",
                "OpAny",
                "OpAnyNoNL",
                "OpBsr",
                "OpAccept",
            ):
                with arm.case(name):
                    # Consuming, or the end of the program: this path cannot
                    # complete the iteration emptily.
                    pass
            with arm.case("OpSplit"):
                f.push(pending, inst.field("arg"))
                f.push(pending, inst.field("alt"))
            with arm.case("OpJump"):
                f.push(pending, inst.field("arg"))
            with arm.case("OpRepLoop"):
                inner = tmp(f, L.Rep, reps.at(inst.field("arg")))
                f.push(pending, inner.field("body"))
                f.push(pending, inner.field("after"))
            with arm.case("OpRepNext"):
                inner = tmp(f, L.Rep, reps.at(inst.field("arg")))
                f.push(pending, inner.field("head"))
                f.push(pending, inner.field("after"))
            with arm.otherwise():
                # Saves, repetition bookkeeping, and every assertion.
                f.push(pending, pc + u32(1))
    f.ret(boolean(False))


def _pool(L: Layout) -> None:
    """The copy-on-write capture pool.

    A handle is an index into the refcount table, and a block is `novec`
    consecutive slots of the flat pool at `handle * novec`. Taking a block
    reserves it and nothing more: every caller overwrites all of it — the
    seed with unset slots, the copy-on-write path with the shared block's
    values — and charges that fill itself, so initialization is paid exactly
    once wherever the block came from.
    """
    f = L.func(
        "pike_take",
        params=[
            ("pool", L.Slots, "inout"),
            ("rc", L.Blocks, "inout"),
            ("free", L.Blocks, "inout"),
            ("novec", u32),
            *CHARGE,
        ],
        ret=u32,
    )
    with f.if_(f["free"].len() > u32(0)):
        held = tmp(f, u32, u32(0))
        f.pop(f["free"], held)
        f.set(f["rc"].at(held), u32(1))
        f.ret(held)
    h = tmp(f, u32, f["rc"].len())
    with f.if_(h >= u32(spec.MAX_BLOCKS)):
        # Unreachable while MAX_BLOCKS bounds the live handles, which section
        # 5's Pike accounting argues; refusing is what keeps this total.
        f.ret(u32(spec.NONE))
    room = tmp(f, boolean, boolean(False))
    f.call(
        "charge_grow",
        [
            f["rc"].cap(),
            f["rc"].len(),
            u32(4),
            u32(spec.MAX_BLOCKS),
            inout(f["mem"]),
            inout(f["peak"]),
            inout(f["cost"]),
            f["memlimit"],
            f["costlimit"],
        ],
        dest=room,
    )
    with f.if_(lnot(room)):
        f.ret(u32(spec.NONE))
    f.push(f["rc"], u32(1))
    k = tmp(f, u32, u32(0))
    with f.while_(k < f["novec"], down(f["novec"], k)):
        f.call(
            "charge_grow",
            [
                f["pool"].cap(),
                f["pool"].len(),
                u32(4),
                u32(spec.MAX_POOL),
                inout(f["mem"]),
                inout(f["peak"]),
                inout(f["cost"]),
                f["memlimit"],
                f["costlimit"],
            ],
            dest=room,
        )
        with f.if_(lnot(room)):
            f.ret(u32(spec.NONE))
        f.push(f["pool"], u32(spec.UNSET))
        f.set(k, k + u32(1))
    f.ret(h)

    f = L.func(
        "pike_drop",
        params=[
            ("rc", L.Blocks, "inout"),
            ("free", L.Blocks, "inout"),
            ("h", u32),
            *CHARGE,
        ],
        ret=boolean,
    )
    with f.if_(f["h"] == u32(spec.NONE)):
        f.ret(boolean(True))
    left = tmp(f, u32, f["rc"].at(f["h"]) - u32(1))
    f.set(f["rc"].at(f["h"]), left)
    with f.if_(left == u32(0)):
        room = tmp(f, boolean, boolean(False))
        f.call(
            "charge_grow",
            [
                f["free"].cap(),
                f["free"].len(),
                u32(4),
                u32(spec.MAX_BLOCKS),
                inout(f["mem"]),
                inout(f["peak"]),
                inout(f["cost"]),
                f["memlimit"],
                f["costlimit"],
            ],
            dest=room,
        )
        with f.if_(lnot(room)):
            f.ret(boolean(False))
        f.push(f["free"], f["h"])
    f.ret(boolean(True))

    f = L.func(
        "pike_write",
        params=[
            ("pool", L.Slots, "inout"),
            ("rc", L.Blocks, "inout"),
            ("free", L.Blocks, "inout"),
            ("novec", u32),
            ("h", u32, "inout"),
            ("slot", u32),
            ("value", u32),
            *CHARGE,
        ],
        ret=boolean,
    )
    novec = f["novec"]
    with f.if_(f["rc"].at(f["h"]) > u32(1)):
        copied = tmp(f, counter, novec.cast(counter) * counter(spec.REG_SIZE))
        with f.if_(copied > f["costlimit"] - f["cost"]):
            f.ret(boolean(False))
        f.set(f["cost"], f["cost"] + copied)
        fresh = tmp(f, u32, u32(spec.NONE))
        f.call(
            "pike_take",
            [
                inout(f["pool"]),
                inout(f["rc"]),
                inout(f["free"]),
                novec,
                inout(f["mem"]),
                inout(f["peak"]),
                inout(f["cost"]),
                f["memlimit"],
                f["costlimit"],
            ],
            dest=fresh,
        )
        with f.if_(fresh == u32(spec.NONE)):
            f.ret(boolean(False))
        taken = tmp(f, u32, fresh * novec)
        held = tmp(f, u32, f["h"] * novec)
        k = tmp(f, u32, u32(0))
        with f.while_(k < novec, down(novec, k)):
            f.set(f["pool"].at(taken + k), f["pool"].at(held + k))
            f.set(k, k + u32(1))
        f.set(f["rc"].at(f["h"]), f["rc"].at(f["h"]) - u32(1))
        f.set(f["h"], fresh)
    f.set(f["pool"].at(f["h"] * novec + f["slot"]), f["value"])
    f.ret(boolean(True))


def _pushes(L: Layout) -> None:
    """One growth-checked push per array a thread can land on."""
    for name, vec_type, maximum in (
        ("pike_defer", L.Closure, spec.MAX_CLOSURE),
        ("pike_park", L.Threads, spec.MAX_THREADS),
    ):
        f = L.func(
            name,
            params=[
                ("held", vec_type, "inout"),
                ("pcv", u32),
                ("hv", u32),
                *CHARGE,
            ],
            ret=boolean,
        )
        room = tmp(f, boolean, boolean(False))
        f.call(
            "charge_grow",
            [
                f["held"].cap(),
                f["held"].len(),
                u32(spec.TH_SIZE),
                u32(maximum),
                inout(f["mem"]),
                inout(f["peak"]),
                inout(f["cost"]),
                f["memlimit"],
                f["costlimit"],
            ],
            dest=room,
        )
        with f.if_(lnot(room)):
            f.ret(boolean(False))
        f.push(f["held"], L.Th.of(pc=f["pcv"], h=f["hv"]))
        f.ret(boolean(True))


def _closure(L: Layout) -> None:
    """The epsilon closure, depth-first in split order.

    Expands from one starting thread and appends every suspension — a
    consuming instruction or Accept — to the list in exactly the order the
    backtracking matcher would reach them, which is what makes list order
    preference order. The explicit stack is LIFO, so a fork pushes its second
    choice first; the visited set admits each pc once per position, and the
    loser of a race hands its capture block back.

    The variant needs one word: an iteration either marks an unseen pc,
    pushing at most two continuations, or pops a seen one and nothing else,
    so the stack length plus twice the unseen count strictly falls.
    """
    f = L.func(
        "pike_add",
        params=[
            ("list", L.Threads, "inout"),
            ("stk", L.Closure, "inout"),
            ("seen", bytes_, "inout"),
            ("pool", L.Slots, "inout"),
            ("rc", L.Blocks, "inout"),
            ("free", L.Blocks, "inout"),
            ("code", L.FrozenCode),
            ("reps", L.FrozenReps),
            ("subj", L.frozen_bytes),
            ("pos", u32),
            ("novec", u32),
            ("nltype", u32),
            ("notbol", boolean),
            ("noteol", boolean),
            ("pc0", u32),
            ("h0", u32),
            *CHARGE,
        ],
        ret=boolean,
    )
    code = f["code"]
    subj = f["subj"]
    pos = f["pos"]
    nltype = f["nltype"]
    n = tmp(f, u32, subj.len())
    okv = tmp(f, boolean, boolean(False))

    def charged(args) -> list:
        return [
            *args,
            inout(f["mem"]),
            inout(f["peak"]),
            inout(f["cost"]),
            f["memlimit"],
            f["costlimit"],
        ]

    def defer(pcv, hv) -> None:
        f.call("pike_defer", charged([inout(f["stk"]), pcv, hv]), dest=okv)
        with f.if_(lnot(okv)):
            f.ret(boolean(False))

    def drop(hv) -> None:
        f.call("pike_drop", charged([inout(f["rc"]), inout(f["free"]), hv]), dest=okv)
        with f.if_(lnot(okv)):
            f.ret(boolean(False))

    defer(f["pc0"], f["h0"])
    slack = tmp(f, counter, code.len().cast(counter) * counter(2))

    with f.while_(
        f["stk"].len() > u32(0), f["stk"].len().cast(counter) + slack
    ):
        th = tmp(f, L.Th)
        f.pop(f["stk"], th)
        pc = tmp(f, u32, th.field("pc"))
        h = tmp(f, u32, th.field("h"))
        at = tmp(f, u32, pc.shr(3))
        bit = tmp(f, u8, L.BITS.at(pc & u32(7)))
        with f.if_((f["seen"].at(at) & bit) != u8(0)):
            drop(h)
            f.cont()
        f.set(f["seen"].at(at), f["seen"].at(at) | bit)
        f.set(slack, slack - counter(2))
        with f.if_(counter(1) > f["costlimit"] - f["cost"]):
            f.ret(boolean(False))
        f.set(f["cost"], f["cost"] + counter(1))
        inst = tmp(f, L.Inst, code.at(pc))

        def hold(test) -> None:
            with f.if_(test):
                defer(pc + u32(1), h)
            with f.else_():
                drop(h)

        def fork(first, second) -> None:
            f.set(f["rc"].at(h), f["rc"].at(h) + u32(1))
            defer(second, h)
            defer(first, h)

        with f.switch(inst.field("op")) as arm:
            for name in ("OpChar", "OpCharCI", "OpClass", "OpAny", "OpAnyNoNL", "OpAccept"):
                with arm.case(name):
                    f.call(
                        "pike_park",
                        charged([inout(f["list"]), pc, h]),
                        dest=okv,
                    )
                    with f.if_(lnot(okv)):
                        f.ret(boolean(False))
            with arm.case("OpBsr"):
                # `pike_ok` has already refused any program carrying one; the
                # arm keeps the switch total, and dying here is the honest
                # reading of an instruction this matcher must never meet.
                drop(h)
            with arm.case("OpSplit"):
                fork(inst.field("arg"), inst.field("alt"))
            with arm.case("OpJump"):
                defer(inst.field("arg"), h)
            with arm.case("OpSave"):
                f.call(
                    "pike_write",
                    charged(
                        [
                            inout(f["pool"]),
                            inout(f["rc"]),
                            inout(f["free"]),
                            f["novec"],
                            inout(h),
                            inst.field("arg"),
                            pos,
                        ]
                    ),
                    dest=okv,
                )
                with f.if_(lnot(okv)):
                    f.ret(boolean(False))
                defer(pc + u32(1), h)

            with arm.case("OpCirc"):
                hold(land(pos == u32(0), lnot(f["notbol"])))
            with arm.case("OpCircM"):
                ok = tmp(f, boolean, lnot(f["notbol"]))
                with f.if_(pos != u32(0)):
                    back = tmp(f, u32, u32(0))
                    f.call("newline_before", [subj, pos, nltype], dest=back)
                    f.set(ok, land(pos != n, back != u32(0)))
                hold(ok)
            with arm.case("OpDoll"):
                ends = tmp(f, boolean, boolean(False))
                f.call("at_line_end", [subj, pos, nltype], dest=ends)
                hold(land(lnot(f["noteol"]), ends))
            with arm.case("OpDollE"):
                hold(land(lnot(f["noteol"]), pos == n))
            with arm.case("OpDollM"):
                ok = tmp(f, boolean, lnot(f["noteol"]))
                with f.if_(pos < n):
                    here = tmp(f, u32, u32(0))
                    f.call("newline_at", [subj, pos, nltype], dest=here)
                    f.set(ok, here != u32(0))
                hold(ok)
            with arm.case("OpSod"):
                hold(pos == u32(0))
            with arm.case("OpEod"):
                hold(pos == n)
            with arm.case("OpEodn"):
                ends = tmp(f, boolean, boolean(False))
                f.call("at_line_end", [subj, pos, nltype], dest=ends)
                hold(ends)
            with arm.case("OpWordB"):
                f.call("word_edge", [subj, pos], dest=okv)
                hold(okv)
            with arm.case("OpNotWordB"):
                f.call("word_edge", [subj, pos], dest=okv)
                hold(lnot(okv))

            # RepEnter's mark in the visited set is the empty-match rule: a
            # loop path that comes back to it without consuming has already
            # been, and dies.
            for name in ("OpRepZero", "OpRepEnter"):
                with arm.case(name):
                    defer(pc + u32(1), h)
            # Another iteration first or the exit first, by greediness — the
            # same preference the backtracking matcher shows at the head —
            # with RepNext's body arm pointing past the head so an empty
            # iteration meets its own RepEnter mark rather than looping.
            for name in ("OpRepLoop", "OpRepNext"):
                with arm.case(name):
                    rep = tmp(f, L.Rep, f["reps"].at(inst.field("arg")))
                    with f.if_(rep.field("greedy")):
                        fork(rep.field("body"), rep.field("after"))
                    with f.else_():
                        fork(rep.field("after"), rep.field("body"))
    f.ret(boolean(True))


def _match(L: Layout) -> None:
    """The lockstep scan.

    One pass over the subject. At each position the current list is seeded —
    lowest priority, so an earlier start always outranks a later one, which
    is leftmost — then stepped in order, survivors closing over into the next
    list. A recorded match stops the seeding and kills everything below the
    thread that found it; the threads above it keep running and may replace
    it with an earlier-starting or higher-preference answer.

    The signature is the backtracking matcher's, stack limit included, so the
    two are callable interchangeably; the stack limit simply has nothing to
    refuse here, and the reported stack usage is zero.
    """
    f = L.func(
        "pike_match",
        params=[
            ("re", L.Re),
            ("subj", L.frozen_bytes),
            ("start", u32),
            ("mopts", u32),
            ("costlimit", counter),
            ("stacklimit", u32),
            ("memlimit", counter),
            ("ov", L.Ovec, "inout"),
            ("use", L.Usage, "inout"),
        ],
        ret=u32,
    )
    re = f["re"]
    subj = f["subj"]
    mopts = f["mopts"]
    costlimit = f["costlimit"]
    memlimit = f["memlimit"]
    ov = f["ov"]

    n = tmp(f, u32, subj.len())
    cost = tmp(f, counter, counter(0))
    mem = tmp(f, counter, counter(0))
    peak = tmp(f, counter, counter(0))
    f.set(f["use"].field("cost"), cost)
    f.set(f["use"].field("stack"), u32(0))
    f.set(f["use"].field("mem"), peak)
    # A program compilation did not route here is refused before anything
    # runs, the deterministic BadInput DESIGN.md section 6 gives `Exec` on a
    # configuration the pattern is not eligible for. Decided in the engine
    # rather than left to callers, because this matcher reads the Rep opcodes
    # as pure-star forks and would answer an ineligible program wrongly
    # instead of loudly.
    with f.if_(lnot(re.field("pike"))):
        f.ret(u32(spec.BAD_INPUT))
    with f.if_(f["start"] > n):
        f.ret(u32(spec.BAD_INPUT))

    code = f.let("code", L.FrozenCode, re.field("code"))
    reps = f.let("reps", L.FrozenReps, re.field("reps"))
    classes = f.let("classes", L.frozen_bytes, re.field("classes"))
    nltype = tmp(f, u32, re.field("nltype"))
    ncap = tmp(f, u32, re.field("ncap"))
    novec = tmp(f, u32, (ncap + u32(1)) * u32(2))
    anchored = tmp(
        f,
        boolean,
        lor(
            (re.field("opts") & u32(spec.ANCHORED)) != u32(0),
            (mopts & u32(spec.MATCH_ANCHORED)) != u32(0),
        ),
    )
    notempty = tmp(f, boolean, (mopts & u32(spec.NOTEMPTY)) != u32(0))
    notempty_at = tmp(f, boolean, (mopts & u32(spec.NOTEMPTY_ATSTART)) != u32(0))
    nocrlf = tmp(f, boolean, re.field("hascrlf") == u32(0))
    crlfish = tmp(
        f,
        boolean,
        lor(
            nltype == u32(spec.NL_CRLF),
            lor(nltype == u32(spec.NL_ANYCRLF), nltype == u32(spec.NL_ANY)),
        ),
    )
    notbol = tmp(f, boolean, (mopts & u32(spec.NOTBOL)) != u32(0))
    noteol = tmp(f, boolean, (mopts & u32(spec.NOTEOL)) != u32(0))

    clist = f.let("clist", L.Threads)
    nlist = f.let("nlist", L.Threads)
    stk = f.let("stk", L.Closure)
    seen = f.let("seen", bytes_)
    pool = f.let("pool", L.Slots)
    rc = f.let("rc", L.Blocks)
    free = f.let("free", L.Blocks)

    # The ovector and the visited set are sized once and their zeroing is
    # charged, the same rule as the backtracking matcher's register file.
    words = tmp(f, u32, code.len().shr(3) + u32(1))
    setup = tmp(
        f,
        counter,
        novec.cast(counter) * counter(spec.REG_SIZE) + words.cast(counter),
    )
    with f.if_(lor(setup > memlimit, setup > costlimit)):
        f.ret(u32(spec.RESOURCE_EXCEEDED))
    f.set(mem, setup)
    f.set(peak, setup)
    f.set(cost, setup)
    f.reserve(ov, novec)
    f.truncate(ov, u32(0))
    k = tmp(f, u32, u32(0))
    with f.while_(k < novec, down(novec, k)):
        f.push(ov, u32(spec.UNSET))
        f.set(k, k + u32(1))
    f.reserve(seen, words)
    f.set(k, u32(0))
    with f.while_(k < words, down(words, k)):
        f.push(seen, u8(0))
        f.set(k, k + u32(1))

    mh = tmp(f, u32, u32(spec.NONE))
    seeding = tmp(f, boolean, boolean(True))
    result = tmp(f, u32, u32(spec.NO_MATCH))
    running = tmp(f, boolean, boolean(True))
    pos = tmp(f, u32, f["start"])
    okv = tmp(f, boolean, boolean(False))
    block = tmp(f, counter, novec.cast(counter) * counter(spec.REG_SIZE))
    cwords = tmp(f, counter, words.cast(counter))
    crfirst = tmp(f, boolean, re.field("crfirst") != u32(0))

    def charged(args) -> list:
        return [
            *args,
            inout(mem),
            inout(peak),
            inout(cost),
            memlimit,
            costlimit,
        ]

    def blown() -> None:
        f.set(result, u32(spec.RESOURCE_EXCEEDED))
        f.set(running, boolean(False))

    def close(hv) -> None:
        """One thread into the next list, from pc+1 at the next position."""
        f.call(
            "pike_add",
            charged(
                [
                    inout(nlist),
                    inout(stk),
                    inout(seen),
                    inout(pool),
                    inout(rc),
                    inout(free),
                    code,
                    reps,
                    subj,
                    pos + u32(1),
                    novec,
                    nltype,
                    notbol,
                    noteol,
                    pc + u32(1),
                    hv,
                ]
            ),
            dest=okv,
        )
        with f.if_(lnot(okv)):
            blown()

    def drop(hv) -> None:
        f.call("pike_drop", charged([inout(rc), inout(free), hv]), dest=okv)
        with f.if_(lnot(okv)):
            blown()

    with f.while_(running, down(n + u32(2), pos)):
        # Seed at this position, lowest priority, unless a match already
        # exists — a seed could only start later, and leftmost has decided —
        # or the pattern is anchored elsewhere, or pcre2's bumpalong rule
        # declines to start between the halves of a CRLF.
        with f.if_(land(seeding, lor(lnot(anchored), pos == f["start"]))):
            skip = tmp(f, boolean, boolean(False))
            with f.if_(land(pos > f["start"], land(crlfish, nocrlf))):
                with f.if_(
                    land(
                        crfirst,
                        land(
                            subj.at(pos - u32(1)) == u8(0x0D),
                            land(pos < n, subj.at(pos) == u8(0x0A)),
                        ),
                    )
                ):
                    f.set(skip, boolean(True))
            with f.if_(lnot(skip)):
                sh = tmp(f, u32, u32(spec.NONE))
                f.call(
                    "pike_take",
                    charged([inout(pool), inout(rc), inout(free), novec]),
                    dest=sh,
                )
                with f.if_(sh == u32(spec.NONE)):
                    blown()
                with f.else_():
                    with f.if_(block > costlimit - cost):
                        blown()
                    with f.else_():
                        f.set(cost, cost + block)
                        base = tmp(f, u32, sh * novec)
                        f.set(k, u32(0))
                        with f.while_(k < novec, down(novec, k)):
                            f.set(pool.at(base + k), u32(spec.UNSET))
                            f.set(k, k + u32(1))
                        f.set(pool.at(base), pos)
                        f.call(
                            "pike_add",
                            charged(
                                [
                                    inout(clist),
                                    inout(stk),
                                    inout(seen),
                                    inout(pool),
                                    inout(rc),
                                    inout(free),
                                    code,
                                    reps,
                                    subj,
                                    pos,
                                    novec,
                                    nltype,
                                    notbol,
                                    noteol,
                                    u32(0),
                                    sh,
                                ]
                            ),
                            dest=okv,
                        )
                        with f.if_(lnot(okv)):
                            blown()

        # The marks in the visited set belong to the list just built; from
        # here on it fills for the next position's list, so it is cleared,
        # and the clearing is charged like any other zeroing.
        with f.if_(running):
            with f.if_(cwords > costlimit - cost):
                blown()
            with f.else_():
                f.set(cost, cost + cwords)
                f.set(k, u32(0))
                with f.while_(k < words, down(words, k)):
                    f.set(seen.at(k), u8(0))
                    f.set(k, k + u32(1))

        i = tmp(f, u32, u32(0))
        with f.while_(land(running, i < clist.len()), down(clist.len(), i)):
            th = tmp(f, L.Th, clist.at(i))
            pc = tmp(f, u32, th.field("pc"))
            h = tmp(f, u32, th.field("h"))
            with f.if_(counter(1) > costlimit - cost):
                blown()
                f.cont()
            f.set(cost, cost + counter(1))
            inst = tmp(f, L.Inst, code.at(pc))

            def step(test) -> None:
                with f.if_(land(pos < n, test)):
                    close(h)
                with f.else_():
                    drop(h)

            with f.switch(inst.field("op")) as arm:
                with arm.case("OpChar"):
                    step(subj.at(pos) == inst.field("arg").cast(u8))
                with arm.case("OpCharCI"):
                    step(
                        L.LOWER.at(subj.at(pos).cast(u32))
                        == inst.field("arg").cast(u8)
                    )
                with arm.case("OpClass"):
                    hit = tmp(f, boolean, boolean(False))
                    with f.if_(pos < n):
                        f.call(
                            "class_has",
                            [classes, inst.field("arg"), subj.at(pos)],
                            dest=hit,
                        )
                    step(hit)
                with arm.case("OpAny"):
                    step(boolean(True))
                with arm.case("OpAnyNoNL"):
                    nl = tmp(f, u32, u32(0))
                    with f.if_(pos < n):
                        f.call("newline_at", [subj, pos, nltype], dest=nl)
                    step(nl == u32(0))
                with arm.case("OpAccept"):
                    began = tmp(f, u32, pool.at(h * novec))
                    empty = tmp(f, boolean, began == pos)
                    refuse = tmp(
                        f,
                        boolean,
                        land(
                            empty,
                            lor(
                                notempty,
                                land(notempty_at, began == f["start"]),
                            ),
                        ),
                    )
                    with f.if_(refuse):
                        drop(h)
                    with f.else_():
                        hv = tmp(f, u32, h)
                        f.call(
                            "pike_write",
                            charged(
                                [
                                    inout(pool),
                                    inout(rc),
                                    inout(free),
                                    novec,
                                    inout(hv),
                                    u32(1),
                                    pos,
                                ]
                            ),
                            dest=okv,
                        )
                        with f.if_(lnot(okv)):
                            blown()
                        with f.else_():
                            drop(mh)
                            with f.if_(running):
                                f.set(mh, hv)
                                f.set(seeding, boolean(False))
                                f.set(result, u32(spec.MATCHED))
                                # Everything below this thread loses: a later
                                # seed or a lower-preference path can no
                                # longer produce the answer.
                                j = tmp(f, u32, i + u32(1))
                                with f.while_(
                                    land(running, j < clist.len()),
                                    down(clist.len(), j),
                                ):
                                    drop(clist.at(j).field("h"))
                                    f.set(j, j + u32(1))
                                f.set(i, clist.len())
                                f.cont()
                with arm.otherwise():
                    # The closure only ever parks a thread on a consuming
                    # instruction or Accept, so this arm is what keeps the
                    # switch total rather than a path anything reaches; a
                    # thread that somehow lands here dies, and the
                    # cross-matcher tests would say so.
                    drop(h)
            f.set(i, i + u32(1))

        with f.if_(running):
            f.truncate(clist, u32(0))
            f.swap(clist, nlist)
            with f.if_(pos >= n):
                f.set(running, boolean(False))
            with f.else_():
                with f.if_(
                    land(clist.len() == u32(0), lor(lnot(seeding), anchored))
                ):
                    f.set(running, boolean(False))
        f.set(pos, pos + u32(1))

    with f.if_(result == u32(spec.MATCHED)):
        with f.if_(block > costlimit - cost):
            f.set(result, u32(spec.RESOURCE_EXCEEDED))
        with f.else_():
            f.set(cost, cost + block)
            f.set(k, u32(0))
            with f.while_(k < novec, down(novec, k)):
                f.set(ov.at(k), pool.at(mh * novec + k))
                f.set(k, k + u32(1))
    f.set(f["use"].field("cost"), cost)
    f.set(f["use"].field("stack"), u32(0))
    f.set(f["use"].field("mem"), peak)
    f.ret(result)


def _sat(f, name, a, b, over):
    out = tmp(f, counter)
    f.call(name, [a, b, inout(over)], dest=out)
    return out


def _certificate(L: Layout) -> None:
    """The closed form of BOUNDS.md section 9, and its checker.

    No region prices: the visited set admits every instruction at most once
    per list build whatever the pattern's structure, so the whole call is a
    handful of counts read straight off the program. The builder computes the
    form and the checker recomputes it and asks for domination, which is the
    relationship section 9 sanctions — for this configuration the rule is the
    formula, so restating it twice would only be writing the formula twice.
    """
    f = L.func(
        "pike_price",
        params=[("re", L.Re), ("cert", L.Cert, "inout")],
        ret=boolean,
    )
    re = f["re"]
    code = re.field("code")
    over = f.let("over", boolean, boolean(False))

    big = tmp(f, counter, code.len().cast(counter))
    slots = tmp(f, counter, (re.field("ncap") + u32(1)).cast(counter) * counter(2))
    block = tmp(f, counter, slots * counter(spec.REG_SIZE))
    words = tmp(f, counter, (code.len().shr(3) + u32(1)).cast(counter))
    saves = tmp(f, counter, counter(0))
    pc = tmp(f, u32, u32(0))
    with f.while_(pc < code.len(), down(code.len(), pc)):
        with f.if_(code.at(pc).field("op") == L.Op.OpSave):
            f.set(saves, saves + counter(1))
        f.set(pc, pc + u32(1))

    def cap(entries):
        """The section 5 growth schedule's final capacity for that many
        entries: nothing for none, else four plus twice the count."""
        held = tmp(f, counter, counter(0))
        with f.if_(entries > counter(0)):
            doubled = _sat(f, "sat_mul", entries, counter(spec.GROW_FACTOR), over)
            f.set(held, _sat(f, "sat_add", doubled, counter(spec.GROW_MIN), over))
        return held

    # The reservation R: two thread lists, the closure stack, refcounts and
    # the free list, and the pool, each at its section 9 entry bound times
    # its entry size.
    lists = _sat(f, "sat_mul", cap(big), counter(2 * spec.TH_SIZE), over)
    closure = _sat(
        f,
        "sat_mul",
        cap(_sat(f, "sat_mul", big, counter(2), over)),
        counter(spec.TH_SIZE),
        over,
    )
    blocks = tmp(
        f,
        counter,
        _sat(
            f,
            "sat_add",
            _sat(f, "sat_mul", big, counter(4), over),
            counter(2),
            over,
        ),
    )
    tables = _sat(f, "sat_mul", cap(blocks), counter(2 * spec.REG_SIZE), over)
    pool = _sat(
        f,
        "sat_mul",
        cap(_sat(f, "sat_mul", blocks, slots, over)),
        counter(spec.REG_SIZE),
        over,
    )
    reserved = tmp(f, counter, lists)
    for extra in (closure, tables, pool):
        f.set(reserved, _sat(f, "sat_add", reserved, extra, over))

    setup = _sat(f, "sat_add", block, words, over)
    # One position: the closure's marks and the steps, at most one each per
    # instruction; a copy-on-write per Save plus the accept's own; the seed's
    # block fill; and the visited set cleared.
    position = _sat(f, "sat_mul", big, counter(2), over)
    writes = _sat(
        f,
        "sat_mul",
        _sat(f, "sat_add", saves, counter(2), over),
        block,
        over,
    )
    f.set(position, _sat(f, "sat_add", position, writes, over))
    f.set(position, _sat(f, "sat_add", position, words, over))

    steady = _sat(f, "sat_add", setup, block, over)
    growth = _sat(f, "sat_mul", reserved, counter(3), over)
    steady = _sat(f, "sat_add", steady, growth, over)
    held = _sat(f, "sat_mul", reserved, counter(2), over)
    resident = _sat(f, "sat_add", setup, held, over)

    with f.if_(over):
        f.ret(boolean(False))
    cert = f["cert"]
    f.set(cert.field("config"), L.Cfg.CfgPike)
    f.set(cert.field("complexity"), L.Cc.CcLinear)
    f.set(cert.field("cost"), poly(L, c0=steady, c1=position))
    f.set(cert.field("stack"), zero(L))
    f.set(cert.field("mem"), const(L, resident))
    empty = f.let("empty", L.Prices)
    f.freeze(cert.field("prices"), empty)
    f.ret(boolean(True))

    f = L.func(
        "pike_check",
        params=[("re", L.Re), ("cert", L.Cert)],
        ret=L.Cr,
    )
    cert = f["cert"]
    fits = tmp(f, boolean, boolean(False))
    f.call("pike_ok", [f["re"]], dest=fits)
    with f.if_(lnot(fits)):
        f.ret(L.Cr.CrIneligible)
    with f.if_(cert.field("config") != L.Cfg.CfgPike):
        f.ret(L.Cr.CrConfig)
    with f.if_(cert.field("prices").len() != u32(0)):
        f.ret(L.Cr.CrPrices)
    # Linearity is the shape of the rule here, so the claim has to say it and
    # the bound has to have it; a complexity naming no variant is the same
    # made-up-ordinal refusal as everywhere else.
    known = tmp(f, boolean, boolean(False))
    with f.switch(cert.field("complexity")) as arm:
        with arm.case("CcLinear"):
            f.set(known, boolean(True))
        with arm.case("CcNotProvenLinear"):
            f.ret(L.Cr.CrNotLinear)
    with f.if_(lnot(known)):
        f.ret(L.Cr.CrShape)
    with f.if_(lnot(linear(cert.field("cost")))):
        f.ret(L.Cr.CrNotLinear)
    needed = f.let("needed", L.Cert)
    priced = tmp(f, boolean, boolean(False))
    f.call("pike_price", [f["re"], inout(needed)], dest=priced)
    with f.if_(lnot(priced)):
        f.ret(L.Cr.CrOverflow)
    holds = tmp(f, boolean, boolean(False))
    # The same discipline as the backtracking total check: cost and memory
    # may overestimate, the stack must equal the requirement — which here is
    # exactly zero, since no backtrack stack exists on this path, so a
    # certificate claiming entries the matcher can never push is refused
    # under the same name section 5's rule uses.
    for claim, rule, refusal in (
        ("cost", "poly_ge", L.Cr.CrTotalCost),
        ("stack", "poly_eq", L.Cr.CrTotalStack),
        ("mem", "poly_ge", L.Cr.CrTotalMem),
    ):
        f.call(rule, [cert.field(claim), needed.field(claim)], dest=holds)
        with f.if_(lnot(holds)):
            f.ret(refusal)
    f.ret(L.Cr.CrOk)
