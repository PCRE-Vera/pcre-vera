"""The backtracking matcher, written in TIR.

Depth-first exploration over an explicit stack of (pc, position, undo mark),
never host recursion, with every instruction visit charged against the caller's
cost limit, every push checked against the stack limit, and every array growth
charged against the memory limit before it happens. The worst case is therefore
a clean ResourceExceeded rather than an unbounded run (DESIGN.md section 4.3).

Captures and repetition counters live in one flat register file; a write to it
records an undo entry, which backtracking replays. Undo entries are recorded
only while there is something to backtrack to, which is what keeps the trail
from growing over a long run of a pattern that has no choice points at all.

The bounds these limits are compared against are the caller's, not yet the
analyzer's: computing them from the pattern is M5.
"""

from __future__ import annotations

from ..dsl import Expr, boolean, counter, inout, land, lnot, lor, u32, u8
from . import spec
from .layout import Layout
from .parser import down, tmp


def build(L: Layout) -> None:
    _conventions(L)
    _scratch(L)
    _match(L)


def _conventions(L: Layout) -> None:
    """Where a newline starts, where one ends, and what \\R eats.

    All three follow the pinned pcre2's own reading, which is why they are
    written as its three separate questions rather than as one predicate.
    """
    f = L.func(
        "newline_at",
        params=[("subj", L.frozen_bytes), ("pos", u32), ("nltype", u32)],
        ret=u32,
    )
    subj = f["subj"]
    pos = f["pos"]
    nltype = f["nltype"]
    n = tmp(f, u32, subj.len())
    with f.if_(pos >= n):
        f.ret(u32(0))
    c = tmp(f, u8, subj.at(pos))
    with f.if_(nltype == u32(spec.NL_LF)):
        with f.if_(c == u8(0x0A)):
            f.ret(u32(1))
        f.ret(u32(0))
    with f.if_(nltype == u32(spec.NL_CR)):
        with f.if_(c == u8(0x0D)):
            f.ret(u32(1))
        f.ret(u32(0))
    with f.if_(nltype == u32(spec.NL_CRLF)):
        with f.if_(
            land(c == u8(0x0D), land(pos + u32(1) < n, subj.at(pos + u32(1)) == u8(0x0A)))
        ):
            f.ret(u32(2))
        f.ret(u32(0))
    with f.if_(c == u8(0x0A)):
        f.ret(u32(1))
    with f.if_(c == u8(0x0D)):
        with f.if_(land(pos + u32(1) < n, subj.at(pos + u32(1)) == u8(0x0A))):
            f.ret(u32(2))
        f.ret(u32(1))
    with f.if_(nltype == u32(spec.NL_ANY)):
        with f.if_(lor(c == u8(0x0B), lor(c == u8(0x0C), c == u8(0x85)))):
            f.ret(u32(1))
    f.ret(u32(0))

    f = L.func(
        "newline_before",
        params=[("subj", L.frozen_bytes), ("pos", u32), ("nltype", u32)],
        ret=u32,
    )
    subj = f["subj"]
    pos = f["pos"]
    nltype = f["nltype"]
    with f.if_(pos == u32(0)):
        f.ret(u32(0))
    with f.if_(nltype == u32(spec.NL_LF)):
        with f.if_(subj.at(pos - u32(1)) == u8(0x0A)):
            f.ret(u32(1))
        f.ret(u32(0))
    with f.if_(nltype == u32(spec.NL_CR)):
        with f.if_(subj.at(pos - u32(1)) == u8(0x0D)):
            f.ret(u32(1))
        f.ret(u32(0))
    with f.if_(nltype == u32(spec.NL_CRLF)):
        with f.if_(
            land(
                pos >= u32(2),
                land(subj.at(pos - u32(2)) == u8(0x0D), subj.at(pos - u32(1)) == u8(0x0A)),
            )
        ):
            f.ret(u32(2))
        f.ret(u32(0))
    c = tmp(f, u8, subj.at(pos - u32(1)))
    with f.if_(c == u8(0x0A)):
        with f.if_(land(pos >= u32(2), subj.at(pos - u32(2)) == u8(0x0D))):
            f.ret(u32(2))
        f.ret(u32(1))
    with f.if_(c == u8(0x0D)):
        f.ret(u32(1))
    with f.if_(nltype == u32(spec.NL_ANY)):
        with f.if_(lor(c == u8(0x0B), lor(c == u8(0x0C), c == u8(0x85)))):
            f.ret(u32(1))
    f.ret(u32(0))

    f = L.func(
        "bsr_at",
        params=[("subj", L.frozen_bytes), ("pos", u32), ("bsr", u32)],
        ret=u32,
    )
    subj = f["subj"]
    pos = f["pos"]
    n = tmp(f, u32, subj.len())
    with f.if_(pos >= n):
        f.ret(u32(0))
    c = tmp(f, u8, subj.at(pos))
    with f.if_(c == u8(0x0D)):
        with f.if_(land(pos + u32(1) < n, subj.at(pos + u32(1)) == u8(0x0A))):
            f.ret(u32(2))
        f.ret(u32(1))
    with f.if_(c == u8(0x0A)):
        f.ret(u32(1))
    with f.if_(f["bsr"] == u32(spec.BSR_ANYCRLF)):
        f.ret(u32(0))
    with f.if_(lor(c == u8(0x0B), lor(c == u8(0x0C), c == u8(0x85)))):
        f.ret(u32(1))
    f.ret(u32(0))

    f = L.func(
        "class_has",
        params=[("classes", L.frozen_bytes), ("idx", u32), ("c", u8)],
        ret=boolean,
    )
    at = tmp(f, u32, f["idx"] * u32(32) + f["c"].shr(3).cast(u32))
    bit = tmp(f, u8, L.BITS.at(f["c"].cast(u32) & u32(7)))
    f.ret((f["classes"].at(at) & bit) != u8(0))

    f = L.func(
        "at_line_end",
        params=[("subj", L.frozen_bytes), ("pos", u32), ("nltype", u32)],
        ret=boolean,
    )
    n = tmp(f, u32, f["subj"].len())
    with f.if_(f["pos"] >= n):
        f.ret(boolean(True))
    step = tmp(f, u32, u32(0))
    f.call("newline_at", [f["subj"], f["pos"], f["nltype"]], dest=step)
    f.ret(land(step != u32(0), f["pos"] + step == n))


def _scratch(L: Layout) -> None:
    """Growth, charged before it happens.

    TIR-SPEC.md section 11.3 counts both buffers while the elements are copied,
    so that is what goes against the memory limit. The work is cost, at one
    unit per IR byte zeroed or copied, which is how DESIGN.md section 5 defines
    scratch management.
    """
    f = L.func(
        "charge_grow",
        params=[
            ("oldcap", u32),
            ("lenv", u32),
            ("esize", u32),
            ("maxv", u32),
            ("mem", counter, "inout"),
            ("peak", counter, "inout"),
            ("cost", counter, "inout"),
            ("memlimit", counter),
            ("costlimit", counter),
        ],
        ret=boolean,
    )
    with f.if_(f["lenv"] < f["oldcap"]):
        f.ret(boolean(True))
    with f.if_(f["lenv"] >= f["maxv"]):
        f.ret(boolean(False))
    newcap = tmp(f, u32, u32(4))
    with f.if_(f["oldcap"] * u32(2) > u32(4)):
        f.set(newcap, f["oldcap"] * u32(2))
    with f.if_(newcap > f["maxv"]):
        f.set(newcap, f["maxv"])
    grown = tmp(f, counter, newcap.cast(counter) * f["esize"].cast(counter))
    held = tmp(f, counter, f["oldcap"].cast(counter) * f["esize"].cast(counter))
    with f.if_(grown > f["memlimit"] - f["mem"]):
        f.ret(boolean(False))
    # Every byte of the new buffer is zeroed and every byte of the old one is
    # copied over it, and both are work: a growth that charged only the copy
    # would let a run allocate its first block for nothing.
    work = tmp(f, counter, grown + held)
    with f.if_(work > f["costlimit"] - f["cost"]):
        f.ret(boolean(False))
    f.set(f["cost"], f["cost"] + work)
    total = tmp(f, counter, f["mem"] + grown)
    with f.if_(total > f["peak"]):
        f.set(f["peak"], total)
    f.set(f["mem"], total - held)
    f.ret(boolean(True))

    f = L.func(
        "write_reg",
        params=[
            ("regs", L.Regs, "inout"),
            ("trail", L.Trail, "inout"),
            ("mem", counter, "inout"),
            ("peak", counter, "inout"),
            ("cost", counter, "inout"),
            ("memlimit", counter),
            ("costlimit", counter),
            ("btlen", u32),
            ("slot", u32),
            ("value", u32),
        ],
        ret=boolean,
    )
    # With nothing on the backtrack stack, no undo entry can ever be replayed,
    # so recording one would only make the trail grow for the length of the run.
    with f.if_(f["btlen"] > u32(0)):
        room = tmp(f, boolean, boolean(False))
        f.call(
            "charge_grow",
            [
                f["trail"].cap(),
                f["trail"].len(),
                u32(spec.UNDO_SIZE),
                u32(spec.MAX_TRAIL),
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
        f.push(
            f["trail"],
            L.Undo.of(slot=f["slot"], old=f["regs"].at(f["slot"])),
        )
    f.set(f["regs"].at(f["slot"]), f["value"])
    f.ret(boolean(True))

    f = L.func(
        "push_bt",
        params=[
            ("bt", L.Stack, "inout"),
            ("mem", counter, "inout"),
            ("peak", counter, "inout"),
            ("cost", counter, "inout"),
            ("memlimit", counter),
            ("costlimit", counter),
            ("stacklimit", u32),
            ("pcv", u32),
            ("posv", u32),
            ("mark", u32),
        ],
        ret=boolean,
    )
    with f.if_(f["bt"].len() >= f["stacklimit"]):
        f.ret(boolean(False))
    room = tmp(f, boolean, boolean(False))
    f.call(
        "charge_grow",
        [
            f["bt"].cap(),
            f["bt"].len(),
            u32(spec.BT_SIZE),
            u32(spec.MAX_STACK),
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
    f.push(f["bt"], L.Bt.of(pc=f["pcv"], pos=f["posv"], mark=f["mark"]))
    f.ret(boolean(True))


def _match(L: Layout) -> None:
    f = L.func(
        "match",
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
    stackpeak = tmp(f, u32, u32(0))
    f.set(f["use"].field("cost"), cost)
    f.set(f["use"].field("stack"), stackpeak)
    f.set(f["use"].field("mem"), peak)
    with f.if_(f["start"] > n):
        f.ret(u32(spec.BAD_INPUT))

    code = f.let("code", L.FrozenCode, re.field("code"))
    classes = f.let("classes", L.frozen_bytes, re.field("classes"))
    reps = f.let("reps", L.FrozenReps, re.field("reps"))
    nltype = tmp(f, u32, re.field("nltype"))
    bsr = tmp(f, u32, re.field("bsr"))
    ncap = tmp(f, u32, re.field("ncap"))
    nreg = tmp(f, u32, re.field("nregs"))
    novec = tmp(f, u32, (ncap + u32(1)) * u32(2))
    regbase = tmp(f, u32, novec)
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

    regs = f.let("regs", L.Regs)
    bt = f.let("bt", L.Stack)
    trail = f.let("trail", L.Trail)

    # The register file and the ovector are sized once, and their zeroing is
    # charged, because setup work is work (DESIGN.md section 5).
    setup = tmp(f, counter, (nreg + novec).cast(counter) * counter(4))
    with f.if_(lor(setup > memlimit, setup > costlimit)):
        f.ret(u32(spec.RESOURCE_EXCEEDED))
    f.set(mem, setup)
    f.set(peak, setup)
    f.set(cost, setup)
    f.reserve(regs, nreg)
    f.reserve(ov, novec)
    k = tmp(f, u32, u32(0))
    with f.while_(k < nreg, down(nreg, k)):
        f.push(regs, u32(spec.UNSET))
        f.set(k, k + u32(1))
    f.truncate(ov, u32(0))
    f.set(k, u32(0))
    with f.while_(k < novec, down(novec, k)):
        f.push(ov, u32(spec.UNSET))
        f.set(k, k + u32(1))

    attempt = tmp(f, u32, f["start"])
    result = tmp(f, u32, u32(spec.NO_MATCH))
    searching = tmp(f, boolean, boolean(True))
    okv = tmp(f, boolean, boolean(False))

    with f.while_(searching, down(n + u32(1), attempt)):
        reset = tmp(f, counter, nreg.cast(counter) * counter(4))
        with f.if_(reset > costlimit - cost):
            f.set(result, u32(spec.RESOURCE_EXCEEDED))
            f.set(searching, boolean(False))
            f.cont()
        f.set(cost, cost + reset)
        j = tmp(f, u32, u32(0))
        with f.while_(j < nreg, down(nreg, j)):
            f.set(regs.at(j), u32(spec.UNSET))
            f.set(j, j + u32(1))
        f.truncate(bt, u32(0))
        f.truncate(trail, u32(0))

        pc = tmp(f, u32, u32(0))
        pos = tmp(f, u32, attempt)
        running = tmp(f, boolean, boolean(True))
        fail = tmp(f, boolean, boolean(False))
        found = tmp(f, boolean, boolean(False))

        with f.while_(running, costlimit - cost):
            with f.if_(cost >= costlimit):
                f.set(result, u32(spec.RESOURCE_EXCEEDED))
                f.set(searching, boolean(False))
                f.set(running, boolean(False))
                f.cont()
            f.set(cost, cost + counter(1))
            inst = tmp(f, L.Inst, code.at(pc))

            def step(test: Expr, length: Expr) -> None:
                with f.if_(land(pos < n, test)):
                    f.set(pos, pos + length)
                    f.set(pc, pc + u32(1))
                with f.else_():
                    f.set(fail, boolean(True))

            def holds(test: Expr) -> None:
                with f.if_(test):
                    f.set(pc, pc + u32(1))
                with f.else_():
                    f.set(fail, boolean(True))

            def save(slot: Expr, value: Expr) -> None:
                f.call(
                    "write_reg",
                    [
                        inout(regs),
                        inout(trail),
                        inout(mem),
                        inout(peak),
                        inout(cost),
                        memlimit,
                        costlimit,
                        bt.len(),
                        slot,
                        value,
                    ],
                    dest=okv,
                )
                with f.if_(lnot(okv)):
                    f.set(result, u32(spec.RESOURCE_EXCEEDED))
                    f.set(searching, boolean(False))
                    f.set(running, boolean(False))

            def fork(target: Expr) -> None:
                mark = tmp(f, u32, trail.len())
                f.call(
                    "push_bt",
                    [
                        inout(bt),
                        inout(mem),
                        inout(peak),
                        inout(cost),
                        memlimit,
                        costlimit,
                        f["stacklimit"],
                        target,
                        pos,
                        mark,
                    ],
                    dest=okv,
                )
                with f.if_(lnot(okv)):
                    f.set(result, u32(spec.RESOURCE_EXCEEDED))
                    f.set(searching, boolean(False))
                    f.set(running, boolean(False))
                with f.else_():
                    with f.if_(bt.len() > stackpeak):
                        f.set(stackpeak, bt.len())

            with f.switch(inst.field("op")) as arm:
                with arm.case("OpChar"):
                    step(subj.at(pos) == inst.field("arg").cast(u8), u32(1))
                with arm.case("OpCharCI"):
                    step(
                        L.LOWER.at(subj.at(pos).cast(u32)) == inst.field("arg").cast(u8),
                        u32(1),
                    )
                with arm.case("OpClass"):
                    hit = tmp(f, boolean, boolean(False))
                    with f.if_(pos < n):
                        f.call(
                            "class_has",
                            [classes, inst.field("arg"), subj.at(pos)],
                            dest=hit,
                        )
                    step(hit, u32(1))
                with arm.case("OpAny"):
                    step(boolean(True), u32(1))
                with arm.case("OpAnyNoNL"):
                    nl = tmp(f, u32, u32(0))
                    with f.if_(pos < n):
                        f.call("newline_at", [subj, pos, nltype], dest=nl)
                    step(nl == u32(0), u32(1))
                with arm.case("OpBsr"):
                    eaten = tmp(f, u32, u32(0))
                    f.call("bsr_at", [subj, pos, bsr], dest=eaten)
                    with f.if_(eaten != u32(0)):
                        f.set(pos, pos + eaten)
                        f.set(pc, pc + u32(1))
                    with f.else_():
                        f.set(fail, boolean(True))
                with arm.case("OpSplit"):
                    fork(inst.field("alt"))
                    f.set(pc, inst.field("arg"))
                with arm.case("OpJump"):
                    f.set(pc, inst.field("arg"))
                with arm.case("OpSave"):
                    save(inst.field("arg"), pos)
                    f.set(pc, pc + u32(1))

                with arm.case("OpCirc"):
                    holds(land(pos == u32(0), lnot(notbol)))
                with arm.case("OpCircM"):
                    ok = tmp(f, boolean, lnot(notbol))
                    with f.if_(pos != u32(0)):
                        back = tmp(f, u32, u32(0))
                        f.call("newline_before", [subj, pos, nltype], dest=back)
                        f.set(ok, land(pos != n, back != u32(0)))
                    holds(ok)
                with arm.case("OpDoll"):
                    ends = tmp(f, boolean, boolean(False))
                    f.call("at_line_end", [subj, pos, nltype], dest=ends)
                    holds(land(lnot(noteol), ends))
                with arm.case("OpDollE"):
                    holds(land(lnot(noteol), pos == n))
                with arm.case("OpDollM"):
                    ok = tmp(f, boolean, lnot(noteol))
                    with f.if_(pos < n):
                        here = tmp(f, u32, u32(0))
                        f.call("newline_at", [subj, pos, nltype], dest=here)
                        f.set(ok, here != u32(0))
                    holds(ok)
                with arm.case("OpSod"):
                    holds(pos == u32(0))
                with arm.case("OpEod"):
                    holds(pos == n)
                with arm.case("OpEodn"):
                    ends = tmp(f, boolean, boolean(False))
                    f.call("at_line_end", [subj, pos, nltype], dest=ends)
                    holds(ends)
                with arm.case("OpWordB"):
                    f.call("word_edge", [subj, pos], dest=okv)
                    holds(okv)
                with arm.case("OpNotWordB"):
                    f.call("word_edge", [subj, pos], dest=okv)
                    holds(lnot(okv))

                with arm.case("OpRepZero"):
                    save(regbase + inst.field("arg") * u32(2), u32(0))
                    f.set(pc, pc + u32(1))
                with arm.case("OpRepEnter"):
                    save(regbase + inst.field("arg") * u32(2) + u32(1), pos)
                    f.set(pc, pc + u32(1))
                with arm.case("OpRepLoop"):
                    rep = tmp(f, L.Rep, reps.at(inst.field("arg")))
                    cnt = tmp(f, u32, regs.at(regbase + inst.field("arg") * u32(2)))
                    with f.if_(cnt < rep.field("lo")):
                        f.set(pc, rep.field("body"))
                    with f.else_():
                        with f.if_(cnt >= rep.field("hi")):
                            f.set(pc, rep.field("after"))
                        with f.else_():
                            with f.if_(rep.field("greedy")):
                                fork(rep.field("after"))
                                f.set(pc, rep.field("body"))
                            with f.else_():
                                fork(rep.field("body"))
                                f.set(pc, rep.field("after"))
                with arm.case("OpRepNext"):
                    rep = tmp(f, L.Rep, reps.at(inst.field("arg")))
                    slot = tmp(f, u32, regbase + inst.field("arg") * u32(2))
                    cnt = tmp(f, u32, regs.at(slot) + u32(1))
                    entered = tmp(f, u32, regs.at(slot + u32(1)))
                    save(slot, cnt)
                    # An iteration that consumed nothing does not go round
                    # again, once the minimum count is behind us: the rule
                    # pcre2 applies at a repeating ket. A bounded repetition
                    # has no repeating ket — pcre2 replicates it — so the rule
                    # does not apply there, and `(|a){1,3}` really can reach
                    # its third copy after two empty ones.
                    with f.if_(
                        land(
                            rep.field("hi") == u32(spec.NONE),
                            land(pos == entered, cnt >= rep.field("lo")),
                        )
                    ):
                        f.set(pc, rep.field("after"))
                    with f.else_():
                        f.set(pc, rep.field("head"))

                with arm.case("OpAccept"):
                    empty = tmp(f, boolean, pos == attempt)
                    refuse = tmp(
                        f,
                        boolean,
                        land(
                            empty,
                            lor(notempty, land(notempty_at, attempt == f["start"])),
                        ),
                    )
                    with f.if_(refuse):
                        f.set(fail, boolean(True))
                    with f.else_():
                        f.set(regs.at(u32(0)), attempt)
                        f.set(regs.at(u32(1)), pos)
                        f.set(found, boolean(True))
                        f.set(running, boolean(False))

            with f.if_(fail):
                with f.if_(bt.len() == u32(0)):
                    f.set(running, boolean(False))
                    f.truncate(trail, u32(0))
                with f.else_():
                    entry = tmp(f, L.Bt)
                    f.pop(bt, entry)
                    f.set(pc, entry.field("pc"))
                    f.set(pos, entry.field("pos"))
                    with f.while_(
                        trail.len() > entry.field("mark"), trail.len().cast(counter)
                    ):
                        undo = tmp(f, L.Undo)
                        f.pop(trail, undo)
                        f.set(regs.at(undo.field("slot")), undo.field("old"))
                    with f.if_(bt.len() == u32(0)):
                        f.truncate(trail, u32(0))
                    f.set(fail, boolean(False))

        with f.if_(found):
            f.set(result, u32(spec.MATCHED))
            f.set(searching, boolean(False))
            f.cont()
        with f.if_(lnot(searching)):
            f.cont()
        with f.if_(lor(anchored, attempt >= n)):
            f.set(searching, boolean(False))
            f.cont()
        f.set(attempt, attempt + u32(1))
        # Having just walked past a CR onto a LF, do not start a match between
        # the two when the convention makes them one newline and the pattern
        # never spells either out. This is pcre2's bumpalong rule, and it is
        # observable: it declines a position where a match could have started.
        with f.if_(
            land(
                land(crlfish, land(nocrlf, re.field("crfirst") != u32(0))),
                land(
                    subj.at(attempt - u32(1)) == u8(0x0D),
                    land(attempt < n, subj.at(attempt) == u8(0x0A)),
                ),
            )
        ):
            f.set(attempt, attempt + u32(1))

    f.set(f["use"].field("cost"), cost)
    f.set(f["use"].field("stack"), stackpeak)
    f.set(f["use"].field("mem"), peak)
    with f.if_(result == u32(spec.MATCHED)):
        k = tmp(f, u32, u32(0))
        with f.while_(k < novec, down(novec, k)):
            f.set(ov.at(k), regs.at(k))
            f.set(k, k + u32(1))
    f.ret(result)

    f = L.func(
        "word_edge", params=[("subj", L.frozen_bytes), ("pos", u32)], ret=boolean
    )
    n = tmp(f, u32, f["subj"].len())
    before = tmp(f, boolean, boolean(False))
    after = tmp(f, boolean, boolean(False))
    with f.if_(f["pos"] > u32(0)):
        f.call("ct", [f["subj"].at(f["pos"] - u32(1)), u8(spec.CT_WORD)], dest=before)
    with f.if_(f["pos"] < n):
        f.call("ct", [f["subj"].at(f["pos"]), u8(spec.CT_WORD)], dest=after)
    f.ret(before != after)
