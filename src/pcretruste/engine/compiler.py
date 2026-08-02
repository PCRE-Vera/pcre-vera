"""The bytecode compiler, written in TIR.

The AST is walked with an explicit job stack rather than by recursion, which TIR
does not have: a job carries the node it is on and how far through it the walk
has got, so a construct that has to emit something after its children — a
group's closing Save, an alternation's jump patches — simply gets revisited.

Counted repetitions compile to a counter register and the four Rep opcodes
rather than to unrolled copies. That is the backtracking VM's form; the Pike VM
of M5 wants the unrolled one, and DESIGN.md section 4.3 keeps them apart on
purpose, because keying a visited set by pc is only sound without counters.
"""

from __future__ import annotations

from ..dsl import boolean, counter, inout, land, u8, u32
from . import spec
from .layout import Layout
from .parser import down, tmp

# How many times the walk may revisit a job before we call it a bug of ours
# rather than a pattern's fault. Every node is entered once and revisited once
# per child, so twice the arena is already generous.
WALK_FUEL = 8 * spec.MAX_NODES


def build(L: Layout) -> None:
    _emit(L)
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

    f = L.func("push_job", params=[("w", L.Work, "inout"), ("node", u32)])
    w = f["w"]
    with f.if_(w.field("jobs").len() >= u32(spec.MAX_JOBS)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()
    f.push(
        w.field("jobs"),
        L.Job.of(node=f["node"], phase=u32(0), cur=u32(0), mark=u32(0), base=u32(0)),
    )

    f = L.func("push_patch", params=[("w", L.Work, "inout"), ("pc", u32)])
    w = f["w"]
    with f.if_(w.field("patches").len() >= u32(spec.MAX_PATCHES)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()
    f.push(w.field("patches"), f["pc"])

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


def _walk(L: Layout) -> None:
    f = L.func(
        "generate", params=[("w", L.Work, "inout"), ("endanchored", boolean)]
    )
    w = f["w"]
    root = tmp(f, u32, w.field("root"))
    f.call("push_job", [inout(w), root])
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
                    f.call("push_job", [inout(w), child])

            with arm.case("NdGroup"):
                with f.if_(job.field("phase") == u32(0)):
                    with f.if_(nd.field("val") != u32(0)):
                        slot = tmp(f, u32, nd.field("val") * u32(2))
                        f.call("emit", [inout(w), L.Op.OpSave, slot, u32(0)], dest=pc)
                    f.set(w.field("jobs").at(top).field("phase"), u32(1))
                    body = tmp(f, u32, nd.field("first"))
                    with f.if_(body != u32(0)):
                        f.call("push_job", [inout(w), body])
                with f.else_():
                    with f.if_(nd.field("val") != u32(0)):
                        slot = tmp(f, u32, nd.field("val") * u32(2) + u32(1))
                        f.call("emit", [inout(w), L.Op.OpSave, slot, u32(0)], dest=pc)
                    f.pop(w.field("jobs"), done)

            with arm.case("NdAlt"):
                f.call("walk_alt", [inout(w), top, job, nd])

            with arm.case("NdRepeat"):
                f.call("walk_repeat", [inout(w), top, job, nd])

    with f.if_(w.field("err") != u32(0)):
        f.ret()
    with f.if_(fuel == counter(0)):
        f.set(w.field("err"), u32(spec.E_INTERNAL))
        f.ret()
    with f.if_(f["endanchored"]):
        f.call("emit", [inout(w), L.Op.OpEod, u32(0), u32(0)], dest=pc)
    f.call("emit", [inout(w), L.Op.OpAccept, u32(0), u32(0)], dest=pc)
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
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(3)):
        f.pop(w.field("jobs"), done)
        f.ret()

    branch = tmp(f, u32, f["nd"].field("first"))
    with f.if_(job.field("phase") == u32(0)):
        f.set(w.field("jobs").at(top).field("base"), w.field("patches").len())
    with f.else_():
        # The branch just compiled jumps to the end; the split that guarded it
        # now knows where the next one starts.
        f.call("emit", [inout(w), L.Op.OpJump, u32(0), u32(0)], dest=pc)
        f.call("push_patch", [inout(w), pc])
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("code").at(job.field("mark")).field("alt"), w.field("code").len())
        f.set(branch, w.field("nodes").at(job.field("cur")).field("nxt"))

    with f.if_(w.field("nodes").at(branch).field("nxt") == u32(0)):
        f.set(w.field("jobs").at(top).field("phase"), u32(2))
        with f.if_(job.field("phase") == u32(0)):
            f.set(w.field("jobs").at(top).field("phase"), u32(3))
    with f.else_():
        f.call("emit", [inout(w), L.Op.OpSplit, u32(0), u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("code").at(pc).field("arg"), pc + u32(1))
        f.set(w.field("jobs").at(top).field("mark"), pc)
        f.set(w.field("jobs").at(top).field("phase"), u32(1))
    f.set(w.field("jobs").at(top).field("cur"), branch)
    f.call("push_job", [inout(w), branch])


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
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(2)):
        r = tmp(f, u32, job.field("mark"))
        f.call("emit", [inout(w), L.Op.OpRepNext, r, u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("reps").at(r).field("after"), w.field("code").len())
        f.pop(w.field("jobs"), done)
        f.ret()

    with f.if_(job.field("phase") == u32(3)):
        f.pop(w.field("jobs"), done)
        f.ret()

    lo = tmp(f, u32, nd.field("val"))
    hi = tmp(f, u32, nd.field("aux"))
    body = tmp(f, u32, nd.field("first"))

    with f.if_(hi == u32(0)):
        f.pop(w.field("jobs"), done)
        f.ret()
    with f.if_(land(lo == u32(1), hi == u32(1))):
        f.set(w.field("jobs").at(top).field("phase"), u32(3))
        f.call("push_job", [inout(w), body])
        f.ret()
    with f.if_(land(lo == u32(0), hi == u32(1))):
        f.call("emit", [inout(w), L.Op.OpSplit, u32(0), u32(0)], dest=pc)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        f.set(w.field("jobs").at(top).field("mark"), pc)
        f.set(w.field("jobs").at(top).field("phase"), u32(1))
        f.call("push_job", [inout(w), body])
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
    f.call("push_job", [inout(w), body])


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
