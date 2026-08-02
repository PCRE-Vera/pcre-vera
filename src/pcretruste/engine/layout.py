"""The declarations every part of the engine shares.

One object holds the module under construction plus every type and constant the
parser, the code generator and the matcher refer to, so those three modules read
as ordinary code against a vocabulary rather than as string lookups.

Nothing here is trusted. It builds IR; the validator decides whether the IR
means anything.
"""

from __future__ import annotations

from ..dsl import Module, boolean, bytes_, counter, frozen, u8, u32, vec
from . import spec


class Layout:
    def __init__(self) -> None:
        m = Module()
        self.m = m

        # --- enums ---

        self.Nd = m.enum(
            "Nd",
            [
                "NdNil",
                "NdChar",
                "NdCharCI",
                "NdClass",
                "NdAny",
                "NdAnyNoNL",
                "NdBsr",
                "NdConcat",
                "NdAlt",
                "NdGroup",
                "NdRepeat",
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
            ],
        )

        self.Op = m.enum(
            "Op",
            [
                "OpChar",
                "OpCharCI",
                "OpClass",
                "OpAny",
                "OpAnyNoNL",
                "OpBsr",
                "OpSplit",
                "OpJump",
                "OpSave",
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
                "OpRepZero",
                "OpRepLoop",
                "OpRepEnter",
                "OpRepNext",
                "OpAccept",
            ],
        )

        self.Ek = m.enum(
            "Ek",
            [
                "EkErr",
                "EkChar",
                "EkSet",
                "EkNegSet",
                "EkSod",
                "EkEod",
                "EkEodn",
                "EkWordB",
                "EkNotWordB",
                "EkBsr",
                "EkNop",
            ],
        )

        # --- structs ---
        #
        # An AST node keeps its children in a sibling list so that the arena
        # stays a flat array of copyable records: `first` and `last` bound the
        # list, `nxt` walks it. Index 0 is the nil node, never a real child.

        self.Node = m.struct(
            "Node",
            [
                ("kind", self.Nd),
                ("val", u32),
                ("aux", u32),
                ("opts", u32),
                ("first", u32),
                ("last", u32),
                ("nxt", u32),
            ],
        )

        self.Inst = m.struct("Inst", [("op", self.Op), ("arg", u32), ("alt", u32)])

        self.Rep = m.struct(
            "Rep",
            [
                ("lo", u32),
                ("hi", u32),
                ("greedy", boolean),
                ("head", u32),
                ("body", u32),
                ("after", u32),
            ],
        )

        # `qual` is the node a quantifier would apply to, which is not simply
        # the last child of `cat`: an inline option group clears it, so `a(?i)*`
        # is the "nothing to repeat" error pcre2 reports rather than a repeat
        # of the `a`.
        self.Frame = m.struct(
            "Frame",
            [
                ("grp", u32),
                ("alt", u32),
                ("cat", u32),
                ("qual", u32),
                ("opts", u32),
                ("at", u32),
                ("unsup", u32),
            ],
        )

        self.Quant = m.struct(
            "Quant",
            [("ok", boolean), ("lo", u32), ("hi", u32), ("end", u32)],
        )

        self.Job = m.struct(
            "Job",
            [
                ("node", u32),
                ("phase", u32),
                ("cur", u32),
                ("mark", u32),
                ("base", u32),
            ],
        )

        self.NameEnt = m.struct("NameEnt", [("off", u32), ("nlen", u32), ("grp", u32)])

        # A group reference met during the parse, held until the end of the
        # pass because forward references are legal. `num` is the absolute
        # group number, or NONE for a reference by name, in which case `off`
        # and `nlen` locate the name in the pattern. `off` doubles as the byte
        # offset any error about this reference is reported at.
        self.Ref = m.struct("Ref", [("num", u32), ("off", u32), ("nlen", u32)])

        self.Bt = m.struct("Bt", [("pc", u32), ("pos", u32), ("mark", u32)])

        self.Undo = m.struct("Undo", [("slot", u32), ("old", u32)])

        self.Esc = m.struct("Esc", [("kind", self.Ek), ("val", u32)])

        # --- sequence types ---

        self.frozen_bytes = frozen(bytes_)

        self.Nodes = vec(self.Node, spec.MAX_NODES)
        self.Frames = vec(self.Frame, spec.MAX_DEPTH + 1)
        self.Code = vec(self.Inst, spec.MAX_CODE)
        self.Reps = vec(self.Rep, spec.MAX_REPS)
        self.Jobs = vec(self.Job, spec.MAX_JOBS)
        self.Patches = vec(u32, spec.MAX_PATCHES)
        self.Pending = vec(u32, spec.MAX_CODE)
        self.NameEnts = vec(self.NameEnt, spec.MAX_NAMES)
        self.Refs = vec(self.Ref, spec.MAX_REFS)
        self.Ovec = vec(u32, spec.MAX_OVEC)
        self.Regs = vec(u32, spec.MAX_REGS)
        self.Stack = vec(self.Bt, spec.MAX_STACK)
        self.Trail = vec(self.Undo, spec.MAX_TRAIL)

        self.FrozenCode = frozen(self.Code)
        self.FrozenReps = frozen(self.Reps)

        # --- the compiled pattern ---
        #
        # Every field is frozen or scalar, so `Re` is copyable and travels as an
        # ordinary `in` parameter. That is what lets one compiled pattern serve
        # any number of match calls without a linear value ever being shared.

        self.Re = m.struct(
            "Re",
            [
                ("code", frozen(self.Code)),
                ("classes", frozen(bytes_)),
                ("reps", frozen(self.Reps)),
                ("names", frozen(bytes_)),
                ("nameents", frozen(self.NameEnts)),
                ("ncap", u32),
                ("nname", u32),
                ("nregs", u32),
                ("opts", u32),
                ("nltype", u32),
                ("bsr", u32),
                ("hascrlf", u32),
                ("crfirst", u32),
            ],
        )

        self.Work = m.struct(
            "Work",
            [
                ("nodes", self.Nodes),
                ("frames", self.Frames),
                ("classes", bytes_),
                ("names", bytes_),
                ("nameents", self.NameEnts),
                ("code", self.Code),
                ("reps", self.Reps),
                ("jobs", self.Jobs),
                ("patches", self.Patches),
                ("ncap", u32),
                ("nname", u32),
                ("nclass", u32),
                ("nrep", u32),
                ("opts", u32),
                ("err", u32),
                ("erroff", u32),
                ("root", u32),
                ("refs", self.Refs),
                ("hascrlf", u32),
                ("crfirst", u32),
                ("nltype", u32),
                ("clselems", u32),
                ("clsrange", u32),
                ("clscrlf", u32),
                ("pending", self.Pending),
                ("seen", bytes_),
            ],
        )

        self.Out = m.struct(
            "Out",
            [("err", u32), ("erroff", u32), ("re", self.Re)],
        )

        self.Usage = m.struct(
            "Usage",
            [("cost", counter), ("stack", u32), ("mem", counter)],
        )

        # --- constants ---

        self.SETS = m.const("SETS", frozen(bytes_), spec.set_table())
        self.POSIX = m.const("POSIX", frozen(bytes_), spec.posix_table())
        self.BITS = m.const("BITS", frozen(bytes_), spec.bit_table())
        self.LOWER = m.const("LOWER", frozen(bytes_), spec.lower_table())
        self.FLIP = m.const("FLIP", frozen(bytes_), spec.flip_table())
        self.CTYPE = m.const("CTYPE", frozen(bytes_), spec.ctype_table())

    # --- small conveniences the three builders share ---

    def func(self, name: str, params=(), ret=None):
        return self.m.func(name, params=params, ret=ret)

    def build(self):
        return self.m.build()


__all__ = ["Layout", "boolean", "bytes_", "counter", "frozen", "u8", "u32", "vec"]
