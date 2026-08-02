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

        # The vocabulary of the resource analysis, from DESIGN.md section 5.
        # `Rk` says what source construct a region came from, `Cfg` names the
        # internal configuration a certificate prices, `Cc` is the complexity
        # class the analysis claims, `Bk` picks which of the three bounds an
        # accessor is asking for, and `Cr` is the checker's verdict.
        #
        # A kind is not a label: BOUNDS.md gives each one its own composition
        # rule and its own shape for the bytecode it covers, so naming the
        # wrong kind is a refusal rather than a mislabelled tree.

        self.Rk = m.enum("Rk", ["RkRoot", "RkGroup", "RkBranch", "RkAlt", "RkRepeat"])

        self.Cfg = m.enum("Cfg", ["CfgBacktrack", "CfgPike", "CfgMemo"])

        # What a certificate claims about its own cost bound, which is not
        # quite the pattern's complexity class. The class of a pattern is fixed
        # at compilation and takes no configuration (DESIGN.md section 2.4),
        # and it is the class of the certificate for the path compilation
        # selected: a Pike-eligible pattern is linear, and its test-only
        # backtracking certificate honestly says otherwise about the path
        # nobody can ask for.
        #
        # The order is the point rather than an accident, here and in `Cr`
        # below: a zero value is the first variant (TIR-SPEC.md section 4.1),
        # so a certificate nobody finished filling in has to come out claiming
        # nothing rather than claiming to be linear.
        self.Cc = m.enum("Cc", ["CcNotProvenLinear", "CcLinear"])

        self.Bk = m.enum("Bk", ["BkCost", "BkStack", "BkMem"])

        self.Cr = m.enum(
            "Cr",
            [
                # The tree is a tree, and its ranges nest.
                "CrNoRegions",
                "CrRootKind",
                "CrRootParent",
                "CrRootRange",
                "CrTwoRoots",
                "CrParentOrder",
                "CrBackwards",
                "CrNotNested",
                "CrOverlap",
                # The certificate is about this program, in this configuration.
                "CrNoRules",
                "CrConfig",
                "CrBase",
                # The tree accounts for the bytecode it claims to cover.
                "CrOpcode",
                "CrShape",
                "CrChildren",
                # The composition rules of BOUNDS.md have an answer, and the
                # certificate is at least as large as the answer.
                "CrAmbiguous",
                "CrOverflow",
                "CrRegionWork",
                "CrRegionOuts",
                "CrRegionStack",
                "CrRegionTrail",
                "CrTotalCost",
                "CrTotalStack",
                "CrTotalMem",
                "CrNotLinear",
                # Last, so that a verdict nobody assigned is a refusal.
                "CrOk",
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

        # --- the bound certificate ---
        #
        # One bound is a polynomial over a single growth base:
        #
        #     base^n * (c0 + c1*(n+1) + c2*(n+1)^2 + ... )
        #
        # in the subject length n. A base of one is the polynomial case, which
        # is what a Pike-eligible pattern gets; a base above one is the shape a
        # backtracking bound takes when the structural analysis of BOUNDS.md
        # finds genuine ambiguity.
        #
        # Writing the powers in (n + 1) rather than in n is what makes the form
        # closed under the two things the checker does with it. Every basis
        # function is then at least 1 and nondecreasing, so a sum of two bounds
        # with different bases can be over-approximated by the larger base
        # without going wrong at n = 0, and a claim dominates a requirement
        # exactly when it dominates it coefficient by coefficient.
        #
        # `Bound` is what evaluating one answers: a number, or the explicit
        # refusal DESIGN.md section 2.4 calls ExceedsBudget. When `ok` is false
        # the value says nothing, because "at least 2^53" is not a budget
        # anybody can plan with.

        self.Poly = m.struct(
            "Poly",
            [("base", counter)]
            + [(f"c{degree}", counter) for degree in range(spec.MAX_DEGREE + 1)],
        )

        self.Bound = m.struct("Bound", [("ok", boolean), ("value", counter)])

        # What a region costs for one entry into it: instruction visits,
        # backtrack entries pushed, undo entries recorded, and the forward
        # exits it hands the construct that follows it. The last one is the
        # region's ambiguity, and it is the multiplier everything else in
        # BOUNDS.md composes with.
        self.Region = m.struct(
            "Region",
            [
                ("kind", self.Rk),
                ("parent", u32),
                ("lo", u32),
                ("hi", u32),
                ("work", self.Poly),
                ("outs", self.Poly),
                ("stack", self.Poly),
                ("trail", self.Poly),
            ],
        )

        # The running total of a walk across one span of bytecode: what it has
        # charged so far, and the flow reaching the point it has got to.
        self.Acc = m.struct(
            "Acc",
            [
                ("work", self.Poly),
                ("stack", self.Poly),
                ("trail", self.Poly),
                ("flow", self.Poly),
            ],
        )

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
        self.Regions = vec(self.Region, spec.MAX_REGIONS)
        self.Marks = vec(u32, spec.MAX_REGIONS)

        self.FrozenCode = frozen(self.Code)
        self.FrozenReps = frozen(self.Reps)
        self.FrozenRegions = frozen(self.Regions)

        # A certificate is frozen the moment the analyzer is done with it, for
        # the same reason the compiled pattern is: one of them serves any number
        # of simultaneous accessor calls, and nothing can write through it.
        #
        # The three whole-pattern bounds are the ones the accessors of
        # DESIGN.md section 2.4 report. They are not the root region's numbers:
        # a region is priced per entry into it, and the pattern is entered once
        # per starting position, on top of setup and scratch growth that no
        # region covers.
        self.Cert = m.struct(
            "Cert",
            [
                ("config", self.Cfg),
                ("complexity", self.Cc),
                ("cost", self.Poly),
                ("stack", self.Poly),
                ("mem", self.Poly),
                ("regions", self.FrozenRegions),
            ],
        )

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
