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
        # selected. Which path that is settles nothing on its own: a
        # Pike-eligible pattern is linear, and so is `\R`, which is not
        # eligible and carries a linear backtracking bound anyway. What the
        # test-only backtracking certificate of an eligible pattern claims is
        # about the path nobody can ask for, and it may honestly say
        # otherwise.
        #
        # The order is the point rather than an accident, here and in `Cr`
        # below: a zero value is the first variant (TIR-SPEC.md section 4.1),
        # so a certificate nobody finished filling in has to come out claiming
        # nothing rather than claiming to be linear.
        self.Cc = m.enum("Cc", ["CcNotProvenLinear", "CcLinear"])

        self.Bk = m.enum("Bk", ["BkCost", "BkStack", "BkMem"])

        # And what the analyzer came back with. Two of these are the honest
        # answer for a pattern that has no bound of the shape BOUNDS.md section
        # 2 writes down, and compilation goes on without a certificate.
        # `ArShape` is the other kind: the analyzer met something in the region
        # tree it had no rule for, which for a tree the compiler emitted is a
        # bug of ours. It is first so that a verdict nobody assigned says
        # exactly that, and `ArOk` is last so that one never claims success.
        self.Ar = m.enum("Ar", ["ArShape", "ArAmbiguous", "ArOverflow", "ArOk"])

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
                "CrIneligible",
                "CrPrices",
                "CrBase",
                # The tree accounts for the bytecode it claims to cover, and
                # every field of the certificate names something the checker
                # knows: `CrShape` covers a value that names no variant too,
                # since an enum is an integer once printed.
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
                "CrTotalTrail",
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

        # What one AST node's lowered form comes to, and what the pre-check
        # found under it. The compiler computes one of these per arena slot in
        # a single reverse scan — children always sit above their parent — and
        # reads the root's off the top, which is how the fit vector of
        # DESIGN.md section 4.3 is decided without expanding anything.
        #
        # The four sizes are counters because they multiply: a quantifier may
        # name 65535 and quantifiers nest, so the product is exactly the number
        # that has to saturate rather than wrap. The two transient counts do
        # not multiply — the lowering copies constructs side by side, never
        # inside one another — so u32 is the honest width for them.
        self.Size = m.struct(
            "Size",
            [
                ("code", counter),
                ("regions", counter),
                ("reps", counter),
                ("visits", counter),
                ("depth", u32),
                ("patches", u32),
                # Can this subtree match without consuming a byte? Read the
                # way `pike_hollow` reads the bytecode, so assertions count as
                # non-consuming and the two answers agree.
                ("nullable", boolean),
                ("blockers", u32),
                # Is there a repetition under here that the lowering would
                # actually rewrite? A pattern with none is already canonical.
                ("needs", boolean),
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

        # `here` is the region anything this job emits belongs to. A job that
        # opens a region of its own overwrites it, so children are pushed with
        # the innermost one and the closing visit knows what to finish. `arm`
        # is the alternation branch currently open, which is the one thing a
        # job can be building two of at once.
        self.Job = m.struct(
            "Job",
            [
                ("node", u32),
                ("phase", u32),
                ("cur", u32),
                ("mark", u32),
                ("base", u32),
                ("here", u32),
                ("arm", u32),
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

        # One Pike thread: where it is suspended and which capture block it
        # holds, as a handle into the copy-on-write pool rather than as slots
        # of its own — sharing a block is a handle copy and a refcount bump,
        # which is what keeps forking cheap and the pool inside the section 5
        # memory accounting.
        self.Th = m.struct("Th", [("pc", u32), ("h", u32)])

        self.Esc = m.struct("Esc", [("kind", self.Ek), ("val", u32)])

        # --- the bound certificate ---
        #
        # One bound is a polynomial over a single growth base:
        #
        #     base^n * (c0 + c1*(n+1) + c2*(n+1)^2 + ... )
        #
        # in the subject length n. A base of one is the polynomial case, which
        # every Pike-eligible pattern gets and plenty of backtracking ones do
        # too; a base above one is the shape a backtracking bound takes when
        # the structural analysis of BOUNDS.md finds genuine ambiguity.
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

        # What a public analysis accessor answers. `Bound` cannot carry it:
        # DESIGN.md section 2.4 gives the accessors three outcomes — a finite
        # number, ExceedsBudget, and BadInput for a configuration or length the
        # pattern cannot be asked about — and a single flag folds the last two
        # together. The status is the outcome ordinal of spec.py, the same
        # numbering `match` reports, so ExceedsBudget is distinct from the
        # runtime ResourceExceeded by construction. When the status is not OK
        # the value says nothing.
        self.Answer = m.struct("Answer", [("status", u32), ("value", counter)])

        # A region is one source construct the compiler flattened, and it is
        # the compiler that emits it: it has the AST in hand while it lays out
        # the bytecode, which is the one moment anything knows that this stretch
        # of instructions came from that quantifier. The table lives on the
        # compiled pattern, so there is one of it, and the checker holds it to
        # the bytecode rather than believing it.
        self.Region = m.struct(
            "Region",
            [("kind", self.Rk), ("parent", u32), ("lo", u32), ("hi", u32)],
        )

        # And this is what a certificate says one entry into that region costs:
        # instruction visits, backtrack entries pushed, undo entries recorded,
        # and the forward exits it hands the construct that follows it. The
        # last one is the region's ambiguity, and it is the multiplier
        # everything else in BOUNDS.md composes with. One price per region, in
        # the same order, so a claim cannot be about a region nobody emitted.
        self.Price = m.struct(
            "Price",
            [
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
        self.Sizes = vec(self.Size, spec.MAX_NODES)
        self.Order = vec(u32, spec.MAX_NODES)
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
        self.Prices = vec(self.Price, spec.MAX_REGIONS)
        self.Marks = vec(u32, spec.MAX_REGIONS)
        self.Threads = vec(self.Th, spec.MAX_THREADS)
        self.Closure = vec(self.Th, spec.MAX_CLOSURE)
        self.Slots = vec(u32, spec.MAX_POOL)
        self.Blocks = vec(u32, spec.MAX_BLOCKS)
        self.Steps = vec(u32, spec.MAX_CLOSURE)

        self.FrozenCode = frozen(self.Code)
        self.FrozenReps = frozen(self.Reps)
        self.FrozenRegions = frozen(self.Regions)
        self.FrozenPrices = frozen(self.Prices)

        # A certificate is frozen the moment the analyzer is done with it, for
        # the same reason the compiled pattern is: one of them serves any number
        # of simultaneous accessor calls, and nothing can write through it.
        #
        # Three of the whole-pattern bounds are the ones the accessors of
        # DESIGN.md section 2.4 report. They are not the root region's numbers:
        # a region is priced per entry into it, and the pattern is entered once
        # per starting position, on top of setup and scratch growth that no
        # region covers.
        #
        # `trail` is the fourth, and it is not an accessor's answer: it is the
        # other array a preallocated context sizes, held to the same section 5
        # equality as the stack so that the memory bound really pays for what
        # the two claims demand.
        self.Cert = m.struct(
            "Cert",
            [
                ("config", self.Cfg),
                ("complexity", self.Cc),
                ("cost", self.Poly),
                ("stack", self.Poly),
                ("trail", self.Poly),
                ("mem", self.Poly),
                ("prices", self.FrozenPrices),
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
                ("regions", self.FrozenRegions),
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
                # Whether the Pike VM may run this program: every repetition
                # is a pure star and nothing consumes a variable number of
                # bytes, so the bytecode is state-free and a visited set keyed
                # by pc alone is sound (DESIGN.md section 4.3). Fixed at
                # compilation, like everything else about the execution path.
                ("pike", boolean),
                # What the compiler decided about lowering this pattern's
                # counted repetitions, which of the two blockers the pre-check
                # found on the original AST, and whether the fully lowered
                # candidate would have fitted the storage caps. Three separate
                # answers because they are three separate questions: a pattern
                # can be left in counter form by a blocker and be oversized as
                # well, and a report that recombined them could not say so.
                ("lowdec", u32),
                ("blockers", u32),
                ("lowfits", boolean),
                # The bound certificate for the backtracking configuration, and
                # whether there is one. Compilation runs the analyzer and then
                # the checker, and only a `CrOk` puts anything here, so the
                # flag is what separates "certified" from "the analyzer found
                # no bound of a shape this arithmetic can write down".
                #
                # It is a flag rather than something read off the certificate
                # because a zero-valued `Cert` is a perfectly well-formed
                # claim — `CfgBacktrack`, not proven linear, and nothing costs
                # anything — and that is the one reading a caller must never
                # get from a pattern nobody priced.
                ("hascert", boolean),
                ("cert", self.Cert),
                # And the same pair for the Pike configuration, present
                # exactly on eligible patterns whose closed form fits counter
                # arithmetic. Two slots rather than a table because wave 1
                # has two configurations, and the accessors read whichever
                # one prices the path compilation selected.
                ("haspikecert", boolean),
                ("pikecert", self.Cert),
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
                ("regions", self.Regions),
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
                # The lowering's own workings: the per-node sizes, the
                # decision they led to, and the fit vector the emitter is held
                # to afterwards. `predicted` says whether that vector
                # describes what is about to be emitted — it does when the
                # lowering runs and when there was nothing to lower, and it
                # does not when a blocker sent the pattern back to counter
                # form, since then the sizes describe a program nobody emits.
                ("sizes", self.Sizes),
                # Every reachable node, parents before children. The arena's
                # own order is not that: an alternation node is allocated when
                # the first `|` is read, which is after its own first branch,
                # so a reverse scan of the arena would price that branch after
                # the alternation that needs it. One pass down this list
                # instead, and every child is priced before its parent.
                ("order", self.Order),
                ("lowering", boolean),
                ("lowdec", u32),
                ("blockers", u32),
                ("lowfits", boolean),
                ("predicted", boolean),
                ("fitcode", counter),
                ("fitregion", counter),
                ("fitrep", counter),
                ("fitregs", counter),
                ("fitvisit", counter),
                ("fitjobs", u32),
                ("fitpatch", u32),
                # And what the walk really reached, so that the two
                # calculations of one number can be compared instead of
                # trusted.
                ("peakjobs", u32),
                ("peakpatch", u32),
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

        # What the Pike VM's scratch comes to, as the growth schedule's final
        # capacities: one count per array group — each thread list, the
        # closure stack, each copy-on-write table, the pool — the visited
        # set's width in bytes, and their weighed sum R, the section 9
        # reservation. Computed by one function and read by both the pricer
        # and context creation, so the certificate's memory bound and the
        # reservation a context materializes cannot disagree.
        self.Room = m.struct(
            "Room",
            [
                ("lists", counter),
                ("stk", counter),
                ("tables", counter),
                ("pool", counter),
                ("words", u32),
                ("reserved", counter),
            ],
        )

        # --- the preallocated context (DESIGN.md section 2.4) ---
        #
        # Everything a match needs, owned once: the compiled pattern, the
        # baked ceilings, and every scratch array the selected matcher
        # touches. Creation reserves each array at the growth schedule's
        # final capacity for its certificate bound and zeroes the lot,
        # `slack` materializes the growth-overlap copy the section 5 memory
        # bound charges for, and together with the two caller-owned result
        # stores — the ovector the run cores fill and the converted view a
        # match answers through — the reservations come to exactly
        # `worstCaseMemory(maxlen)`: a context is the memory bound made
        # physical, which is what lets a call on one allocate nothing at
        # all. The ovector travels as a call parameter rather than a field
        # because a linear field cannot be read through the generated
        # façade: each wrapper materializes it once beside the context and
        # hands it in, which is the same ownership either way.
        #
        # `ready` is written last by a creation that accepted everything and
        # first by one that refused, so a context that was never created, or
        # whose creation refused, answers BadInput rather than matching on
        # arrays nobody reserved.
        self.Ctx = m.struct(
            "Ctx",
            [
                ("re", self.Re),
                ("ready", boolean),
                ("maxlen", u32),
                ("costcap", counter),
                ("stackcap", u32),
                ("memcap", counter),
                ("regs", self.Regs),
                ("bt", self.Stack),
                ("trail", self.Trail),
                ("clist", self.Threads),
                ("nlist", self.Threads),
                ("stk", self.Closure),
                ("seen", bytes_),
                ("pool", self.Slots),
                ("rc", self.Blocks),
                ("free", self.Blocks),
                ("slack", bytes_),
            ],
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
