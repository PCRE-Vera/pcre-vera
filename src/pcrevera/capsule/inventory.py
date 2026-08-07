"""The theorem inventory: what is proved, by name, in a form a machine reads.

`THEOREMS.md` is prose, and prose drifts. It already does: it calls the Pike
refinement `pikeRun_refines_matches`, and the theorem is spelled
`pikeRun_refinesMatches`. Nothing caught that, because nothing ever asked Lean.

This module is the inventory that does. Every claim names a layer, an
identifier, the kind of evidence behind it, and the Lean declarations that
carry it, resolved to fully qualified names against the sources so a capsule
verifier can elaborate each one and refuse a claim whose theorem is gone. The
layer I rows are not written here at all: they are computed from the artifact's
own call graph, so a new helper appears in the inventory before anybody can
forget to mention it.

The kinds are kept apart on purpose. A `#guard` that reduces inside the
elaborator is evidence and not a theorem, and the inventory says so rather than
letting a green build read as a proof.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, replace
from pathlib import Path

from ..paths import REPO_ROOT
from ..tir import coverage, ir
from . import canonical, sha256_bytes

PATH = REPO_ROOT / "conformance" / "theorem-inventory.json"

SCHEMA = "pcrevera/theorem-inventory@1"

AXIOMS = ("Classical.choice", "Quot.sound", "propext")
"""The three axioms of Lean's own foundation. A claim may depend on these and
on nothing else; anything further is a foundational decision, and the verifier
refuses to let one arrive unannounced."""

KINDS = ("definition", "proof", "interpreter-check", "replay", "differential")
"""What stands behind a claim. `definition` is a spelling in Lean and carries no
obligation of its own; `proof` is checked by the kernel; `interpreter-check` is
reduction inside the elaborator; `replay` runs recorded answers back through the
reference engine; `differential` compares against the pinned oracle."""

STATUSES = ("complete", "partial", "absent")


@dataclass(frozen=True)
class Decl:
    """One Lean declaration a claim rests on."""

    module: str
    name: str | None
    """The short name inside the module, or None where the claim is about the
    module as a whole and there is no single declaration to elaborate."""


WAVE1_FEATURES = (
    "core.pattern",
    "syntax.alternation",
    "syntax.anchor",
    "syntax.class",
    "syntax.dot",
    "syntax.escape.class",
    "syntax.escape.literal",
    "syntax.escape.newline",
    "syntax.group.capturing",
    "syntax.group.comment",
    "syntax.group.named",
    "syntax.group.noncapturing",
    "syntax.group.options",
    "syntax.literal",
    "syntax.quantifier.greedy",
    "syntax.quantifier.lazy",
    "syntax.quoting",
)
"""The feature keys a wave 1 claim covers.

Layers S and R quantify over the whole wave 1 AST with no feature carve-out, so
a claim about them covers every wave 1 family and says so. This is what turns
the ledger's `claims` column from a list of impressive identifiers into a join:
a feature may only spend a claim that names it. A test holds this tuple to the
ledger's own wave 1 rows."""

REPETITION_FEATURES = ("syntax.quantifier.greedy", "syntax.quantifier.lazy")
"""What the quantifier lowering is about, and nothing else."""


@dataclass(frozen=True)
class Claim:
    id: str
    layer: str
    kind: str
    status: str
    statement: str
    domain: str
    decls: tuple[Decl, ...] = ()
    note: str = ""
    features: tuple[str, ...] = ()
    """The feature keys this claim covers. Empty where the claim is about the
    engine's own representation rather than about a syntax family, which is why
    no layer I claim yet backs any feature's I column."""


_TABLE: tuple[Claim, ...] = (
    Claim(
        "S-1",
        "S",
        "definition",
        "complete",
        "the wave 1 AST as an inductive type, options as parameters",
        "the wave 1 constructors of DESIGN.md section 2.1",
        (Decl("lean/Pcrevera/Spec/Ast.lean", "Ast"),),
    ),
    Claim(
        "S-2",
        "S",
        "definition",
        "complete",
        "priority-ordered big-step search: Found with captures, NotFound, or "
        "BadInput, and nothing else",
        "every spec AST at every fuel",
        (Decl("lean/Pcrevera/Spec/Match.lean", "matchesF"),),
    ),
    Claim(
        "S-3",
        "S",
        "proof",
        "complete",
        "beyond a computable sufficient fuel the answer no longer changes",
        "every spec AST",
        (Decl("lean/Pcrevera/Spec/Total.lean", "matches_stable"),),
    ),
    Claim(
        "S-4",
        "S",
        "definition",
        "complete",
        "S-2 read at the stable fuel of S-3, so totality is earned",
        "every spec AST",
        (Decl("lean/Pcrevera/Spec/Total.lean", "Matches"),),
    ),
    Claim(
        "S-5",
        "S",
        "definition",
        "complete",
        "the internal configuration domain, wider than the public API",
        "Pike, backtracking and memoized, each with or without a context",
        (
            Decl("lean/Pcrevera/Ref/Exec.lean", "Config"),
            Decl("lean/Pcrevera/Ref/Bytecode.lean", "Limits"),
            Decl("lean/Pcrevera/Ref/Exec.lean", "Exec"),
        ),
    ),
    Claim(
        "S-6",
        "S",
        "definition",
        "complete",
        "the creation step, its one-time reservation and zeroing charged "
        "against the creation limits",
        "every compiled pattern and creation limit vector",
        (Decl("lean/Pcrevera/Ref/Exec.lean", "createCtx"),),
    ),
    Claim(
        "S-7",
        "S",
        "proof",
        "complete",
        "Exec answers BadInput exactly where Matches does, plus the "
        "execution-only cases",
        "every configuration Exec admits",
        (Decl("lean/Pcrevera/Proofs/BadInput.lean", "exec_badinput_iff"),),
    ),
    Claim(
        "S-8",
        "S",
        "proof",
        "complete",
        "whenever Exec answers Found or NotFound, that answer is Matches",
        "both matchers, every start offset and match option, over the whole "
        "Config domain",
        (
            Decl("lean/Pcrevera/Proofs/Refine.lean", "btRun_refines_matches"),
            Decl("lean/Pcrevera/Proofs/PikeRefine.lean", "pikeRun_refines_matches"),
            Decl("lean/Pcrevera/Proofs/ExecBacktrack.lean", "btRun_refinesMatches"),
            Decl("lean/Pcrevera/Proofs/ExecPike.lean", "pikeRun_refinesMatches"),
            Decl("lean/Pcrevera/Proofs/ExecContext.lean", "exec_refinesAnswers"),
        ),
        "the Pike half carries the eligibility hypothesis (compile p).pike = true",
    ),
    Claim(
        "S-9",
        "S",
        "proof",
        "complete",
        "raising a limit never changes a Found or NotFound",
        "both limit vectors admitted by the configuration",
        (Decl("lean/Pcrevera/Proofs/Monotone.lean", "exec_monotone"),),
    ),
    Claim(
        "S-10",
        "S",
        "proof",
        "complete",
        "every limit at or above the analyzer's bound rules ResourceExceeded out",
        "both matchers, plain call and context call alike",
        (
            Decl("lean/Pcrevera/Proofs/RepRun.lean", "btRun_inBudget_counted"),
            Decl("lean/Pcrevera/Proofs/PikeBounds.lean", "pikeRun_inBudget"),
            Decl("lean/Pcrevera/Proofs/PikeBounds.lean", "pikeRun_inBudget_ctx"),
        ),
    ),
    Claim(
        "S-11",
        "S",
        "proof",
        "complete",
        "S-10 for a context, conditional on creation having succeeded",
        "the calls a created context admits",
        (
            Decl("lean/Pcrevera/Proofs/CtxSufficient.lean", "ctx_sufficient"),
            Decl("lean/Pcrevera/Proofs/CtxSufficient.lean", "ctx_sufficient_pike"),
            Decl("lean/Pcrevera/Proofs/CtxSufficient.lean", "ctx_sufficient_bt"),
        ),
    ),
    Claim(
        "S-12",
        "S",
        "proof",
        "complete",
        "on a Pike-eligible pattern the two matchers agree under sufficient budgets",
        "every Pike-eligible wave 1 pattern",
        (
            Decl("lean/Pcrevera/Proofs/ExecPike.lean", "matchers_agree_wf"),
            Decl(
                "lean/Pcrevera/Proofs/AgreeSufficient.lean",
                "matchers_agree_sufficient",
            ),
        ),
    ),
    Claim(
        "R-1",
        "R",
        "definition",
        "complete",
        "spec AST to bytecode, the compiler of the real engine restated",
        "every spec AST",
        (Decl("lean/Pcrevera/Ref/Compile.lean", "compile"),),
    ),
    Claim(
        "R-2",
        "R",
        "definition",
        "complete",
        "the bytecode under a configuration: same VM loops, same cost "
        "accounting, same context split",
        "every program and configuration",
        (
            Decl("lean/Pcrevera/Ref/VM.lean", "btRun"),
            Decl("lean/Pcrevera/Ref/Pike.lean", "pikeRun"),
            Decl("lean/Pcrevera/Ref/Exec.lean", "run"),
        ),
    ),
    Claim(
        "R-3",
        "R",
        "definition",
        "complete",
        "the creation step of S-6, executable, with the accessors beside it",
        "every compiled pattern",
        (
            Decl("lean/Pcrevera/Ref/Context.lean", "Ctx"),
            Decl("lean/Pcrevera/Ref/Context.lean", "ctxCreate"),
            Decl("lean/Pcrevera/Ref/Context.lean", "ctxMatch"),
        ),
    ),
    Claim(
        "R-4",
        "R",
        "proof",
        "complete",
        "running the compiled pattern equals Exec: soundness and completeness "
        "in one equation",
        "every configuration, pattern, subject, start and limit vector",
        (Decl("lean/Pcrevera/Ref/Exec.lean", "run_compile_eq_exec"),),
    ),
    Claim(
        "R-5",
        "R",
        "proof",
        "complete",
        "every run halts: the backtracking loop by the cost charge, the "
        "lockstep loops by their declared variants",
        "both matchers",
        (
            Decl("lean/Pcrevera/Proofs/BtTermination.lean", "btRun_halts"),
            Decl("lean/Pcrevera/Proofs/PikeTermination.lean", "pikeAdd_fuel_irrelevant"),
            Decl(
                "lean/Pcrevera/Proofs/PikeTermination.lean", "scanFirst_fuel_irrelevant"
            ),
            Decl(
                "lean/Pcrevera/Proofs/PikeTermination.lean", "pikeHollow_fuel_irrelevant"
            ),
            Decl(
                "lean/Pcrevera/Proofs/PikeTermination.lean", "boundPowGo_fuel_irrelevant"
            ),
        ),
    ),
    Claim(
        "R-6",
        "R",
        "proof",
        "complete",
        "the cost a run charges is at most the certificate's bound at the "
        "subject length",
        "both matchers",
        (
            Decl("lean/Pcrevera/Proofs/RepRun.lean", "btRun_cost_le_counted"),
            Decl("lean/Pcrevera/Proofs/PikeBounds.lean", "pikeRun_cost_le_check"),
        ),
    ),
    Claim(
        "R-7",
        "R",
        "proof",
        "complete",
        "the same for backtrack entries",
        "both matchers",
        (
            Decl("lean/Pcrevera/Proofs/RepRun.lean", "btRun_stack_le_counted"),
            Decl("lean/Pcrevera/Proofs/PikeBounds.lean", "pikeRun_stack_le"),
        ),
    ),
    Claim(
        "R-8",
        "R",
        "proof",
        "complete",
        "the same for scratch bytes, peak capacity with growth overlap included",
        "both matchers",
        (
            Decl("lean/Pcrevera/Proofs/RepRun.lean", "btRun_mem_le_counted"),
            Decl("lean/Pcrevera/Proofs/PikeBounds.lean", "pikeRun_mem_le_check"),
        ),
    ),
    Claim(
        "R-9",
        "R",
        "proof",
        "complete",
        "a created context's resident bytes are worstCaseMemory at the declared "
        "maximum, and no call on it allocates",
        "both matchers, on a context call",
        (
            Decl("lean/Pcrevera/Proofs/CtxReserve.lean", "ctx_resident_eq_reservation"),
            Decl("lean/Pcrevera/Proofs/CtxSufficient.lean", "ctxMatch_no_growth_pike"),
            Decl("lean/Pcrevera/Proofs/CtxSufficient.lean", "ctxMatch_no_growth_bt"),
            Decl("lean/Pcrevera/Proofs/RepRun.lean", "btRun_no_growth_ctx_counted"),
            Decl("lean/Pcrevera/Proofs/PikeBounds.lean", "pikeRun_no_growth"),
        ),
    ),
    Claim(
        "R-10",
        "R",
        "replay",
        "complete",
        "the reference compiler and VM, evaluated on the committed corpora, "
        "give the recorded answers",
        "conformance/corpus.json and conformance/sweep.json through the "
        "committed AST bridge",
        (Decl("lean/CorpusCheck.lean", None),),
    ),
    Claim(
        "L-1",
        "L",
        "definition",
        "complete",
        "the quantifier lowering as a function on Ast, with the condition under "
        "which it preserves the search",
        "every spec AST",
        (
            Decl("lean/Pcrevera/Spec/Lower.lean", "lower"),
            Decl("lean/Pcrevera/Spec/Lower.lean", "Nullable"),
            Decl("lean/Pcrevera/Spec/Lower.lean", "LowerSafe"),
        ),
    ),
    Claim(
        "L-2",
        "L",
        "proof",
        "complete",
        "a tree and its lowered form return the same ordered thread list from "
        "every position, lifted to the public answer",
        "every LowerSafe tree",
        (
            Decl("lean/Pcrevera/Proofs/LowerMatch.lean", "lower_searchEq"),
            Decl("lean/Pcrevera/Proofs/LowerPat.lean", "Matches_lower"),
        ),
    ),
    Claim(
        "L-2a",
        "L",
        "proof",
        "complete",
        "the bounded splice, a finite induction needing no semantic hypothesis",
        "every bounded repetition, the empty range included",
        (Decl("lean/Pcrevera/Proofs/LowerSplice.lean", "evRep_bounded"),),
    ),
    Claim(
        "L-2b",
        "L",
        "proof",
        "complete",
        "the unbounded splice: past the minimum the count is read in two places "
        "and both have stopped caring",
        "every unbounded repetition whose body must consume",
        (
            Decl("lean/Pcrevera/Proofs/LowerSplice.lean", "evRep_unbounded"),
            Decl("lean/Pcrevera/Proofs/LowerSplice.lean", "searchRep_count_free"),
        ),
    ),
    Claim(
        "L-3",
        "L",
        "proof",
        "complete",
        "the structural preservation lemmas, gathered at the pattern",
        "every well-formed tree",
        (
            Decl("lean/Pcrevera/Proofs/LowerShape.lean", "maxGroup_lower"),
            Decl("lean/Pcrevera/Proofs/LowerShape.lean", "crWalk_lower"),
            Decl("lean/Pcrevera/Proofs/LowerWf.lean", "wfAst_lower"),
            Decl("lean/Pcrevera/Proofs/LowerWf.lean", "capsBelow_lower"),
            Decl("lean/Pcrevera/Proofs/LowerWf.lean", "wf_lowered"),
            Decl("lean/Pcrevera/Proofs/LowerWf.lean", "covered_lower"),
        ),
    ),
    Claim(
        "L-4",
        "L",
        "proof",
        "absent",
        "the lowering moved inside Ref.compile, so the pipeline spends L-2 "
        "rather than the bridge",
        "outstanding in M7R; see PLAN-M7.md section 10",
    ),
    Claim(
        "L-5",
        "L",
        "proof",
        "absent",
        "the emitted-size counting theorem restated over the lowered sizes",
        "outstanding in M7R; see PLAN-M7.md section 10",
    ),
    Claim(
        "I-1",
        "I",
        "definition",
        "complete",
        "the TIR syntax, its interpreter and its execution relation, with "
        "stability and uniqueness of a run",
        "every TIR program",
        (
            Decl("lean/Pcrevera/Tir/Syntax.lean", "Program"),
            Decl("lean/Pcrevera/Tir/Interp.lean", "Value"),
            Decl("lean/Pcrevera/Tir/Exec.lean", "Runs"),
            Decl("lean/Pcrevera/Tir/Stable.lean", "runs_stable"),
            Decl("lean/Pcrevera/Tir/Stable.lean", "runs_unique"),
        ),
    ),
    Claim(
        "I-2",
        "I",
        "proof",
        "partial",
        "the decoder inverts the printer's tree for every canonical program",
        "every canonical program at sufficient decode depth",
        (
            Decl("lean/Pcrevera/Tir/Print.lean", "programJ"),
            Decl("lean/Pcrevera/Tir/Decode.lean", "decode"),
            Decl("lean/Pcrevera/Tir/RoundTrip.lean", "decodeProgram_programJ"),
            Decl("lean/Pcrevera/Tir/PrintCheck.lean", None),
            Decl("lean/Pcrevera/Tir/Artifact.lean", None),
        ),
        "the step from printed text to a parsed value stays a check: "
        "PrintCheck.lean holds the printer to serialize.dumps byte for byte, "
        "and Artifact.lean settles the canonicality premise on the artifact by "
        "reduction, which is the interpreter and not the kernel",
    ),
    Claim(
        "I-3",
        "I",
        "interpreter-check",
        "complete",
        "the committed artifact decodes and prints back to the same bytes, and "
        "is canonical inside its decode fuel",
        "gen/engine.tir.json, by reduction in the elaborator rather than by "
        "the kernel",
        (Decl("lean/Pcrevera/Tir/Artifact.lean", None),),
        "the evidence is the module's #guards, which are not declarations and "
        "are deliberately not recorded as theorems; what the row pins is the "
        "module they live in",
    ),
    Claim(
        "I-4",
        "I",
        "proof",
        "complete",
        "the artifact's region_kids means what Ref.regionKids means",
        "one artifact function",
        (Decl("lean/Pcrevera/Tir/RegionKids.lean", "region_kids_simulates"),),
    ),
    Claim(
        "I-5",
        "I",
        "proof",
        "absent",
        "the per-function simulation campaign over the compiler",
        "outstanding in M7R; see PLAN-M7.md section 10",
    ),
    Claim(
        "I-6",
        "I",
        "proof",
        "absent",
        "the per-function simulation campaign over the matchers",
        "outstanding in M7R; see PLAN-M7.md section 10",
    ),
    Claim(
        "I-7",
        "I",
        "proof",
        "partial",
        "the pool allocator simulates Ref.chargeGrow, given a contract for "
        "charge_grow that is itself unproved",
        "one artifact function, conditionally",
        (Decl("lean/Pcrevera/Tir/PikeTake.lean", "pike_take_simulates"),),
        "the coverage ledger does not count this theorem, because its "
        "hypothesis is the obligation the campaign owes",
    ),
    Claim(
        "I-8",
        "I",
        "proof",
        "absent",
        "the composed compiler theorem",
        "outstanding in M7R; see PLAN-M7.md section 10",
    ),
    Claim(
        "I-9",
        "I",
        "proof",
        "absent",
        "the composed matcher theorem",
        "outstanding in M7R; see PLAN-M7.md section 10",
    ),
    Claim(
        "I-10",
        "I",
        "proof",
        "absent",
        "the artifact theorem, the composition of I-5 to I-9",
        "outstanding in M7R; see PLAN-M7.md section 1 for the statement it "
        "would be",
    ),
)


def _covering(claim: Claim) -> Claim:
    """Which features a claim covers, where the table does not say.

    Layers S and R quantify over the whole wave 1 AST and carry no feature
    hypothesis, so every one of their claims covers every wave 1 family; saying
    that once here is more honest than repeating a seventeen-element tuple
    twenty-two times, and gate 2a is where claims start differing by feature.
    The lowering is about counted repetition alone. Layer I is about the
    artifact's own representation, so its claims cover no syntax family at all,
    which is why nothing yet backs a feature's I column.
    """
    if claim.features:
        return claim
    if claim.layer in ("S", "R"):
        return replace(claim, features=WAVE1_FEATURES)
    if claim.layer == "L":
        return replace(claim, features=REPETITION_FEATURES)
    return claim


CLAIMS: tuple[Claim, ...] = tuple(_covering(claim) for claim in _TABLE)


MODIFIERS =r"(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*"

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    + MODIFIERS
    + r"(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([^\s({\[:]+)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)")
SCOPE_RE = re.compile(r"^" + MODIFIERS + r"(section|mutual)(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")


class ScopeError(ValueError):
    """A module whose scopes do not balance the way this reader models them.

    Raised rather than guessed at, because the alternative is a qualified name
    that is quietly wrong: a declaration read one namespace too deep still
    looks like a name, and the inventory would record it as the theorem.
    """


IDENT = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?")


def uncommented(source: str) -> list[str]:
    """The module's lines with comments blanked out, line numbering intact.

    Necessary rather than fussy: `Basic.lean` opens with a doc comment whose
    prose starts a line with the word `namespace`, and a reader that took that
    for a scope would put every declaration in the file one level too deep.

    Four lexical facts have to be honoured for that not to happen anywhere
    else. Lean's block comments nest. A `--` inside a string is not a comment.
    A raw string `r#"..."#` ends only at a quote followed by as many hashes as
    opened it, so the quotes inside one toggle nothing. And `'"'` is a
    character literal, not the start of a string — `Print.lean` writes exactly
    that, and a reader that misses it spends the rest of the file guessing.
    """
    out: list[str] = []
    depth = 0
    instring = False
    raw: int | None = None
    for line in source.splitlines():
        kept: list[str] = []
        i = 0
        while i < len(line):
            two = line[i : i + 2]
            if raw is not None:
                if line[i] == '"' and line[i + 1 : i + 1 + raw] == "#" * raw:
                    i += 1 + raw
                    raw = None
                else:
                    i += 1
                continue
            if instring:
                kept.append(line[i])
                if line[i] == "\\":
                    if i + 1 < len(line):
                        kept.append(line[i + 1])
                    i += 2
                    continue
                if line[i] == '"':
                    instring = False
                i += 1
                continue
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/" and depth:
                depth -= 1
                i += 2
                continue
            if depth:
                i += 1
                continue
            if two == "--":
                break
            fresh = i == 0 or line[i - 1] not in IDENT
            if line[i] == "r" and fresh:
                hashes = 0
                while line[i + 1 + hashes : i + 2 + hashes] == "#":
                    hashes += 1
                if line[i + 1 + hashes : i + 2 + hashes] == '"':
                    raw = hashes
                    i += 2 + hashes
                    continue
            if line[i] == "'" and fresh:
                closing = _char_literal(line, i)
                if closing is not None:
                    kept.append("'")
                    i = closing + 1
                    continue
            if line[i] == '"':
                instring = True
            kept.append(line[i])
            i += 1
        out.append("".join(kept))
    if depth or instring or raw is not None:
        raise ScopeError("the module ends inside a comment, string or raw string")
    return out


CHAR_ESCAPE_WIDTH = 8
"""Enough for `\\u1234`, the widest escape a Lean character literal has."""


def _char_literal(line: str, start: int) -> int | None:
    """Where a character literal opening at `start` closes, or None.

    An apostrophe is also a perfectly good identifier character, so this is only
    consulted where one cannot be a suffix, and it still has to find a plausible
    closing quote before deciding.
    """
    if line[start + 1 : start + 2] == "\\":
        end = line.find("'", start + 2, start + 2 + CHAR_ESCAPE_WIDTH)
        return end if end != -1 else None
    if line[start + 2 : start + 3] == "'":
        return start + 2
    return None


def _close(
    stack: list[tuple[str, str | None]], want: str | None, number: int, line: str
) -> None:
    """Pop what an `end` closes, which may be more than one frame.

    `end A.B` closes two nested namespaces at once, so the frames are popped
    until their names join back into the name written. A bare `end` closes the
    anonymous scope a `section` or a `mutual` opened.
    """
    if want is None:
        if stack and stack[-1] == ("scope", None):
            stack.pop()
            return
        raise ScopeError(f"line {number}: {line.strip()!r} closes nothing open")
    parts: list[str] = []
    while stack and stack[-1][1] is not None:
        parts.insert(0, stack.pop()[1])
        if ".".join(parts) == want:
            return
    raise ScopeError(f"line {number}: {line.strip()!r} closes nothing open")


def declarations(source: str) -> dict[str, str]:
    """Every declaration a Lean module makes, short name to qualified name.

    Three things open a scope here and all three are tracked: `namespace`,
    which contributes to the qualified name, and `section` and `mutual`, which
    do not but still have to be closed before the `end` that closes a namespace
    is read as one. `_root_.` escapes the namespace stack, which is how
    `Pat.crFirst` gets out of `Pcrevera.Spec`.

    A repeated short name maps to nothing rather than to a guess: the inventory
    names one declaration, and two candidates mean it does not know which.
    """
    stack: list[tuple[str, str | None]] = []
    seen: dict[str, str | None] = {}
    for number, line in enumerate(uncommented(source), 1):
        opened = NAMESPACE_RE.match(line)
        if opened:
            # One frame per component, because `namespace Std.Stream` may be
            # closed by `end Stream` alone, leaving `Std` open.
            stack.extend(("namespace", part) for part in opened.group(1).split("."))
            continue
        scoped = SCOPE_RE.match(line)
        if scoped:
            stack.append(("scope", scoped.group(2)))
            continue
        closed = END_RE.match(line)
        if closed:
            _close(stack, closed.group(1), number, line)
            continue
        found = DECL_RE.match(line)
        if not found:
            continue
        written = found.group(2)
        if written.startswith("_root_."):
            qualified = written[len("_root_.") :]
        else:
            prefix = [name for kind, name in stack if kind == "namespace"]
            qualified = ".".join([*prefix, written])
        short = written.rsplit(".", 1)[-1]
        seen[short] = None if short in seen else qualified
    # A namespace left open at the end of a file is legal Lean and costs the
    # reader nothing: it applies to every declaration below it either way. A
    # mismatched `end` is the opposite, and is refused above.
    return {short: name for short, name in seen.items() if name is not None}


def resolve(claim: Claim, decl: Decl, root: Path) -> dict:
    """One declaration row: its module, its hash, and its qualified name."""
    path = root / decl.module
    if not path.is_file():
        raise LookupError(f"{claim.id} names {decl.module}, which is not a file")
    data = path.read_bytes()
    row = {"module": decl.module, "sha256": sha256_bytes(data)}
    if decl.name is None:
        return row
    names = declarations(data.decode("utf-8"))
    if decl.name not in names:
        raise LookupError(
            f"{claim.id} names {decl.name} in {decl.module}, which declares no "
            "such name once"
        )
    row["lean"] = names[decl.name]
    return row


def build(program: ir.Program, artifact_sha256: str, root: Path = REPO_ROOT) -> dict:
    """The inventory, resolved against the Lean sources and the artifact."""
    claims = []
    for claim in CLAIMS:
        row = {
            "id": claim.id,
            "layer": claim.layer,
            "kind": claim.kind,
            "status": claim.status,
            "statement": claim.statement,
            "domain": claim.domain,
            "features": list(claim.features),
            "declarations": [resolve(claim, decl, root) for decl in claim.decls],
        }
        if claim.note:
            row["note"] = claim.note
        claims.append(row)

    ledger = coverage.ledger(program, artifact_sha256)
    owed = ledger["post_parse"]

    by_layer: dict[str, int] = {}
    by_kind: dict[str, int] = {}
    by_status: dict[str, int] = {}
    for claim in CLAIMS:
        by_layer[claim.layer] = by_layer.get(claim.layer, 0) + 1
        by_kind[claim.kind] = by_kind.get(claim.kind, 0) + 1
        by_status[claim.status] = by_status.get(claim.status, 0) + 1

    return {
        "schema": SCHEMA,
        "artifact": artifact_sha256,
        "axioms": list(AXIOMS),
        "counts": {
            "claims": len(CLAIMS),
            "byLayer": by_layer,
            "byKind": by_kind,
            "byStatus": by_status,
        },
        "claims": claims,
        "layerI": {
            "domain": [entry["name"] for entry in owed],
            "counts": {
                "owed": len(owed),
                "proved": sum(1 for entry in owed if entry["theorem"]),
            },
            "functions": owed,
        },
    }


def render(built: dict) -> str:
    return canonical(built)


# Greedy up to the fixed tail, because Lean lets an identifier end in an
# apostrophe and `'foo'' depends on axioms: [...]` is what it then prints.
AXIOM_LINE = re.compile(r"^'(.+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE)
NO_AXIOMS = re.compile(r"^'(.+)' does not depend on any axioms", re.MULTILINE)


def elaboration_source(built: dict) -> str:
    """A Lean module that asks Lean about every name the inventory records.

    Reading a name out of a source file proves it is written there. It does not
    prove Lean accepts it, that it is the theorem and not a variable shadowing
    one, or that its proof rests on the three axioms and nothing else. This
    module is what settles those, and it is generated from the inventory so it
    cannot fall behind it.
    """
    modules: list[str] = []
    checks: list[str] = []
    for claim in built["claims"]:
        for decl in claim["declarations"]:
            if "lean" not in decl:
                continue
            module = decl["module"]
            if not module.startswith("lean/") or not module.endswith(".lean"):
                raise LookupError(f"{claim['id']}: {module} is not a Lean module path")
            name = module[len("lean/") : -len(".lean")].replace("/", ".")
            if name not in modules:
                modules.append(name)
            checks.append(f"#check @{decl['lean']}")
            checks.append(f"#print axioms {decl['lean']}")
    imports = "\n".join(f"import {name}" for name in modules)
    return imports + "\n\n" + "\n".join(checks) + "\n"


def axioms_used(output: str) -> dict[str, list[str]]:
    """What `#print axioms` reported, name by name."""
    found: dict[str, list[str]] = {}
    for name in NO_AXIOMS.findall(output):
        found[name] = []
    for name, listed in AXIOM_LINE.findall(output):
        found[name] = [axiom.strip() for axiom in listed.split(",") if axiom.strip()]
    return found


__all__ = [
    "AXIOMS",
    "CLAIMS",
    "KINDS",
    "PATH",
    "SCHEMA",
    "STATUSES",
    "Claim",
    "Decl",
    "ScopeError",
    "axioms_used",
    "build",
    "declarations",
    "elaboration_source",
    "render",
    "resolve",
    "uncommented",
]
