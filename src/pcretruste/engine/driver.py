"""Running the TIR engine from Python.

The same two questions the oracle answers — compile this, match that — asked of
our own engine through the reference interpreter, and answered with the same
value types wherever pcre2 has the same outcome. Where it does not, the answer
is one of ours: an unsupported construct, a pattern past our documented limits,
a run that went over the caller's budget, or bad input.

This is the M3 execution path. The Go and JavaScript backends (M4) run the same
program without going through Python at all, and must agree with it bit for bit.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from ..oracle.client import Compiled, CompileError, Match, NoMatch
from ..tir.interp import Cell, Frozen, Interpreter, Seq, StructValue, Tag
from ..tir.types import CAP, CEILING, COUNTER, INT_RANGE, U8, U32, StructType, Type
from . import spec
from .program import program

STEPS_PER_UNIT = 256
"""Interpreter steps to allow per engine cost unit.

The interpreter counts its own statements, which the engine's cost model knows
nothing about, so the step budget is derived from the caller's cost limit with
room to spare. That keeps `OutOfFuel` — an outcome only this execution path can
give — unreachable, and leaves the engine's own limits as the ones that decide.
"""

SETUP_STEPS = 20_000_000
"""Steps allowed for compilation and setup, before any cost unit is charged."""

DEFAULT_COST_LIMIT = 10_000_000
DEFAULT_STACK_LIMIT = 100_000
DEFAULT_MEMORY_LIMIT = 64 * 1024 * 1024

# What a limit may say at all, from DESIGN.md section 2.4: a cost no larger
# than the counter saturation point, a memory reservation no larger than the
# portable allocation ceiling, and a stack no deeper than that ceiling divided
# by what one entry weighs. Anything else is BadInput, never a silent clamp.
MAX_COST_LIMIT = CAP
MAX_MEMORY_LIMIT = CEILING
MAX_STACK_LIMIT = spec.MAX_STACK


@dataclass(frozen=True)
class Unsupported:
    """A construct or option pcre2 accepts and this release does not."""

    code: int
    offset: int
    what: str


@dataclass(frozen=True)
class TooLarge:
    """A pattern past one of the documented portable limits of spec.py."""

    code: int = spec.E_PATTERN_TOO_LARGE


@dataclass(frozen=True)
class ResourceExceeded:
    """The run went over the cost, stack, or scratch-memory limit."""


@dataclass(frozen=True)
class BadInput:
    """A start offset outside the subject, or another argument we refuse."""


@dataclass(frozen=True)
class Usage:
    cost: int
    stack: int
    memory: int


@dataclass(frozen=True)
class Limits:
    cost: int = DEFAULT_COST_LIMIT
    stack: int = DEFAULT_STACK_LIMIT
    memory: int = DEFAULT_MEMORY_LIMIT


@dataclass(frozen=True)
class Term:
    """One term of a bound: `coef * base^n * n^degree` in the subject length."""

    coef: int
    base: int = 1
    degree: int = 0


@dataclass(frozen=True)
class Sum:
    """Where a bound's terms sit in the certificate's flat term table."""

    first: int = 0
    count: int = 0


@dataclass(frozen=True)
class Region:
    """One source construct, its instruction range, and what it is priced at."""

    kind: str
    parent: int
    lo: int
    hi: int
    cost: Sum = Sum()
    stack: Sum = Sum()
    mem: Sum = Sum()


@dataclass(frozen=True)
class Certificate:
    """What the analyzer will produce and the checker already refuses to guess at.

    Region 0 is the root, so the whole-pattern bounds are its bounds and there
    is no second copy of them to disagree with the tree.
    """

    regions: tuple[Region, ...]
    terms: tuple[Term, ...] = ()
    config: str = "CfgBacktrack"
    complexity: str = "CcNotProvenLinear"


class EngineError(RuntimeError):
    """The engine did something only a bug of ours explains."""


def _frozen(items: list, elem: Type, maximum: int) -> Frozen:
    if len(items) > maximum:
        raise EngineError(f"{len(items)} of {elem} is past the declared maximum {maximum}")
    return Frozen(Seq(elem, maximum, items, len(items)))


def _blob(data: bytes) -> Frozen:
    return _frozen(list(data), U8, CEILING)


def _certificate(cert: Certificate) -> StructValue:
    """A certificate as the TIR values that stand for one.

    The checker's whole job is to distrust what it is handed, so this refuses
    only what would not be a TIR value at all — a count no u32 holds, a table
    longer than its declared maximum. Anything that is well typed and still
    nonsense is exactly what the checker is there to answer for.
    """
    regions = [
        StructValue(
            "Region",
            {
                "kind": _tag(region.kind, "Rk"),
                "parent": _scalar(region.parent, U32),
                "lo": _scalar(region.lo, U32),
                "hi": _scalar(region.hi, U32),
                "cost": _sum(region.cost),
                "stack": _sum(region.stack),
                "mem": _sum(region.mem),
            },
        )
        for region in cert.regions
    ]
    terms = [
        StructValue(
            "Term",
            {
                "coef": _scalar(one.coef, COUNTER),
                "base": _scalar(one.base, U32),
                "degree": _scalar(one.degree, U32),
            },
        )
        for one in cert.terms
    ]
    return StructValue(
        "Cert",
        {
            "config": _tag(cert.config, "Cfg"),
            "complexity": _tag(cert.complexity, "Cc"),
            "regions": _frozen(regions, StructType("Region"), spec.MAX_REGIONS),
            "terms": _frozen(terms, StructType("Term"), spec.MAX_TERMS),
        },
    )


def _sum(one: Sum) -> StructValue:
    return StructValue(
        "Sum", {"first": _scalar(one.first, U32), "count": _scalar(one.count, U32)}
    )


def _scalar(value: object, t: Type) -> int:
    """An integer a TIR value of this type could actually hold."""
    if not _in_range(value, INT_RANGE[t][1]):
        raise EngineError(f"{value!r} is not a {t}")
    assert isinstance(value, int)
    return value


def _tag(variant: str, enum: str) -> Tag:
    """A variant this enum actually declares, since a tag is a name, not a number."""
    if variant not in program().enum_map[enum].variants:
        raise EngineError(f"enum {enum} has no variant {variant!r}")
    return Tag(enum, variant)


def _options(names: Sequence[str], table: dict[str, int], what: str) -> int | None:
    bits = 0
    for name in names:
        if name not in table:
            return None
        bits |= table[name]
    return bits


@dataclass(frozen=True)
class CompiledPattern:
    """What the engine hands back, plus the bits Python needs to read it."""

    re: StructValue
    captures: int
    names: tuple[tuple[bytes, int], ...]


class Engine:
    """The wave 1 engine, one instance per user of it.

    The TIR program is shared and immutable; the interpreter is not, so each
    call gets its own with a fresh step count.
    """

    def __init__(self, limits: Limits | None = None) -> None:
        self.program = program()
        self.limits = limits or Limits()
        self.last_usage: Usage | None = None

    def _interp(self, cost: int = 0) -> Interpreter:
        return Interpreter(self.program, fuel=SETUP_STEPS + STEPS_PER_UNIT * cost)

    # --- compilation ---

    def compile_pattern(
        self,
        pattern: bytes,
        *,
        options: Sequence[str] = (),
        newline: str | None = "LF",
        bsr: str | None = "UNICODE",
    ) -> CompiledPattern | CompileError | Unsupported | TooLarge:
        bits = _options(options, spec.COMPILE_OPTIONS, "a compile option")
        if bits is None:
            return Unsupported(
                spec.E_UNSUPPORTED_OPTION, 0, f"one of {', '.join(options)}"
            )
        nltype = spec.NEWLINE_CONVENTIONS.get(newline or "LF")
        bsrtype = spec.BSR_CONVENTIONS.get(bsr or "UNICODE")
        if nltype is None or bsrtype is None:
            return Unsupported(spec.E_UNSUPPORTED_OPTION, 0, "a newline convention")

        interp = self._interp()
        out = Cell(interp.zero(StructType("Out")))
        interp.call(
            "compile", [_blob(pattern), bits, nltype, bsrtype, out]
        )
        value = out.value
        assert isinstance(value, StructValue)
        err = value.fields["err"]
        assert isinstance(err, int)
        if err == 0:
            re = value.fields["re"]
            assert isinstance(re, StructValue)
            return CompiledPattern(re=re, captures=re.fields["ncap"], names=_names(re))
        offset = value.fields["erroff"]
        assert isinstance(offset, int)
        if err == spec.E_PATTERN_TOO_LARGE:
            return TooLarge()
        if err in spec.OUR_ERRORS:
            return Unsupported(err, offset, spec.OUR_ERRORS[err])
        return CompileError(code=err, offset=offset, message=_message(err))

    def compile(
        self,
        pattern: bytes,
        *,
        options: Sequence[str] = (),
        newline: str | None = "LF",
        bsr: str | None = "UNICODE",
    ):
        """The corpus runner's compile step: identity and group names, or a failure."""
        built = self.compile_pattern(
            pattern, options=options, newline=newline, bsr=bsr
        )
        if isinstance(built, CompiledPattern):
            return Compiled(capture_count=built.captures, names=built.names)
        return built

    # --- matching ---

    def match(
        self,
        pattern: bytes,
        subject: bytes,
        *,
        start: int = 0,
        options: Sequence[str] = (),
        match_options: Sequence[str] = (),
        newline: str | None = "LF",
        bsr: str | None = "UNICODE",
        limits: Limits | None = None,
    ):
        built = self.compile_pattern(
            pattern, options=options, newline=newline, bsr=bsr
        )
        if not isinstance(built, CompiledPattern):
            return built
        return self.match_compiled(
            built,
            subject,
            start=start,
            match_options=match_options,
            limits=limits,
        )

    def match_compiled(
        self,
        built: CompiledPattern,
        subject: bytes,
        *,
        start: int = 0,
        match_options: Sequence[str] = (),
        limits: Limits | None = None,
    ):
        bits = _options(match_options, spec.MATCH_OPTIONS, "a match option")
        if bits is None:
            return Unsupported(
                spec.E_UNSUPPORTED_OPTION, 0, f"one of {', '.join(match_options)}"
            )
        # A start offset past the end of the subject is the engine's own
        # BadInput, decided in TIR; only a value no u32 could hold is refused
        # here, because there is no way to pass one in. The same exact-integer
        # reading as the limits, so a bool or a float never reaches the u32
        # parameter looking like a number.
        if not _in_range(start, 0xFFFFFFFF):
            return BadInput()

        budget = limits or self.limits
        if not _in_range(budget.cost, MAX_COST_LIMIT):
            return BadInput()
        if not _in_range(budget.stack, MAX_STACK_LIMIT):
            return BadInput()
        if not _in_range(budget.memory, MAX_MEMORY_LIMIT):
            return BadInput()
        interp = self._interp(budget.cost)
        ov = Cell(interp.zero(interp.p.func_map["match"].param("ov").type))
        usage = Cell(interp.zero(StructType("Usage")))
        status = interp.call(
            "match",
            [
                built.re,
                _blob(subject),
                start,
                bits,
                budget.cost,
                budget.stack,
                budget.memory,
                ov,
                usage,
            ],
        )
        used = usage.value
        assert isinstance(used, StructValue)
        self.last_usage = Usage(
            cost=used.fields["cost"],
            stack=used.fields["stack"],
            memory=used.fields["mem"],
        )
        if status == spec.NO_MATCH:
            return NoMatch()
        if status == spec.RESOURCE_EXCEEDED:
            return ResourceExceeded()
        if status == spec.BAD_INPUT:
            return BadInput()
        if status != spec.MATCHED:
            raise EngineError(f"the matcher returned {status!r}")
        slots = ov.value
        assert isinstance(slots, Seq)
        return Match(ovector=tuple(_offset(v) for v in slots.items))

    # --- bound certificates ---
    #
    # Nothing produces a certificate yet, so these two take one from the
    # caller. When the analyzer lands, compilation runs the same checker over
    # what it produced before any of it is believed.

    def check_certificate(self, cert: Certificate, code_len: int) -> str:
        """The checker's verdict, named: "CrOk", or the reason it refused."""
        answer = self._interp().call(
            "cert_check", [_certificate(cert), _scalar(code_len, U32)]
        )
        assert isinstance(answer, Tag)
        return answer.variant

    def bound(self, cert: Certificate, kind: str, subject_len: int) -> int | None:
        """A certified bound at that subject length, or None for ExceedsBudget."""
        answer = self._interp().call(
            "cert_bound",
            [_certificate(cert), _tag(kind, "Bk"), _scalar(subject_len, COUNTER)],
        )
        assert isinstance(answer, StructValue)
        return answer.fields["value"] if answer.fields["ok"] else None


def _in_range(value: object, ceiling: int) -> bool:
    """A limit is a whole number a counter can hold, and nothing else."""
    return isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= ceiling


def _offset(value: object) -> int:
    assert isinstance(value, int)
    return -1 if value == spec.UNSET else value


def _names(re: StructValue) -> tuple[tuple[bytes, int], ...]:
    blob = re.fields["names"]
    entries = re.fields["nameents"]
    assert isinstance(blob, Frozen) and isinstance(entries, Frozen)
    text = blob.inner
    table = entries.inner
    assert isinstance(text, Seq) and isinstance(table, Seq)
    out = []
    for entry in table.items:
        assert isinstance(entry, StructValue)
        off = entry.fields["off"]
        length = entry.fields["nlen"]
        assert isinstance(off, int) and isinstance(length, int)
        name = bytes(text.items[off : off + length])
        out.append((name, entry.fields["grp"]))
    return tuple(out)


MESSAGES = {
    spec.E_BACKSLASH_AT_END: "a backslash ends the pattern",
    spec.E_C_AT_END: r"\c ends the pattern",
    spec.E_UNRECOGNIZED_ESCAPE: "that escape has no meaning",
    spec.E_QUANTIFIER_ORDER: "the quantifier's bounds are the wrong way round",
    spec.E_QUANTIFIER_TOO_BIG: "the quantifier's bound is too large",
    spec.E_MISSING_BRACKET: "the character class has no closing bracket",
    spec.E_BAD_CLASS_ESCAPE: "that escape is not allowed in a character class",
    spec.E_CLASS_RANGE_ORDER: "the class range runs backwards",
    spec.E_NOTHING_TO_REPEAT: "there is nothing here for the quantifier to repeat",
    spec.E_UNRECOGNIZED_AFTER_QUERY: "that is not a group this engine knows",
    spec.E_POSIX_OUTSIDE_CLASS: "a POSIX class name only means anything inside a class",
    spec.E_POSIX_COLLATING: "POSIX collating elements are not supported",
    spec.E_MISSING_PAREN: "the group has no closing parenthesis",
    spec.E_NO_SUCH_GROUP: "there is no group with that number",
    spec.E_MISSING_COMMENT_PAREN: "the comment group has no closing parenthesis",
    spec.E_TOO_DEEP: "the groups nest too deeply",
    spec.E_UNMATCHED_PAREN: "this closing parenthesis opens nothing",
    spec.E_ZERO_RELATIVE: "a relative reference of zero points at nothing",
    spec.E_MALFORMED_UCP: r"that \p or \P sequence is malformed",
    spec.E_UNKNOWN_PROPERTY: r"there is no property by that name",
    spec.E_BAD_G_ESCAPE: r"\g wants a braced, angle-bracketed, or quoted name or number",
    spec.E_NUMBER_TOO_BIG: "that group number is too big",
    spec.E_BAD_K_ESCAPE: r"\k wants a braced, angle-bracketed, or quoted name",
    spec.E_NUMBER_TERMINATOR: "the group number has no terminator",
    spec.E_UNKNOWN_POSIX_CLASS: "there is no POSIX class by that name",
    spec.E_CODE_POINT_TOO_BIG: "that code point does not fit in a byte",
    spec.E_NO_SUCH_BACKSLASH: "PCRE has no such backslash escape",
    spec.E_BAD_NAME_TERMINATOR: "the group name has no terminator",
    spec.E_DUPLICATE_NAME: "two groups share that name",
    spec.E_NAME_STARTS_WITH_DIGIT: "a group name cannot start with a digit",
    spec.E_NAME_TOO_LONG: "that group name is too long",
    spec.E_INVALID_CLASS_RANGE: "a class range cannot have a set as an endpoint",
    spec.E_OCTAL_TOO_BIG: "that octal value does not fit in a byte",
    spec.E_MISSING_OCTAL_BRACE: r"\o wants a brace",
    spec.E_NAME_EXPECTED: "the group has no name",
    spec.E_BAD_OCTAL_DIGIT: r"the \o{} escape has no closing brace",
    spec.E_BAD_HEX_DIGIT: r"the \x{} escape has no closing brace",
    spec.E_C_NOT_PRINTABLE: r"\c wants a printable ASCII character",
    spec.E_N_IN_CLASS: r"\N means nothing in a character class",
    spec.E_MISSING_DIGITS: "that escape wants digits",
    spec.E_BAD_HYPHEN: "that hyphen clears nothing",
}


def _message(code: int) -> str:
    return MESSAGES.get(code, f"compile error {code}")
