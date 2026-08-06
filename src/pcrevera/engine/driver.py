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
from dataclasses import dataclass, replace

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
class InternalError:
    """The engine contradicted itself about a pattern it accepted.

    A type of its own rather than one more code inside `Unsupported`, whose
    meaning is the opposite: an unsupported construct is a thing this release
    does not do, and a caller who skips those is right to. This is a bug of
    ours, and a caller who skipped it would be skipping the report. Every sweep
    that treats "the engine declined" as "nothing to compare" therefore has to
    see a different type, or the bug is invisible on exactly the patterns
    nobody wrote down.
    """

    code: int = spec.E_INTERNAL


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
class Poly:
    """A bound: `base^n` times `coefs[0] + coefs[1] * (n+1) + ...`.

    The coefficients are written low power first and may stop early, since a
    bound rarely reaches the top of the range the struct has room for.
    """

    coefs: tuple[int, ...] = ()
    base: int = 1


ZERO = Poly()


def coef(p: Poly, degree: int) -> int:
    """A coefficient the polynomial stopped short of is zero."""
    return p.coefs[degree] if degree < len(p.coefs) else 0


def canonical(base: int, coefs) -> Poly:
    """The one spelling of a bound, so that two of them compare equal.

    A `Poly` stops where its coefficients do, and a bound worth nothing carries
    no growth either. Both readers of a certificate go through here — the one
    that decodes what the engine built and the one the corpus prices with — so
    that a certificate compared against another is compared as a number rather
    than as however it happened to be written down.
    """
    trimmed = tuple(coefs)
    while trimmed and trimmed[-1] == 0:
        trimmed = trimmed[:-1]
    return ZERO if not trimmed else Poly(trimmed, base)


@dataclass(frozen=True)
class Region:
    """One source construct the compiler flattened, and its instruction range.

    The compiled pattern carries these; nothing else does, so a certificate
    cannot come to disagree with the tree it prices.
    """

    kind: str
    parent: int
    lo: int
    hi: int


@dataclass(frozen=True)
class Price:
    """What a certificate claims one entry into a region costs.

    `outs` is how many times control can leave the region going forward, which
    is the ambiguity everything else composes with (BOUNDS.md section 3).
    """

    work: Poly = ZERO
    outs: Poly = ZERO
    stack: Poly = ZERO
    trail: Poly = ZERO


@dataclass(frozen=True)
class Certificate:
    """What the analyzer produces and the checker refuses to guess at.

    One price per region of the compiled pattern, in the same order. Three of
    the whole-pattern bounds are what the accessors report, and they are not
    the root region's numbers: the root is priced per starting position, and a
    call pays for setup, for delivering its answer, and for scratch growth on
    top. The trail is the fourth, the other array a preallocated context
    sizes, and is never an accessor's answer.
    """

    prices: tuple[Price, ...]
    cost: Poly = ZERO
    stack: Poly = ZERO
    trail: Poly = ZERO
    mem: Poly = ZERO
    config: str = "CfgBacktrack"
    complexity: str = "CcNotProvenLinear"


CERT_SLOTS = {
    "CfgBacktrack": ("hascert", "cert"),
    "CfgPike": ("haspikecert", "pikecert"),
}
"""Which Re fields hold each configuration's certificate. A lookup that
raises on a configuration nobody stored, so a typo or a future CfgMemo never
silently reads the backtracking slot."""


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
    longer than its declared maximum, a field the struct does not declare.
    Anything that is well typed and still nonsense is exactly what the checker
    is there to answer for.

    Nothing outside the engine builds a certificate: the analyzer does, in TIR,
    where the types are the guarantee. So a malformed one arriving here really
    is a bug of ours, which is what `EngineError` says.
    """
    # The length first, before converting elements that are about to be thrown
    # away: a table past its declared maximum is refused either way, and
    # building it costs tens of megabytes on the way to the same answer.
    _fits(cert.prices, spec.MAX_REGIONS, "prices")
    prices = [
        _struct(
            "Price",
            {
                "work": _poly(one.work),
                "outs": _poly(one.outs),
                "stack": _poly(one.stack),
                "trail": _poly(one.trail),
            },
        )
        for one in cert.prices
    ]
    return _struct(
        "Cert",
        {
            "config": _tag(cert.config, "Cfg"),
            "complexity": _tag(cert.complexity, "Cc"),
            "cost": _poly(cert.cost),
            "stack": _poly(cert.stack),
            "trail": _poly(cert.trail),
            "mem": _poly(cert.mem),
            "prices": _frozen(prices, StructType("Price"), spec.MAX_REGIONS),
        },
    )


def _regions(regions: Sequence[Region]) -> Frozen:
    """A region table as the TIR values that stand for one.

    Only the corpus builds one of these: the compiler emits the real thing.
    What it is for is the other half of the checker's job — every rule that
    holds the tree to the bytecode needs a tree that does not, and the only way
    to write one down is to put it where the compiler would have.
    """
    _fits(regions, spec.MAX_REGIONS, "regions")
    return _frozen(
        [
            _struct(
                "Region",
                {
                    "kind": _tag(one.kind, "Rk"),
                    "parent": _scalar(one.parent, U32),
                    "lo": _scalar(one.lo, U32),
                    "hi": _scalar(one.hi, U32),
                },
            )
            for one in regions
        ],
        StructType("Region"),
        spec.MAX_REGIONS,
    )


def _poly(one: Poly) -> StructValue:
    _fits(one.coefs, len(spec.DEGREES), "coefficients")
    fields: dict[str, object] = {"base": _scalar(one.base, COUNTER)}
    for degree in spec.DEGREES:
        fields[f"c{degree}"] = _scalar(coef(one, degree), COUNTER)
    return _struct("Poly", fields)


def _struct(name: str, fields: dict[str, object]) -> StructValue:
    """A struct value with every field the declaration names, in its order.

    Naming the fields by hand keeps their types visible, which is worth more
    here than a walk over the declaration would be. What it does not keep is
    honest by itself: a field added to the struct and forgotten here would
    build a value that reads fine until something touches the missing key. So
    the set is compared, and the order comes from the declaration rather than
    from the order this file happens to list them in.
    """
    declared = [f.name for f in program().struct_map[name].fields]
    if set(fields) != set(declared):
        raise EngineError(f"{name} takes {sorted(declared)}, got {sorted(fields)}")
    return StructValue(name, {f: fields[f] for f in declared})


def _fits(items: Sequence, maximum: int, what: str) -> None:
    if len(items) > maximum:
        raise EngineError(f"{len(items)} {what} is past the declared maximum {maximum}")


def _scalar(value: object, t: Type) -> int:
    """An integer a TIR value of this type could actually hold."""
    low, high = INT_RANGE[t]
    if not isinstance(value, int) or isinstance(value, bool) or not low <= value <= high:
        raise EngineError(f"{value!r} is not a {t}")
    return value


def _tag(variant: str, enum: str) -> Tag:
    """A variant this enum actually declares, since a tag is a name, not a number."""
    if variant not in program().enum_map[enum].variants:
        raise EngineError(f"enum {enum} has no variant {variant!r}")
    return Tag(enum, variant)


# --- and the same values read back out ---
#
# A certificate the engine built is a TIR value like any other, so reading one
# is the mirror of writing one. The only thing that is not a field copy is the
# trailing zeros: `Poly` in Python stops where its coefficients do, so that two
# certificates for the same program compare equal whichever side wrote them.


def _read_poly(value: object) -> Poly:
    assert isinstance(value, StructValue)
    return canonical(
        value.fields["base"], [value.fields[f"c{d}"] for d in spec.DEGREES]
    )


def _read_price(value: object) -> Price:
    assert isinstance(value, StructValue)
    return Price(
        **{
            quantity: _read_poly(value.fields[quantity])
            for quantity in ("work", "outs", "stack", "trail")
        }
    )


def _read_cert(value: object) -> Certificate:
    assert isinstance(value, StructValue)
    return Certificate(
        prices=tuple(_read_price(one) for one in items(value.fields["prices"])),
        cost=_read_poly(value.fields["cost"]),
        stack=_read_poly(value.fields["stack"]),
        trail=_read_poly(value.fields["trail"]),
        mem=_read_poly(value.fields["mem"]),
        config=variant_of(value.fields["config"]),
        complexity=variant_of(value.fields["complexity"]),
    )


def items(value: object) -> list:
    """What a sequence holds, whether or not it is frozen."""
    if isinstance(value, Frozen):
        value = value.inner
    assert isinstance(value, Seq)
    return value.items


def variant_of(value: object) -> str:
    """A tag is a name rather than a number, which is what makes it readable."""
    assert isinstance(value, Tag)
    return value.variant


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

    @property
    def certificate(self) -> Certificate | None:
        """The bound certificate compilation produced, or None if it found none.

        Not the public accessor of DESIGN.md section 2.4 — that one answers a
        bound at a subject length and never hands out a certificate at all.
        This is how Python reads the slot, so that the tests and the corpus can
        ask what the analyzer came up with for a program.

        None means the analyzer found no bound of a shape the arithmetic can
        write down. It never means the slot is half filled: compilation writes
        it only after the checker has accepted what is in it.
        """
        if not self.re.fields["hascert"]:
            return None
        return _read_cert(self.re.fields["cert"])

    @property
    def pike_certificate(self) -> Certificate | None:
        """The Pike configuration's certificate, read the same way."""
        if not self.re.fields["haspikecert"]:
            return None
        return _read_cert(self.re.fields["pikecert"])

    def with_regions(self, regions: Sequence[Region]) -> "CompiledPattern":
        """The same pattern carrying a region table nobody compiled.

        Every rule that holds the tree to the bytecode needs a tree that does
        not, and since the compiler is what emits trees, the only way to write
        one down is to put it where the compiler's would have been. Doing that
        to the pattern rather than to a call means every accessor that takes a
        compiled pattern takes a doctored one for free, and the fake is visible
        where it is made.

        The certificate goes with it. It prices the tree the compiler emitted,
        so against another tree it is a claim about nothing, and leaving it
        behind would be leaving something for a reader to trip over.
        """
        return replace(
            self,
            re=_struct(
                "Re",
                {
                    **self.re.fields,
                    "regions": _regions(regions),
                    "hascert": False,
                    "cert": _certificate(Certificate(prices=())),
                },
            ),
        )


@dataclass(frozen=True)
class MatchContext:
    """A preallocated context, as the interpreter holds one.

    The cell is the generated `Ctx` value, and it is the state: every call on
    the context reads and writes through it. The two result stores are the
    context's too, held beside the cell the way every wrapper holds them —
    the ovector the run cores fill and the converted view a match answers
    from, both created with the context and overwritten by each call — so a
    match's answer stays valid exactly until the next call, which is the
    documented lifetime. `memory` is the reservation the context
    materialized — the accessors' worstCaseMemory at the declared length,
    which the corpus holds it to.
    """

    cell: Cell
    ovector: Cell
    view: list[int]
    cost_cap: int
    stack_cap: int
    memory: int

    @property
    def resident(self) -> int:
        """Every byte this context reserved, counted off the stores themselves.

        The arrays in the cell weighed at the IR sizes, plus the ovector the
        run cores fill and the view a match answers through. Nothing here is
        assumed: it is what the object really holds, which is the claim
        BOUNDS.md section 5 makes about the memory bound, and it lives beside
        the object rather than beside any one of the things that ask it, since
        the Python tests and the sweep both do.
        """
        value = self.cell.value
        assert isinstance(value, StructValue)
        total = 0
        for name, esize in WEIGHED:
            array = value.fields[name]
            assert isinstance(array, Seq)
            total += array.cap * esize
        slots = self.ovector.value
        assert isinstance(slots, Seq)
        return total + (slots.cap + len(self.view)) * spec.REG_SIZE


WEIGHED = (
    ("regs", spec.REG_SIZE),
    ("bt", spec.BT_SIZE),
    ("trail", spec.UNDO_SIZE),
    ("clist", spec.TH_SIZE),
    ("nlist", spec.TH_SIZE),
    ("stk", spec.TH_SIZE),
    ("seen", 1),
    ("rc", spec.REG_SIZE),
    ("free", spec.REG_SIZE),
    ("pool", spec.REG_SIZE),
    ("slack", 1),
)
"""What one element of each context array weighs, from BOUNDS.md section 3.

The IR sizes the memory bound is stated in, in one place: a context whose
reservation drifted from the bound cannot agree with a sum taken from here, and
an array added to `Ctx` is a line added here rather than in every runner that
weighs one.
"""


def statused(outcome: object) -> int:
    """The outcome ordinal a driver answer stands for.

    The mapping between the four answer types and the numbers `spec` gives
    them, which every corpus writes down and every runner reads back.
    """
    if isinstance(outcome, Match):
        return spec.MATCHED
    if isinstance(outcome, NoMatch):
        return spec.NO_MATCH
    if isinstance(outcome, ResourceExceeded):
        return spec.RESOURCE_EXCEEDED
    if isinstance(outcome, BadInput):
        return spec.BAD_INPUT
    raise EngineError(f"a call answered {outcome!r}")


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
    ) -> CompiledPattern | CompileError | Unsupported | TooLarge | InternalError:
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
        if err == spec.E_INTERNAL:
            return InternalError()
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
        match_config: int = spec.MC_DEFAULT,
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
            match_config=match_config,
        )

    def match_compiled(
        self,
        built: CompiledPattern,
        subject: bytes,
        *,
        start: int = 0,
        match_options: Sequence[str] = (),
        limits: Limits | None = None,
        match_config: int = spec.MC_DEFAULT,
    ):
        return self._matched(
            "match",
            built,
            subject,
            start=start,
            match_options=match_options,
            limits=limits,
            match_config=match_config,
        )

    # --- the matchers' internal entry points ---
    #
    # Not the public routing: `match_compiled` runs the path compilation
    # selected. These are how the cross-matcher tests of DESIGN.md section 8
    # reach each matcher directly — plain backtracking on a Pike-eligible
    # pattern is a test configuration the public surface never routes, and
    # the Pike VM refuses an ineligible program with its own BadInput.

    def pike_eligible(self, built: CompiledPattern) -> bool:
        """What compilation decided about the Pike VM, off the stored flag."""
        return bool(built.re.fields["pike"])

    def pike_hollow(self, built: CompiledPattern, which: int) -> bool:
        """Can that repetition's body finish an iteration without consuming?

        One of the two halves of eligibility, asked on its own so that the
        migration report of PLAN-POST-M6.md can hold the compiler's pre-check
        to what the emitted program shows rather than to its own reasoning.
        """
        return bool(self._interp().call("pike_hollow", [built.re, which]))

    def pike_match_compiled(self, built, subject: bytes, **kwargs):
        """`match_compiled`, pinned to the Pike VM.

        A pattern compilation did not route here comes back as the
        deterministic BadInput, decided by the generated matcher itself: it
        reads the Rep opcodes as pure-star forks, which is what `pike_ok`
        guarantees they are, and answering an ineligible program would be
        answering it wrongly.
        """
        return self._matched("pike_match", built, subject, **kwargs)

    def bt_match_compiled(self, built, subject: bytes, **kwargs):
        """`match_compiled`, pinned to the backtracking matcher."""
        return self._matched("bt_match", built, subject, **kwargs)

    def _matched(
        self,
        entry: str,
        built: CompiledPattern,
        subject: bytes,
        *,
        start: int = 0,
        match_options: Sequence[str] = (),
        limits: Limits | None = None,
        match_config: int | None = None,
    ):
        """One matcher entry point, run: the public `match` takes the match
        configuration, the two internal ones do not, and everything else about
        the pipeline is identical by construction rather than by copy."""
        bits = _match_bits(match_options)
        if isinstance(bits, Unsupported):
            return bits
        # A start offset past the end of the subject is the engine's own
        # BadInput, decided in TIR; only a value no u32 could hold is refused
        # here, because there is no way to pass one in. The same exact-integer
        # reading as the limits, so a bool or a float never reaches the u32
        # parameter looking like a number. The match configuration is read the
        # same way; which values mean anything is the engine's decision.
        if not _in_range(start, 0xFFFFFFFF):
            return BadInput()
        if match_config is not None and not _in_range(match_config, 0xFFFFFFFF):
            return BadInput()
        budget = limits or self.limits
        if not _representable(budget):
            return BadInput()
        interp = self._interp(budget.cost)
        ov = Cell(interp.zero(interp.p.func_map[entry].param("ov").type))
        usage = Cell(interp.zero(StructType("Usage")))
        status = interp.call(
            entry,
            [
                built.re,
                _blob(subject),
                start,
                bits,
                *([] if match_config is None else [match_config]),
                budget.cost,
                budget.stack,
                budget.memory,
                ov,
                usage,
            ],
        )
        refused = self._finish(entry, status, usage)
        if refused is not None:
            return refused
        slots = ov.value
        assert isinstance(slots, Seq)
        return Match(ovector=tuple(_offset(v) for v in slots.items))

    def _finish(self, entry: str, status: object, usage: Cell):
        """Record what the run used and name every outcome that carries no
        ovector; None is MATCHED, whose answer only the caller can read."""
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
            raise EngineError(f"{entry} returned {status!r}")
        return None

    # --- preallocated contexts ---
    #
    # The generated `ctx_create` and `ctx_match`, run the same way the Go and
    # JavaScript wrappers run them: creation validates, sizes and reserves,
    # matching reuses what creation reserved. The context lives in a `Cell`
    # so its arrays persist across calls, which is the whole point of it.

    def create_context(
        self,
        built: CompiledPattern,
        *,
        max_subject_len: int,
        limits: Limits | None = None,
        match_config: int = spec.MC_DEFAULT,
    ):
        """(status, MatchContext or None): spec.OK and a context, or a refusal.

        The limits are creation's budget and the context's baked ceilings at
        once: the reservation must fit the memory limit, its zeroing must fit
        the cost limit at one unit per IR byte, and later calls may lower the
        cost and stack limits but never raise them.
        """
        if not _in_range(max_subject_len, 0xFFFFFFFF):
            return (spec.BAD_INPUT, None)
        if not _in_range(match_config, 0xFFFFFFFF):
            return (spec.BAD_INPUT, None)
        budget = limits or self.limits
        if not _representable(budget):
            return (spec.BAD_INPUT, None)
        interp = self._interp(budget.cost)
        held = Cell(interp.zero(StructType("Ctx")))
        status = interp.call(
            "ctx_create",
            [
                built.re,
                match_config,
                max_subject_len,
                budget.cost,
                budget.stack,
                budget.memory,
                held,
            ],
        )
        assert isinstance(status, int)
        if status != spec.OK:
            return (status, None)
        value = held.value
        assert isinstance(value, StructValue)
        memcap = value.fields["memcap"]
        assert isinstance(memcap, int)
        # The two result stores, materialized with the context the way every
        # wrapper materializes them: the ovector reserved to its full size,
        # so the run cores' own reserve is a no-op, and the converted view
        # zeroed beside it. The memory bound's setup and deliver terms pay
        # for both, and both are physical from the start.
        novec = 2 * (built.captures + 1)
        slots = interp.zero(interp.p.func_map["ctx_match"].param("ov").type)
        assert isinstance(slots, Seq)
        slots.cap = novec
        return (
            spec.OK,
            MatchContext(
                cell=held,
                ovector=Cell(slots),
                view=[0] * novec,
                cost_cap=budget.cost,
                stack_cap=budget.stack,
                memory=memcap,
            ),
        )

    def context_match(
        self,
        held: "MatchContext",
        subject: bytes,
        *,
        start: int = 0,
        match_options: Sequence[str] = (),
        cost_limit: int | None = None,
        stack_limit: int | None = None,
    ):
        """One call on a context, in the shapes `match_compiled` answers.

        Omitted limits are the baked ceilings; explicit ones may be anything
        representable, and the engine refuses a raise as BadInput.
        """
        bits = _match_bits(match_options)
        if isinstance(bits, Unsupported):
            return bits
        if not _in_range(start, 0xFFFFFFFF):
            return BadInput()
        cost = held.cost_cap if cost_limit is None else cost_limit
        stack = held.stack_cap if stack_limit is None else stack_limit
        if not _in_range(cost, MAX_COST_LIMIT):
            return BadInput()
        if not _in_range(stack, MAX_STACK_LIMIT):
            return BadInput()
        interp = self._interp(cost)
        usage = Cell(interp.zero(StructType("Usage")))
        status = interp.call(
            "ctx_match",
            [held.cell, _blob(subject), start, bits, cost, stack, held.ovector, usage],
        )
        refused = self._finish("ctx_match", status, usage)
        if refused is not None:
            return refused
        slots = held.ovector.value
        assert isinstance(slots, Seq)
        # The answer lands in the context's own view, which is the store the
        # memory bound's deliver term pays for; the tuple handed back is the
        # copy-out, made fresh so a caller may keep it.
        for i, v in enumerate(slots.items):
            held.view[i] = _offset(v)
        return Match(ovector=tuple(held.view))

    # --- bound certificates ---
    #
    # Compilation produces one and stores it, so the production path needs
    # nothing from here: `CompiledPattern.certificate` reads the slot. These
    # are what the corpus and the tests need on top — a verdict on a
    # certificate nobody compiled, a bound off one, a bound off the one a
    # pattern carries, and the reason the analyzer gave for not finding one.

    def analyze(self, built: CompiledPattern) -> tuple[str, Certificate | None]:
        """The analyzer's verdict for this program, named, and what it produced.

        Compilation ran this already and kept the certificate; what it did not
        keep is why there was none, because nothing downstream of a compiled
        pattern has a use for the difference. A corpus does: `ArAmbiguous` and
        `ArOverflow` are the two honest inabilities, and `ArShape` is a bug of
        ours wearing the same clothes.
        """
        interp = self._interp()
        cand = Cell(interp.zero(StructType("Cert")))
        found = variant_of(interp.call("cert_build", [built.re, cand]))
        return found, _read_cert(cand.value) if found == "ArOk" else None

    def _planned(
        self, pattern: bytes, options: Sequence[str], newline: str
    ) -> StructValue:
        """The work area after the dry run, with nothing emitted.

        `plan_lowering` prices the lowered candidate in closed form, so asking
        it on its own costs a walk of the parsed tree however large the
        candidate would be. That is what the cap-adjacent witnesses of
        PLAN-POST-M6.md are found with: the boundary is read off the dry run's
        own report rather than guessed at, and only the two patterns either
        side of it are ever compiled.
        """
        bits = _options(options, spec.COMPILE_OPTIONS, "a compile option")
        assert bits is not None, options
        interp = self._interp()
        work = Cell(interp.zero(StructType("Work")))
        interp.call(
            "parse", [_blob(pattern), bits, spec.NEWLINE_CONVENTIONS[newline], work]
        )
        value = work.value
        assert isinstance(value, StructValue)
        if value.fields["err"]:
            raise ValueError(f"{pattern!r} does not parse: {value.fields['err']}")
        interp.call(
            "plan_lowering", [work, bool(bits & spec.ENDANCHORED)]
        )
        value = work.value
        assert isinstance(value, StructValue)
        return value

    def lowering_plan(
        self,
        pattern: bytes,
        *,
        options: Sequence[str] = (),
        newline: str = "LF",
    ) -> tuple[int, int, bool]:
        """The blockers, the decision and the fit."""
        planned = self._planned(pattern, options, newline)
        return (
            planned.fields["blockers"],
            planned.fields["lowdec"],
            bool(planned.fields["lowfits"]),
        )

    def lowering_fit(
        self,
        pattern: bytes,
        *,
        options: Sequence[str] = (),
        newline: str = "LF",
    ) -> dict[str, int]:
        """The whole vector the dry run predicts, entry by entry.

        The compiler compares this against what it emitted and refuses the
        program when the two differ, which makes it the one number in the
        engine that is checked against itself. So it is also readable from
        outside, where a test can hold the entries it can see — the code, the
        regions, the repetitions and the registers they imply — to the finished
        program rather than to the other half of the same walk.
        """
        planned = self._planned(pattern, options, newline)
        return {
            name: planned.fields[f"fit{name}"]
            for name in ("code", "region", "rep", "regs", "visit", "jobs", "patch")
        }

    def check_shape(self, built: CompiledPattern) -> str:
        """The checker's verdict on the region tree alone, named.

        The half of the checker that takes no certificate, which is the half
        compilation runs whether or not the analyzer found a bound.
        """
        return variant_of(self._interp().call("cert_shape", [built.re]))

    def check_certificate(
        self,
        built: CompiledPattern,
        cert: Certificate,
        config: str = "CfgBacktrack",
    ) -> str:
        """The checker's verdict, named: "CrOk", or the reason it refused.

        The subject is the compiled pattern itself, so what the checker prices
        is the bytecode the matcher would run rather than a description of it.
        """
        return variant_of(
            self._interp().call(
                "cert_check", [built.re, _tag(config, "Cfg"), _certificate(cert)]
            )
        )

    def bound(self, cert: Certificate, kind: str, subject_len: int) -> int | None:
        """A certified bound at that subject length, or None for ExceedsBudget."""
        return self._evaluate(_certificate(cert), kind, subject_len)

    def bound_of(
        self,
        built: CompiledPattern,
        kind: str,
        subject_len: int,
        config: str = "CfgBacktrack",
    ) -> int | None:
        """The same, off a certificate the compiled pattern carries.

        Which is what the Go and JavaScript runners ask, so this is how Python
        asks the same question: `bound` takes a certificate that has been out
        of the engine and back in, and a round trip is not what the other two
        are testing. None here is a pattern with no certificate for that
        configuration, which is the ExceedsBudget the accessors of DESIGN.md
        section 2.4 report for one.
        """
        flag, slot = CERT_SLOTS[config]
        if not built.re.fields[flag]:
            return None
        return self._evaluate(built.re.fields[slot], kind, subject_len)

    def selected_bound(
        self, built: CompiledPattern, kind: str, subject_len: int
    ) -> int | None:
        """The bound of the path compilation selected, which is the public one."""
        config = "CfgPike" if self.pike_eligible(built) else "CfgBacktrack"
        return self.bound_of(built, kind, subject_len, config)

    def _evaluate(self, cert: object, kind: str, subject_len: int) -> int | None:
        answer = self._interp().call(
            "cert_bound", [cert, _tag(kind, "Bk"), _scalar(subject_len, COUNTER)]
        )
        assert isinstance(answer, StructValue)
        return answer.fields["value"] if answer.fields["ok"] else None

    # --- the public analysis accessors ---
    #
    # The four questions of DESIGN.md section 2.4, answered by the generated
    # `re_class`, `re_cost`, `re_stack` and `re_mem` — the same functions the
    # Go and JavaScript wrappers call, so the three languages share one
    # implementation of the contract rather than three readings of it. Each
    # returns the raw (status, value) pair: the corpus pins those numbers, and
    # a language-shaped surface on top of them is the wrappers' business.

    def complexity_class(self, built: CompiledPattern) -> tuple[int, int]:
        """(status, class ordinal), the class being spec.CLASS_*.

        No configuration argument, because the class is fixed at compilation;
        the status is spec.EXCEEDS_BUDGET when no accepted certificate exists.
        """
        return _answer(self._interp().call("re_class", [built.re]))

    def worst_case(
        self,
        built: CompiledPattern,
        kind: str,
        subject_len: object,
        match_config: object = spec.MC_DEFAULT,
    ) -> tuple[int, int]:
        """(status, bound) for kind "cost", "stack" or "mem".

        Only what no counter or u32 could hold is refused here — a negative, a
        fraction, a bool, a length past the saturation point. Everything
        representable goes to the generated function, whose refusals are the
        contract: a length past MAX_LENGTH and a configuration that is not the
        default are its BadInput, absence and saturation its ExceedsBudget.
        """
        if not _in_range(subject_len, CAP):
            return (spec.BAD_INPUT, 0)
        if not _in_range(match_config, 0xFFFFFFFF):
            return (spec.BAD_INPUT, 0)
        entry = {"cost": "re_cost", "stack": "re_stack", "mem": "re_mem"}[kind]
        return _answer(
            self._interp().call(entry, [built.re, match_config, subject_len])
        )


def _answer(value: object) -> tuple[int, int]:
    assert isinstance(value, StructValue)
    status = value.fields["status"]
    held = value.fields["value"]
    assert isinstance(status, int) and isinstance(held, int)
    return (status, held)


def _in_range(value: object, ceiling: int) -> bool:
    """A limit is a whole number a counter can hold, and nothing else."""
    return isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= ceiling


def _representable(budget: Limits) -> bool:
    """Whether all three limits fit the engine's parameters, one rule for
    every entry point that takes a budget."""
    return (
        _in_range(budget.cost, MAX_COST_LIMIT)
        and _in_range(budget.stack, MAX_STACK_LIMIT)
        and _in_range(budget.memory, MAX_MEMORY_LIMIT)
    )


def _match_bits(match_options: Sequence[str]):
    """The option bits, or the Unsupported an unknown name earns."""
    bits = _options(match_options, spec.MATCH_OPTIONS, "a match option")
    if bits is None:
        return Unsupported(
            spec.E_UNSUPPORTED_OPTION, 0, f"one of {', '.join(match_options)}"
        )
    return bits


def _offset(value: object) -> int:
    assert isinstance(value, int)
    return -1 if value == spec.UNSET else value


def _names(re: StructValue) -> tuple[tuple[bytes, int], ...]:
    text = items(re.fields["names"])
    out = []
    for entry in items(re.fields["nameents"]):
        assert isinstance(entry, StructValue)
        off = entry.fields["off"]
        length = entry.fields["nlen"]
        assert isinstance(off, int) and isinstance(length, int)
        out.append((bytes(text[off : off + length]), entry.fields["grp"]))
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
