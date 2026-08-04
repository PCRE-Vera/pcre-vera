"""What one sweep case is put through, and what comes out of it.

DESIGN.md section 8 asks three independent things of a generated case, and this
is all three in one pass, because they want the same compiled pattern and the
same runs.

The semantic check is the differential one: exactly what pcre2 says, down to
the compile error's offset and every ovector entry. The cross-matcher check is
the agreement corollary of section 6 made empirical — on a Pike-eligible
program both matchers are run through the internal entry points, each under its
own analyzer's bounds, and where the backtracking analyzer has no finite
certificate the pair is counted apart rather than folded in with the
agreements. The resource check is section 5 held to the metal: the observed
cost, stack and memory must fit the certificate — each matcher's own — the
three limits are re-run at the observed value and one below on both of them,
and a preallocated context is created at exactly the reservation and one byte
under it, replays every trial, and answers what the plain call answered.

What comes out is one record per case — every value all four implementations
have to agree on — plus the findings, which are failures and only failures, and
the coverage counts. A decline is not a finding: an unsupported construct, a
pattern past a documented limit and a run over a capped budget are outcomes
pcre2 has no opinion about, which is the oracle policy of section 1. Our own
internal error is not a decline, and neither is a checker that refuses a
certificate its own analyzer produced.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field, replace
from typing import Any

from ..engine import spec
from ..engine.driver import (
    BadInput,
    Compiled,
    CompileError,
    CompiledPattern,
    Engine,
    EngineError,
    InternalError,
    Limits,
    Match,
    MatchContext,
    NoMatch,
    ResourceExceeded,
    TooLarge,
    Unsupported,
    items,
    statused,
    variant_of,
)
from ..tir.interp import StructValue
from . import manifest
from .population import Case, Trial

DECLINED = (Unsupported, TooLarge)

BOUNDS = (("cost", "cost", "BkCost"), ("stack", "stack", "BkStack"), ("mem", "memory", "BkMem"))
"""The three bounds, each with the `Limits` field it is the limit for and the
`Bk` variant the engine asks for it by. One tuple rather than three tables
keyed by the same three names: the memory one is spelled differently on every
side, and that is the whole of the mapping."""

KINDS = tuple(kind for kind, _, _ in BOUNDS)

LIMIT_FIELDS = {kind: field_name for kind, field_name, _ in BOUNDS}

BOUND_TAGS = {kind: tag for kind, _, tag in BOUNDS}

CHECKS = (
    "oracle",
    "cross-backend",
    "certificate",
    "bound",
    "edge",
    "cross-matcher",
    "cross-matcher-capped",
    "cross-matcher-unpriced",
    "ineligible",
    "context",
    "context-edge",
)
"""Every kind of check a case can be put through, named where the counting
happens rather than where the gate reads it. `count` refuses a name that is
not here, so a check added without a name is a failure rather than a counter
nobody gates."""

DEFAULT_EDGES = 6
"""How many distinct observed usages of one case get the edge treatment.

Every trial's usage is compared against the bound, which is free. What is
capped here is the re-running, which costs six matches each. A cap rather than
a sample, so that a replay edges exactly the same trials, and one that is
counted in the coverage report rather than left to be inferred.
"""

@dataclass(frozen=True)
class Finding:
    """One failure, in the class that says what kind of failure it is.

    Everything here is fatal. A decline is counted somewhere else, and so are
    the honestly unpriced cross-matcher pairs, because a sweep that reported
    those as findings would be reporting its own documented policy as a bug.
    """

    kind: str
    index: int
    detail: str
    trial: int | None = None

    def __str__(self) -> str:
        where = f"case {self.index}" + ("" if self.trial is None else f", trial {self.trial}")
        return f"[{self.kind}] {where}: {self.detail}"

    def as_json(self) -> dict[str, Any]:
        return {"kind": self.kind, "index": self.index, "trial": self.trial, "detail": self.detail}


@dataclass
class Coverage:
    """What a sweep touched, counted rather than assumed.

    The completion gate of DESIGN.md section 8 is about coverage rather than
    about the raw number of cases, so these are the numbers a campaign is read
    by: which opcodes and region kinds were compiled at all, which matcher was
    selected, how many patterns carried a certificate and how many were
    honestly unpriced, which outcomes came back, which option families and
    conventions were exercised, and how many of each kind of check ran.
    """

    cases: Counter = field(default_factory=Counter)
    families: Counter = field(default_factory=Counter)
    outcomes: Counter = field(default_factory=Counter)
    opcodes: Counter = field(default_factory=Counter)
    regions: Counter = field(default_factory=Counter)
    selection: Counter = field(default_factory=Counter)
    certified: Counter = field(default_factory=Counter)
    options: Counter = field(default_factory=Counter)
    conventions: Counter = field(default_factory=Counter)
    checks: Counter = field(default_factory=Counter)

    def merge(self, other: "Coverage") -> None:
        for name in vars(self):
            getattr(self, name).update(getattr(other, name))

    def as_json(self) -> dict[str, dict[str, int]]:
        return {name: dict(sorted(getattr(self, name).items())) for name in vars(self)}

    @classmethod
    def of(cls, counted: dict[str, dict[str, int]]) -> "Coverage":
        """The same thing read back, for a report that has been written down.

        The inverse of `as_json` belongs beside it: a group renamed here would
        otherwise fail somewhere else entirely, with an AttributeError from a
        module that has no idea what a coverage group is.
        """
        held = cls()
        for group, names in counted.items():
            if not hasattr(held, group):
                raise EngineError(f"{group!r} is not a coverage group")
            getattr(held, group).update(names)
        return held


@dataclass(frozen=True)
class Outcome:
    """One case, run: what to replay, what went wrong, and what it covered."""

    record: dict[str, Any] | None
    findings: tuple[Finding, ...]
    coverage: Coverage


def agrees(ours: object, theirs: object) -> bool:
    """Whether our answer is pcre2's answer, field by field.

    Nothing collapses: a match is the same match only if every ovector entry
    is, a compile error is the same error only if the offset is too, and a
    compiled pattern is the same pattern only if the capture count and the
    group names are. An outcome pcre2 gave that we have no form for is a
    disagreement, never a shrug. The dispatch is on pcre2's answer because it
    is the one being agreed with; ours may be a type it has no notion of.
    """
    if isinstance(theirs, Match):
        return isinstance(ours, Match) and ours.ovector == theirs.ovector
    if isinstance(theirs, NoMatch):
        return isinstance(ours, NoMatch)
    if isinstance(theirs, CompileError):
        return isinstance(ours, CompileError) and (ours.code, ours.offset) == (
            theirs.code,
            theirs.offset,
        )
    if isinstance(theirs, Compiled):
        return (
            isinstance(ours, Compiled)
            and ours.capture_count == theirs.capture_count
            and tuple(sorted(ours.names)) == tuple(sorted(theirs.names))
        )
    return False


ASKED = frozenset({"seed", "index", "family", "pattern", "flags", "newline", "bsr", "maxlen"})
"""The fields of a record that say what was asked rather than what came back.
A trial's three are `manifest.encode_trial`'s, since that is what it writes."""


def _leaves(value: object) -> int:
    """How many values are in there, however deeply.

    A value is anything that is not a list or an object: a number, but also the
    name of a compile outcome and the flag that says a trial carries the limit
    edges, both of which a runner has to reproduce like any other.
    """
    if isinstance(value, dict):
        return sum(_leaves(one) for one in value.values())
    if isinstance(value, list):
        return sum(_leaves(one) for one in value)
    return 1


def facts(record: dict[str, Any]) -> int:
    """How many recorded values another implementation has to reproduce.

    The cross-backend count of DESIGN.md section 8's coverage list. A record is
    replayed rather than recomputed, so what a Go or JavaScript runner is held
    to is exactly the values in it — every one of them, which is why this
    counts the record's own leaves rather than modelling its shape. A field
    added to a trial or to the context is counted the day it appears; a hand
    written sum would go on reporting the old number.

    What is not counted is the half of the record that says what was asked.
    Nobody reproduces a subject.
    """
    asked = ASKED | set(manifest.encode_trial(Trial(b"", (), 0)))
    return sum(
        _leaves(value)
        for key, value in _flattened(record)
        if key not in asked
    )


def _flattened(record: dict[str, Any]):
    """Every (key, value) of the record, with each trial's own pairs inline."""
    for key, value in record.items():
        if key != "trials":
            yield key, value
            continue
        for trial in value:
            yield from trial.items()


def named(status: int) -> str:
    return {
        spec.MATCHED: "match",
        spec.NO_MATCH: "nomatch",
        spec.RESOURCE_EXCEEDED: "resource",
        spec.BAD_INPUT: "badinput",
    }[status]


def limits_for(bound: dict[str, int | None], budget: dict[str, int]) -> Limits:
    """What to run at: the certificate's number, never more than the budget.

    A bound the certificate has no answer for leaves the budget, and so does
    one so large that no sweep could wait for it. Both are capped runs, which
    is why `sufficient` is a separate question from this one.
    """
    picked = {}
    for kind, field_name in LIMIT_FIELDS.items():
        ceiling = budget[field_name]
        claimed = bound[kind]
        picked[field_name] = ceiling if claimed is None else min(claimed, ceiling)
    return Limits(**picked)


def sufficient(bound: dict[str, int | None], budget: dict[str, int]) -> bool:
    """Whether those limits really are the certificate's own, uncapped.

    The premise of the section 6 agreement corollary, and the reason a capped
    run's ResourceExceeded is a decline rather than a disagreement.
    """
    return all(
        bound[kind] is not None and bound[kind] <= budget[field_name]
        for kind, field_name in LIMIT_FIELDS.items()
    )


def _usage(engine: Engine) -> dict[str, int]:
    used = engine.last_usage
    assert used is not None
    return {"cost": used.cost, "stack": used.stack, "mem": used.memory}


SELECTED = "selected"
"""The configuration the accessors answer for, which is the one compilation
picked. Named rather than spelled `None`, because it sits beside `CfgBacktrack`
in the same lookups and the two are different questions."""


def _accessor(engine: Engine, built: CompiledPattern, kind: str, n: int) -> int | None:
    """One public accessor, as a number or as the ExceedsBudget refusal."""
    status, value = engine.worst_case(built, kind, n)
    if status == spec.EXCEEDS_BUDGET:
        return None
    if status != spec.OK:
        raise EngineError(f"the {kind} accessor answered status {status} at n={n}")
    return value


class Bounds:
    """The certified bounds of one compiled pattern, asked once per length.

    A bound is a function of the configuration, the kind and the subject
    length, and every one of them is an interpreter call — the slowest thing
    the sweep does. A case's subjects repeat their lengths heavily (four in
    five, at the campaign's thirty-two), and the context asks again at the
    declared maximum, which is always one of them. Remembering the answer is
    the same answer, arrived at once.
    """

    def __init__(self, engine: Engine, built: CompiledPattern) -> None:
        self.engine = engine
        self.built = built
        self.held: dict[tuple[str, int], dict[str, int | None]] = {}

    def at(self, n: int, config: str = SELECTED) -> dict[str, int | None]:
        found = self.held.get((config, n))
        if found is None:
            found = self.held[(config, n)] = (
                {kind: _accessor(self.engine, self.built, kind, n) for kind in KINDS}
                if config == SELECTED
                else {
                    kind: self.engine.bound_of(self.built, BOUND_TAGS[kind], n, config)
                    for kind in KINDS
                }
            )
        return found


def _tally(source: object, field_name: str, kind_of) -> Counter:
    out: Counter = Counter()
    for one in items(source):
        assert isinstance(one, StructValue)
        out[kind_of(one.fields[field_name])] += 1
    return out


class _Run:
    """One case being run: the record it fills in, and what it found.

    A small object rather than one long function with a dozen accumulators.
    The steps read in the order DESIGN.md section 8 lists them, and each of
    them appends to the same three places.
    """

    def __init__(
        self,
        engine: Engine,
        case: Case,
        budget: dict[str, int],
        oracle: object | None,
        edges: int,
    ) -> None:
        self.engine = engine
        self.case = case
        self.budget = budget
        self.oracle = oracle
        self.edges = edges
        self.findings: list[Finding] = []
        self.coverage = Coverage()
        self.edged: set[tuple[int, int, int]] = set()
        self.bounds: Bounds | None = None

    def fail(self, kind: str, detail: str, trial: int | None = None) -> None:
        self.findings.append(Finding(kind, self.case.index, detail, trial))

    def count(self, group: str, name: str) -> None:
        if group == "checks" and name not in CHECKS:
            raise EngineError(f"{name!r} is not a kind of check this sweep names")
        getattr(self.coverage, group)[name] += 1

    def run(self) -> Outcome:
        case = self.case
        self.count("families", case.family)
        self.count("conventions", f"{case.newline}/{case.bsr}")
        self.count("options", "+".join(case.options) or "none")
        built = self.engine.compile_pattern(
            case.pattern, options=case.options, newline=case.newline, bsr=case.bsr
        )
        if isinstance(built, InternalError):
            self.count("cases", "internal")
            self.fail("internal", "compilation reported an internal error")
            return self.done(None)
        if isinstance(built, DECLINED):
            # A decline is pcre2's business to have no opinion about, not the
            # other backends'. They compile the same pattern and have to refuse
            # it with the same code at the same offset, so it goes in the
            # record like any other outcome and only the oracle comparison is
            # skipped. Leaving it out would be leaving thirty-one cases of a
            # campaign untested in two of the four implementations.
            self.count("cases", "declined")
            self.count("outcomes", "declined")
            refusal: dict[str, Any] = {"kind": "declined", "code": built.code}
            if isinstance(built, Unsupported):
                # A documented limit has no offset in its contract; an
                # unsupported construct is refused at the byte that asked.
                refusal["offset"] = built.offset
            return self.done({**manifest.encode(case), "compile": refusal, "trials": []})
        if isinstance(built, CompileError):
            self.count("cases", "syntax")
            self.count("outcomes", "syntax")
            self.compare_compile(built)
            return self.done(
                {
                    **manifest.encode(case),
                    "compile": {
                        "kind": "compileError",
                        "code": built.code,
                        "offset": built.offset,
                    },
                    "trials": [],
                }
            )

        self.count("cases", "compiled")
        self.count("outcomes", "compiled")
        self.compare_compile(Compiled(capture_count=built.captures, names=built.names))
        self.coverage.opcodes.update(
            _tally(built.re.fields["code"], "op", variant_of)
        )
        self.coverage.regions.update(
            _tally(built.re.fields["regions"], "kind", variant_of)
        )
        return self.done(self.program(built))

    def done(self, record: dict[str, Any] | None) -> Outcome:
        if record is not None:
            self.coverage.checks["cross-backend"] += facts(record)
        return Outcome(record, tuple(self.findings), self.coverage)

    def compare_compile(self, ours: object) -> None:
        if self.oracle is None:
            return
        theirs = self.oracle.compile(
            self.case.pattern,
            options=self.case.options,
            newline=self.case.newline,
            bsr=self.case.bsr,
        )
        self.count("checks", "oracle")
        if not agrees(ours, theirs):
            self.fail("compile", f"ours {ours!r}, pcre2 {theirs!r}")

    def program(self, built: CompiledPattern) -> dict[str, Any]:
        """Everything a compiled pattern is asked, in one record."""
        self.bounds = Bounds(self.engine, built)
        pike = self.engine.pike_eligible(built)
        self.count("selection", "pike" if pike else "backtrack")
        certs = {
            "backtrack": built.certificate is not None,
            "pike": built.pike_certificate is not None,
        }
        for config, held in certs.items():
            self.count("certified", f"{config}:{'certified' if held else 'unpriced'}")
        self.believes(built, certs)

        status, ordinal = self.engine.complexity_class(built)
        if status not in (spec.OK, spec.EXCEEDS_BUDGET):
            self.fail("accessor", f"the class accessor answered status {status}")
        if not pike:
            self.refuses_ineligible(built)
        trials = [self.trial(built, at, one) for at, one in enumerate(self.case.trials)]
        return {
            **manifest.encode(self.case),
            "compile": {
                "kind": "compiled",
                "captures": built.captures,
                "names": {name.hex(): number for name, number in built.names},
            },
            "pike": pike,
            "cert": certs,
            "class": ordinal if status == spec.OK else None,
            "trials": trials,
            "context": self.context(built, trials),
        }

    def believes(self, built: CompiledPattern, certs: dict[str, bool]) -> None:
        """The checker still accepts what the analyzer produced.

        Compilation installs a certificate only after the checker has taken it,
        so a slot holding one the checker now refuses is the two halves of
        DESIGN.md section 5 disagreeing about the same program — a bug of ours,
        and fatal. The analyzer's shape verdict is read the same way: it says
        the tree the compiler emitted is not one the rules can walk, which no
        pattern should ever produce.
        """
        found, produced = self.engine.analyze(built)
        if found == "ArShape":
            self.fail("internal", "the analyzer refused the compiler's own region tree")
        # What compilation kept has to be what the analyzer found, and a
        # pattern the analyzer found nothing for has to carry nothing. The gap
        # in between — the analyzer produced a certificate and the slot is
        # empty — is the checker having refused it, which is the two halves
        # contradicting each other rather than a pattern nobody can price.
        if found == "ArOk" and produced != built.certificate:
            self.fail(
                "internal",
                "compilation kept a backtracking certificate the analyzer did not "
                f"produce: {built.certificate!r} against {produced!r}",
            )
        if found != "ArOk" and built.certificate is not None:
            self.fail(
                "internal",
                f"the analyzer answered {found} and compilation kept a certificate",
            )
        shape = self.engine.check_shape(built)
        if shape != "CrOk":
            self.fail("internal", f"the checker refuses the compiled shape: {shape}")
        for config, slot in (("CfgBacktrack", "backtrack"), ("CfgPike", "pike")):
            if not certs[slot]:
                continue
            cert = built.certificate if slot == "backtrack" else built.pike_certificate
            assert cert is not None
            verdict = self.engine.check_certificate(built, cert, config)
            self.count("checks", "certificate")
            if verdict != "CrOk":
                self.fail(
                    "internal",
                    f"the checker answers {verdict} for the {config} certificate "
                    "compilation installed",
                )

    def refuses_ineligible(self, built: CompiledPattern) -> None:
        """The Pike VM says no to a program compilation did not route to it.

        There is no cross-matcher pair to compare on an ineligible pattern, and
        the refusal is what is worth pinning instead: a matcher that answered
        would be answering a program whose Rep opcodes it reads as forks they
        are not.
        """
        got = self.engine.pike_match_compiled(built, b"", limits=Limits(**self.budget))
        self.count("checks", "ineligible")
        if not isinstance(got, BadInput):
            self.fail(
                "cross-matcher", f"the Pike VM answered {got!r} for an ineligible program"
            )

    def trial(self, built: CompiledPattern, at: int, one: Trial) -> dict[str, Any]:
        bound = self.bounds.at(len(one.subject))
        limits = limits_for(bound, self.budget)
        enough = sufficient(bound, self.budget)
        got = self.call(built, one, limits)
        used = _usage(self.engine)
        status = statused(got)
        self.count("outcomes", named(status))
        row: dict[str, Any] = {
            **manifest.encode_trial(one),
            "bound": bound,
            "outcome": status,
            "usage": used,
        }
        if isinstance(got, Match):
            row["ovector"] = list(got.ovector)

        if status == spec.RESOURCE_EXCEEDED:
            if enough:
                self.fail(
                    "bound",
                    f"a run under the certificate's own limits {limits} was refused",
                    at,
                )
            else:
                self.count("outcomes", "capped")
        else:
            self.compare_match(one, got, at)
            self.fits(bound, used, at)
            if self.edge_wanted(used):
                row["edges"] = True
                self.edge(built, one, limits, used, got, at)
        if self.engine.pike_eligible(built):
            row["cross"] = self.cross(built, one, got, at, row.get("edges", False))
        return row

    def call(
        self, built: CompiledPattern, one: Trial, limits: Limits, matcher: str = "match"
    ):
        """One call, on the selected path or on the backtracking one.

        The two entry points take the same arguments and mean the same thing,
        so everything above works on either: the resource checks of DESIGN.md
        section 8 are asked of both matchers, and asking them twice through one
        function is what keeps the two askings identical.
        """
        entry = (
            self.engine.match_compiled
            if matcher == "match"
            else self.engine.bt_match_compiled
        )
        return entry(
            built, one.subject, start=one.start, match_options=one.match_options, limits=limits
        )

    def compare_match(self, one: Trial, got: object, at: int) -> None:
        if self.oracle is None:
            return
        theirs = self.oracle.match(
            self.case.pattern,
            one.subject,
            start=one.start,
            options=self.case.options,
            match_options=one.match_options,
            newline=self.case.newline,
            bsr=self.case.bsr,
        )
        self.count("checks", "oracle")
        if not agrees(got, theirs):
            self.fail("match", f"ours {got!r}, pcre2 {theirs!r}", at)

    def fits(self, bound: dict[str, int | None], used: dict[str, int], at: int) -> None:
        """The observed numbers fit the certificate, which is the whole claim."""
        for kind in KINDS:
            claimed = bound[kind]
            if claimed is None:
                continue
            self.count("checks", "bound")
            if used[kind] > claimed:
                self.fail("bound", f"{kind} used {used[kind]}, certified {claimed}", at)

    def edge_wanted(self, used: dict[str, int]) -> bool:
        """Whether this usage is one the edges have not been run at yet.

        Six more matches is what the edges cost, so they run once per distinct
        observed usage and no more than `edges` times per case. Both limits are
        deterministic, so every replay edges exactly the same trials.
        """
        key = (used["cost"], used["stack"], used["mem"])
        if key in self.edged or len(self.edged) >= self.edges:
            return False
        self.edged.add(key)
        return True

    def edge(
        self,
        built: CompiledPattern,
        one: Trial,
        limits: Limits,
        used: dict[str, int],
        got: object,
        at: int,
        matcher: str = "match",
    ) -> None:
        """Each limit at the observed value and one below it.

        The deterministic budget boundary of DESIGN.md section 8: at the
        observed value the run gives exactly the answer it just gave, and one
        unit below it is refused. A dimension whose observed value is zero has
        no "one below" to ask about, and its zero limit has already run. The
        same treatment goes to both matchers, since each meters its own work
        and enforces its own limits.
        """
        for kind, field_name in LIMIT_FIELDS.items():
            again = self.call(
                built, one, replace(limits, **{field_name: used[kind]}), matcher
            )
            self.count("checks", "edge")
            if again != got:
                self.fail(
                    "edge",
                    f"at the observed {kind} limit {used[kind]} the {matcher} run "
                    f"answered {again!r} rather than {got!r}",
                    at,
                )
            if used[kind] == 0:
                continue
            refused = self.call(
                built, one, replace(limits, **{field_name: used[kind] - 1}), matcher
            )
            self.count("checks", "edge")
            if not isinstance(refused, ResourceExceeded):
                self.fail(
                    "edge",
                    f"one below the observed {kind} limit {used[kind]} the {matcher} "
                    f"run answered {refused!r} rather than being refused",
                    at,
                )

    def cross(
        self, built: CompiledPattern, one: Trial, got: object, at: int, edged: bool
    ) -> dict[str, Any]:
        """The other matcher on the same trial, under its own analyzer's bounds.

        The selected path on an eligible program is the Pike VM, so what this
        adds is the backtracking run. Where the backtracking analyzer has no
        finite certificate there are no sufficient bounds to run it under, and
        the pair is counted apart: a refusal there says nothing about
        agreement. An answer is still compared, because a real disagreement is
        a bug whatever the budget was.

        The backtracking bound goes into the record beside the answer. Only the
        selected path's bounds are public, so a backend whose backtracking
        analyzer drifted would otherwise be caught only where the drift changed
        an outcome — which, under limits both the old and the new bound allow,
        it would not.
        """
        bound = self.bounds.at(len(one.subject), "CfgBacktrack")
        enough = sufficient(bound, self.budget)
        limits = limits_for(bound, self.budget)
        again = self.call(built, one, limits, "bt_match")
        used = _usage(self.engine)
        row: dict[str, Any] = {"bound": bound, "outcome": statused(again), "usage": used}
        if isinstance(again, Match):
            row["ovector"] = list(again.ovector)
        if isinstance(again, ResourceExceeded):
            if enough:
                self.fail(
                    "bound",
                    f"a backtracking run under its own limits {limits} was refused",
                    at,
                )
            else:
                self.count("checks", "cross-matcher-unpriced")
            return row
        self.fits(bound, used, at)
        if edged:
            row["edges"] = True
            self.edge(built, one, limits, used, again, at, "bt_match")
        self.count("checks", "cross-matcher" if enough else "cross-matcher-capped")
        if again != got:
            self.fail(
                "cross-matcher",
                f"the Pike VM answers {got!r}, the backtracking matcher {again!r}",
                at,
            )
        return row

    def context(self, built: CompiledPattern, trials: list[dict[str, Any]]) -> dict[str, Any]:
        """The preallocated context of DESIGN.md section 2.4, on this case.

        Creation at the reservation and one byte under it, the reservation
        against the memory accessor and against the arrays it really holds,
        every trial replayed on one context, and the per-call cost and stack
        edges. A pattern with no bound has no reservation to make, and the
        ExceedsBudget that comes back is the whole record.
        """
        status, held = self.engine.create_context(
            built, max_subject_len=self.case.maxlen, limits=self.creation_limits()
        )
        self.count("checks", "context")
        if status != spec.OK:
            self.count("outcomes", f"context-{status}")
            return {"status": status}
        assert held is not None
        answered = self.bounds.at(self.case.maxlen)["mem"]
        if answered != held.memory:
            self.fail(
                "context", f"the context reserves {held.memory}, the accessor says {answered}"
            )
        held_bytes = held.resident
        if held_bytes != held.memory:
            self.fail(
                "context",
                f"the context holds {held_bytes} bytes, having reserved {held.memory}",
            )
        self.count("checks", "context")
        self.creation_edge(built, held.memory)
        calls = [
            self.context_call(held, at, one, row)
            for at, (one, row) in enumerate(zip(self.case.trials, trials))
        ]
        out: dict[str, Any] = {"status": status, "memcap": held.memory, "calls": calls}
        picked = self.call_edge(held, trials)
        if picked is not None:
            out["edges"] = picked
        return out

    def creation_limits(self) -> Limits:
        """What creating a context is allowed.

        The reservation is what is being bounded, so the memory limit is the
        sweep's own. Creation charges one cost unit per IR byte it zeroes, so a
        cost ceiling equal to the memory one can never be the limit that binds:
        a reservation the memory limit would allow is one the cost limit
        allows too, and the refusal a sweep records is always about the size of
        the reservation. That ceiling is also the highest a later call may ask
        for, and every call here passes its own limits, so it only ever caps.
        """
        return Limits(
            cost=self.budget["memory"],
            stack=self.budget["stack"],
            memory=self.budget["memory"],
        )

    def creation_edge(self, built: CompiledPattern, memcap: int) -> None:
        """Creation at exactly the reservation, and one byte below it."""
        for memory, want in ((memcap, spec.OK), (memcap - 1, spec.RESOURCE_EXCEEDED)):
            if memory < 0:
                continue
            status, _ = self.engine.create_context(
                built,
                max_subject_len=self.case.maxlen,
                limits=replace(self.creation_limits(), memory=memory),
            )
            self.count("checks", "context-edge")
            if status != want:
                self.fail(
                    "context",
                    f"creation at a memory limit of {memory} answered {status}, wanted {want}",
                )

    def context_call(
        self, held: MatchContext, at: int, one: Trial, row: dict[str, Any]
    ) -> dict[str, Any]:
        got = self.engine.context_match(
            held, one.subject, start=one.start, match_options=one.match_options
        )
        used = _usage(self.engine)
        self.count("checks", "context")
        # A call the context accepted reports the reservation, since that is
        # what is resident for its whole life whatever the subject was. A call
        # it refused as BadInput — a subject past the declared maximum, a limit
        # raised above a baked ceiling — never began, and reports nothing.
        wanted = 0 if statused(got) == spec.BAD_INPUT else held.memory
        if used["mem"] != wanted:
            self.fail(
                "context",
                f"a call reports {used['mem']} bytes against a {held.memory} byte "
                f"reservation, wanting {wanted}",
                at,
            )
        # A subject longer than the declared maximum is a request the context
        # was never sized for, and refusing it is the contract rather than a
        # disagreement with the plain call that answered it.
        if len(one.subject) > self.case.maxlen:
            if statused(got) != spec.BAD_INPUT:
                self.fail(
                    "context",
                    f"a subject of {len(one.subject)} bytes on a context declared for "
                    f"{self.case.maxlen} answered {got!r} rather than BadInput",
                    at,
                )
            return {"outcome": statused(got), "usage": used}
        # A plain call that ran out of budget is not something a context call
        # has to reproduce: the context's own ceilings are its creation's, and
        # its scratch is already there to be reused rather than grown.
        if row["outcome"] in (spec.MATCHED, spec.NO_MATCH):
            if statused(got) != row["outcome"] or (
                isinstance(got, Match) and list(got.ovector) != row["ovector"]
            ):
                self.fail("context", f"the context answers {got!r}, the plain call did not", at)
        return {"outcome": statused(got), "usage": used}

    def call_edge(self, held: MatchContext, trials: list[dict[str, Any]]) -> int | None:
        """The per-call cost and stack edges, on the first trial that completed.

        Memory is not a per-call limit on a context — the reservation is made
        once and a call takes no more — so the memory edge is creation's, and
        it was tested there.
        """
        for at, (one, row) in enumerate(zip(self.case.trials, trials)):
            if row["outcome"] not in (spec.MATCHED, spec.NO_MATCH):
                continue
            if len(one.subject) > self.case.maxlen:
                continue
            got = self.engine.context_match(
                held, one.subject, start=one.start, match_options=one.match_options
            )
            used = _usage(self.engine)
            for kind in ("cost", "stack"):
                self.call_edge_at(held, one, kind, used[kind], got, at)
            return at
        return None

    def call_edge_at(
        self, held: MatchContext, one: Trial, kind: str, observed: int, got: object, at: int
    ) -> None:
        for value in (observed, observed - 1):
            if value < 0:
                continue
            again = self.engine.context_match(
                held,
                one.subject,
                start=one.start,
                match_options=one.match_options,
                **{f"{kind}_limit": value},
            )
            self.count("checks", "context-edge")
            if value == observed:
                if again != got:
                    self.fail(
                        "context",
                        f"at the observed {kind} limit {observed} a context call answered "
                        f"{again!r} rather than {got!r}",
                        at,
                    )
            elif not isinstance(again, ResourceExceeded):
                self.fail(
                    "context",
                    f"one below the observed {kind} limit {observed} a context call "
                    f"answered {again!r} rather than being refused",
                    at,
                )


def run_case(
    engine: Engine,
    case: Case,
    *,
    budget: dict[str, int],
    oracle: object | None = None,
    edges: int = DEFAULT_EDGES,
) -> Outcome:
    """One case through all three checks, with pcre2 if there is one to hand.

    Without an oracle the semantic comparison is the one thing that does not
    run, which is what the committed shard is generated without: the file
    records what our engine answers, a test replays it through pcre2, and the
    two are kept apart so that regenerating the shard never needs a build of
    the pinned library.

    Anything that escapes as an exception is a crash, which is fatal and also
    a finding: a campaign that stopped at the first one would lose everything
    the run had already established.
    """
    try:
        return _Run(engine, case, budget, oracle, edges).run()
    except Exception as exc:
        return Outcome(
            None, (Finding("crash", case.index, f"{type(exc).__name__}: {exc}"),), Coverage()
        )
