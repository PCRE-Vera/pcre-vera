"""Shrinking a failing case until only the failure is left.

A generated pattern is a dozen constructs deep and a generated case carries
thirty-two subjects, so the thing that actually disagrees with pcre2 is buried.
DESIGN.md section 8 wants the minimized case in the corpus rather than the
generated one, and the corpus is read by people.

What is preserved is the class of the disagreement — a compile disagreement
stays a compile disagreement, a bound violation stays a bound violation —
never its wording, since the wording carries the very numbers that are supposed
to shrink. The shrink itself is Zeller's delta debugging on the pattern and on
the subject, and a plain greedy pass on everything else: the trials, the two
option sets, the start offset and the conventions. Each step keeps whatever
still fails and gives up on whatever does not, so the result depends on nothing
but the predicate.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Callable, Sequence, TypeVar

from ..engine.driver import Engine
from .checks import DEFAULT_EDGES, run_case
from .population import Case, Trial

T = TypeVar("T", bound=Sequence)


def ddmin(items: T, ok: Callable[[T], bool]) -> T:
    """The shortest subsequence this can reach that still satisfies `ok`.

    Delta debugging rather than one-byte-at-a-time because a pattern is often
    only interesting with a whole group removed, and because a hundred-byte
    pattern would otherwise cost a hundred runs per pass.
    """
    granularity = 2
    while len(items) >= 2:
        size = max(1, len(items) // granularity)
        chunks = [items[at : at + size] for at in range(0, len(items), size)]
        for at in range(len(chunks)):
            candidate = _joined(chunks[:at] + chunks[at + 1 :], items)
            if ok(candidate):
                items = candidate
                granularity = max(2, granularity - 1)
                break
        else:
            if granularity >= len(items):
                break
            granularity = min(len(items), granularity * 2)
    return items


def _joined(chunks: list, like: Sequence):
    out = like[:0]
    for chunk in chunks:
        out = out + chunk
    return out


class _Shrink:
    """One case being reduced: the predicate, and one pass over each dimension.

    An object rather than a closure threaded through five functions. What the
    predicate needs — the engine, the class to preserve, the budget, the oracle
    and the edge count — are fields, so nothing has to be captured and the loop
    variables of `_trials` are arguments like any other.
    """

    def __init__(
        self,
        engine: Engine,
        kind: str,
        budget: dict[str, int],
        oracle: object | None,
        edges: int,
    ) -> None:
        self.engine = engine
        self.kind = kind
        self.budget = budget
        self.oracle = oracle
        self.edges = edges

    def fails(self, case: Case) -> bool:
        outcome = run_case(
            self.engine, case, budget=self.budget, oracle=self.oracle, edges=self.edges
        )
        return any(one.kind == self.kind for one in outcome.findings)

    def run(self, case: Case) -> Case:
        while True:
            shrunk = self.once(case)
            if shrunk == case:
                return case
            case = shrunk

    def once(self, case: Case) -> Case:
        """One sweep over every dimension, each kept only if it still fails."""
        # No subjects at all is tried first, and it is the answer a compile
        # disagreement should reach: a case that keeps a trial it does not need
        # is a case that gets written into the corpus as a match, which is not
        # what it is about. Delta debugging alone would never offer it, since
        # it stops at one element.
        if case.trials and self.fails(_sized(case, ())):
            case = _sized(case, ())
        else:
            case = _sized(
                case,
                ddmin(
                    case.trials,
                    lambda picked: bool(picked) and self.fails(_sized(case, picked)),
                ),
            )
        case = replace(
            case,
            pattern=ddmin(
                case.pattern, lambda picked: self.fails(replace(case, pattern=picked))
            ),
        )
        for name in case.options:
            candidate = replace(case, options=tuple(o for o in case.options if o != name))
            if self.fails(candidate):
                case = candidate
        for at in range(len(case.trials)):
            case = self.trial(case, at)
        return self.conventions(case)

    def trial(self, case: Case, at: int) -> Case:
        """The subject, the match options and the start offset of one trial.

        A start offset has to move with the subject it points into, so the two
        shrink together: a candidate subject is always tried with an offset
        that still lands inside it.
        """
        one = case.trials[at]

        def holds(picked: Trial) -> bool:
            return self.fails(_with(case, at, picked))

        subject = ddmin(
            one.subject,
            lambda picked: holds(
                replace(one, subject=picked, start=min(one.start, len(picked)))
            ),
        )
        one = replace(one, subject=subject, start=min(one.start, len(subject)))
        for name in one.match_options:
            candidate = replace(
                one, match_options=tuple(o for o in one.match_options if o != name)
            )
            if holds(candidate):
                one = candidate
        if one.start and holds(replace(one, start=0)):
            one = replace(one, start=0)
        return _with(case, at, one)

    def conventions(self, case: Case) -> Case:
        """The default conventions, if the failure does not depend on the pair.

        Both at once and then each on its own: \\R is read against the newline
        convention as well as the BSR one, so a failure can need the pair
        without needing either half of it.
        """
        for newline, bsr in (("LF", "UNICODE"), ("LF", case.bsr), (case.newline, "UNICODE")):
            if (newline, bsr) == (case.newline, case.bsr):
                continue
            candidate = replace(case, newline=newline, bsr=bsr)
            if self.fails(candidate):
                return candidate
        return case


def _sized(case: Case, trials: tuple[Trial, ...]) -> Case:
    """The same case with these trials, and a context sized for them.

    The declared maximum is the longest subject the case carries, so it has to
    move when the subjects do, or a shrunk case would be creating a context for
    a subject nobody asks about any more.
    """
    return replace(
        case, trials=trials, maxlen=max((len(one.subject) for one in trials), default=0)
    )


def _with(case: Case, at: int, trial: Trial) -> Case:
    """The case with one trial replaced, and the context sized again."""
    return _sized(case, case.trials[:at] + (trial,) + case.trials[at + 1 :])


def minimize(
    case: Case,
    kind: str,
    *,
    engine: Engine | None = None,
    budget: dict[str, int],
    oracle: object | None = None,
    edges: int = DEFAULT_EDGES,
) -> Case:
    """The smallest case this can reach that still fails in the same class."""
    held = _Shrink(engine or Engine(), kind, budget, oracle, edges)
    if not held.fails(case):
        raise ValueError(f"the case does not fail with a {kind} finding to begin with")
    return held.run(case)
