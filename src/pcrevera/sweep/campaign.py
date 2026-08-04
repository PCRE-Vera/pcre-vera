"""A whole manifest, run.

One case is `checks.run_case`; this is what turns a manifest into a result
document, a coverage report and a list of failures. It runs sequentially when
it is handed a live oracle — which is what a test does, since the oracle there
is a session fixture — and across processes when it is asked to open its own,
which is what a campaign of a few thousand patterns needs to finish in an
afternoon. The two paths run the same function over the same cases in the same
order, and the result document is sorted by index either way, so a sweep says
the same thing however many workers it had.

The result document is the manifest's cases with every answer attached, under
the conformance corpora's envelope, naming the manifest it came from by hash.
That is the file the Go and JavaScript runners replay: they never generate
anything, and they never ask pcre2 anything, so what they are checking is that
their own generated engine says exactly what this one did.
"""

from __future__ import annotations

import atexit
import multiprocessing
import time
from dataclasses import dataclass, field
from typing import Any, Callable

from ..engine.driver import Engine
from ..oracle import build as build_module
from ..oracle import conformance
from ..oracle import pin as pin_module
from .checks import DEFAULT_EDGES, Coverage, Finding, Outcome, run_case
from .manifest import Manifest
from .population import Case

NOTE = (
    "The answers of one differential sweep, one entry per case of the manifest "
    "named by hash below. Every implementation of the engine must give exactly "
    "these answers: the same compile outcome, the same ovector, the same "
    "certified bounds, the same observed cost, stack and memory, the same "
    "answer from the other matcher, and the same reservation from a "
    "preallocated context. An outcome is a match outcome ordinal (0 matched, 1 "
    "no match, 2 ResourceExceeded, 3 BadInput); a bound of null is the "
    "ExceedsBudget of DESIGN.md section 2.4, and a trial marked edges is one "
    "whose three limits are re-run at the observed value and one below."
)


@dataclass
class Report:
    """What a run produced, before it is written anywhere."""

    manifest: Manifest
    records: list[dict[str, Any]] = field(default_factory=list)
    findings: list[Finding] = field(default_factory=list)
    coverage: Coverage = field(default_factory=Coverage)
    seconds: float = 0.0

    def add(self, outcome: Outcome) -> None:
        if outcome.record is not None:
            self.records.append(outcome.record)
        self.findings.extend(outcome.findings)
        self.coverage.merge(outcome.coverage)

    def order(self) -> None:
        self.records.sort(key=lambda one: one["index"])
        self.findings.sort(key=lambda one: (one.index, one.trial or -1, one.kind))

    def document(self, **extra: Any) -> dict[str, Any]:
        """The result document, which is what every other runner replays."""
        return conformance.document(
            NOTE,
            self.records,
            seed=self.manifest.seed,
            manifest=self.manifest.digest,
            budget=self.manifest.budget,
            coverage=self.coverage.as_json(),
            **extra,
        )


def run(
    man: Manifest,
    *,
    engine: Engine | None = None,
    oracle: object | None = None,
    edges: int = DEFAULT_EDGES,
    progress: Callable[[int, int], None] | None = None,
) -> Report:
    """Every case of a manifest, in this process."""
    held = engine or Engine()
    report = Report(man)
    started = time.monotonic()
    for done, case in enumerate(man.cases, start=1):
        report.add(run_case(held, case, budget=man.budget, oracle=oracle, edges=edges))
        if progress is not None:
            progress(done, len(man.cases))
    report.seconds = time.monotonic() - started
    report.order()
    return report


_STATE: dict[str, Any] = {}


def _begin(budget: dict[str, int], edges: int, wants_oracle: bool) -> None:
    """A worker's own engine, and its own pcre2 if the run compares against one.

    One shim process per worker rather than one shared: the protocol is a
    request and a reply over a pipe, so a shared one would serialize the whole
    campaign behind it.
    """
    _STATE["engine"] = Engine()
    _STATE["budget"] = budget
    _STATE["edges"] = edges
    _STATE["oracle"] = opened() if wants_oracle else None


def _one(case: Case) -> Outcome:
    return run_case(
        _STATE["engine"],
        case,
        budget=_STATE["budget"],
        oracle=_STATE["oracle"],
        edges=_STATE["edges"],
    )


def run_parallel(
    man: Manifest,
    *,
    jobs: int,
    oracle: bool,
    edges: int = DEFAULT_EDGES,
    progress: Callable[[int, int], None] | None = None,
) -> Report:
    """The same run, spread over `jobs` processes.

    Every case is a function of the manifest's own numbers and its index, and
    nothing a case does can be seen by another one, so the only thing the
    workers share is the order the results are put back into.
    """
    if jobs <= 1:
        return run(man, edges=edges, progress=progress, oracle=opened() if oracle else None)
    report = Report(man)
    started = time.monotonic()
    context = multiprocessing.get_context("spawn")
    with context.Pool(
        jobs, initializer=_begin, initargs=(man.budget, edges, oracle)
    ) as pool:
        for done, outcome in enumerate(
            pool.imap_unordered(_one, man.cases, chunksize=4), start=1
        ):
            report.add(outcome)
            if progress is not None:
                progress(done, len(man.cases))
    report.seconds = time.monotonic() - started
    report.order()
    return report


def opened(log: Callable[[str], None] | None = None):
    """A running pcre2, closed when the process that opened it exits.

    One statement of it, for the three places that need one: a worker, a
    single-process run, and the command line's own subcommands.
    """
    held = pin_module.load()
    running = build_module.open_oracle(build_module.ensure(pin=held, log=log), held)
    running.start()
    atexit.register(running.close)
    return running
