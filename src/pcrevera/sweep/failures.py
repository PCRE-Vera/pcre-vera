"""A failure, written down so that it survives the run that found it.

DESIGN.md section 8 wants a disagreement minimized and added to the corpus, and
that only works if what was written down is enough to get back to it. So a
record carries the case in full, the class of the disagreement, every number
it can be regenerated from, and the identity of what found it: the SHA-256 of
the TIR artifact and the pinned pcre2's version and tarball hash. A failure
against a different artifact is a different failure, and one against a
different pcre2 may not be a failure at all.

The minimized case sits beside the original rather than replacing it, because
the reducer's premise — the same disagreement class, still there — is a claim
worth being able to check.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .. import leanexport
from ..engine.program import program
from ..oracle import conformance
from ..oracle import pin as pin_module
from .checks import Finding
from .manifest import encode
from .population import Case

NOTE = (
    "Failures from one differential sweep, each replayable on its own. The "
    "artifact hash and the pinned pcre2 identity are part of the record "
    "because a disagreement is a disagreement between two named things; the "
    "minimized case, where there is one, preserves the class of the original "
    "and is what gets promoted into the committed corpus once the bug is "
    "fixed and pcre2 has confirmed the answer."
)


@dataclass(frozen=True)
class Identity:
    """What found the failure, named well enough to reproduce it."""

    artifact: str
    pcre2_version: str
    pcre2_sha256: str
    pin: str


def identity() -> Identity:
    """The artifact this checkout builds and the pcre2 it is pinned to."""
    held = pin_module.load()
    return Identity(
        artifact=leanexport.digest(leanexport.artifact(program())),
        pcre2_version=held.version,
        pcre2_sha256=held.sha256,
        pin=held.digest,
    )


def replay(
    case: Case, subjects: int, structured: int, budget: dict[str, int], edges: int
) -> str:
    """The command that runs this one case again, and nothing else.

    The budget is spelled out rather than left to the default, because a run
    that was given one is a run whose failure may not exist without it: a
    ResourceExceeded is a decline under one budget and a finding under
    another, and a replay that quietly used the default would be replaying a
    different question.
    """
    return (
        f"uv run python -m pcrevera.sweep replay --seed {case.seed} "
        f"--index {case.index} --subjects {subjects} --structured {structured} "
        f"--cost {budget['cost']} --stack {budget['stack']} "
        f"--memory {budget['memory']} --edges {edges}"
    )


def record(
    finding: Finding,
    case: Case,
    *,
    subjects: int,
    structured: int,
    budget: dict[str, int],
    edges: int,
    minimized: Case | None = None,
) -> dict[str, Any]:
    """One failure, with everything needed to reach it again."""
    out: dict[str, Any] = {
        **finding.as_json(),
        "seed": case.seed,
        "subjects": subjects,
        "structured": structured,
        "case": encode(case),
        "replay": replay(case, subjects, structured, budget, edges),
    }
    if minimized is not None:
        out["minimized"] = encode(minimized)
    return out


def document(
    records: list[dict[str, Any]],
    found: Identity,
    budget: dict[str, int],
    edges: int,
) -> dict[str, Any]:
    """Every failure of one run, under the corpora's own envelope.

    The budget and the edge count are the run's, in the header rather than in
    each record, because they are what the run was: a reducer handed this file
    has to shrink under the same limits the failure was found under, or it is
    shrinking towards a different failure.
    """
    return conformance.document(
        NOTE, records, identity=asdict(found), budget=dict(budget), edges=edges
    )


def write(
    path: Path,
    records: list[dict[str, Any]],
    found: Identity,
    budget: dict[str, int],
    edges: int,
) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(conformance.text(document(records, found, budget, edges)))
    return path
