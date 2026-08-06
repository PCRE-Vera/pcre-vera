"""The stratification report, held to the artifact and to its own rule.

The report is only worth trusting while it matches what the artifact says,
and while the sample it names is really what its recorded rule computes —
a hand-edited pick would silently survive otherwise. Both are regenerated
here and compared.
"""

from __future__ import annotations

import hashlib
import json

from pcrevera.paths import REPO_ROOT
from pcrevera.tir import strata

ARTIFACT = REPO_ROOT / "gen" / "engine.tir.json"
REPORT = json.loads(strata.PATH.read_text())


def test_the_report_is_what_the_artifact_says() -> None:
    assert strata.build(ARTIFACT) == strata.PATH.read_text()


def test_the_report_names_the_artifact_it_was_computed_from() -> None:
    assert REPORT["artifact"] == hashlib.sha256(ARTIFACT.read_bytes()).hexdigest()


def test_every_owed_function_appears_exactly_once() -> None:
    ledger = json.loads((REPO_ROOT / "conformance" / "layer-i.json").read_text())
    owed = [entry["name"] for entry in ledger["post_parse"]]
    names = [row["name"] for row in REPORT["functions"]]
    assert sorted(names) == sorted(owed)
    assert len(names) == len(set(names)) == 80


def test_the_counts_add_up() -> None:
    rows = REPORT["functions"]
    assert REPORT["counts"]["owed"] == len(rows)
    assert REPORT["counts"]["proved"] == sum(1 for r in rows if r["theorem"])
    families: dict[str, int] = {}
    for row in rows:
        families[row["family"]] = families.get(row["family"], 0) + 1
    assert REPORT["counts"]["families"] == families


def test_the_sample_is_what_the_rule_computes() -> None:
    """The rule, reapplied to the rows from scratch: the universe filter,
    the score, and every tie-break, independently of `strata.choose`."""
    universe = [
        r for r in REPORT["functions"]
        if not r["theorem"] and r["shape"]["calls_in_loops"] >= 1
        and r["shape"]["call_sites"] >= 2
    ]
    assert universe, "the rule's universe went empty; the rule needs revisiting"
    best = min(
        universe,
        key=lambda r: (
            r["shape"]["statements"] + 10 * r["shape"]["loops"],
            -len(r["callees"]),
            r["shape"]["ifs"],
            r["name"],
        ),
    )
    assert REPORT["sample"]["selected"] == best["name"]
    assert REPORT["sample"]["rule"] == strata.RULE


def test_the_sample_exercises_composition_in_a_loop() -> None:
    """What the sample was chosen to measure, asserted rather than
    remembered: at least one callee's budget threads through iteration."""
    selected = REPORT["sample"]["selected"]
    row = next(r for r in REPORT["functions"] if r["name"] == selected)
    assert row["shape"]["calls_in_loops"] >= 1
    assert row["shape"]["call_sites"] >= 2
