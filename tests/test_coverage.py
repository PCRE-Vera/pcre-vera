"""The layer I coverage ledger, held to the artifact it was computed from.

The ledger is what turns gate 5's "every post-parse function has its lemma"
into something a machine can check. It is only worth that while it matches the
artifact, and the way it stops matching is silent: a new helper appears, the
manifest still lists the old set, and the proof looks complete when it is not.

So the manifest is regenerated here and compared byte for byte, and the two
facts it rests on — that the entry list really is what the wrappers call, and
that every excluded name really is unreachable except through `parse` — are
checked rather than trusted.
"""

from __future__ import annotations

import hashlib
import json
import re

from pcrevera.paths import GEN_DIR, REPO_ROOT
from pcrevera.tir import coverage, serialize

ARTIFACT = REPO_ROOT / "gen" / "engine.tir.json"
MANIFEST = REPO_ROOT / "conformance" / "layer-i.json"
GO_WRAPPER = GEN_DIR / "go" / "pcrevera.go"
JS_WRAPPER = GEN_DIR / "js" / "index.mjs"

PROGRAM = serialize.loads(ARTIFACT.read_text())
GRAPH = coverage.call_graph(PROGRAM)
LEDGER = json.loads(MANIFEST.read_text())


def test_the_manifest_is_what_the_artifact_says() -> None:
    assert coverage.build(ARTIFACT) == MANIFEST.read_text()


def test_the_manifest_names_the_artifact_it_was_computed_from() -> None:
    assert LEDGER["artifact"] == hashlib.sha256(ARTIFACT.read_bytes()).hexdigest()


def test_every_entry_is_a_function_of_the_artifact() -> None:
    for name in coverage.ENTRIES:
        assert name in GRAPH, name


def test_the_entries_are_what_the_wrappers_actually_call() -> None:
    """The ledger's roots, read off the two wrappers rather than believed.

    A wrapper that reached into the engine for one more function would widen
    the public surface without widening the ledger, and every other check here
    would still pass.
    """
    go_calls = set(re.findall(r"engine\.Tir_([a-z_0-9]+)\(", GO_WRAPPER.read_text()))
    imports = re.search(r"import \{(.*?)\} from \"\./engine\.mjs\";",
                        JS_WRAPPER.read_text(), re.S)
    assert imports is not None
    js_names = {
        # `compile as engineCompile` renames on import; the engine's name is
        # what the ledger is keyed by.
        line.split(" as ")[0].strip().rstrip(",")
        for line in imports.group(1).splitlines()
        if line.strip()
    }
    js_calls = js_names & set(GRAPH)
    assert go_calls == set(coverage.ENTRIES)
    assert js_calls == set(coverage.ENTRIES)


def test_the_three_sets_partition_the_artifact() -> None:
    owed = {entry["name"] for entry in LEDGER["post_parse"]}
    parser = set(LEDGER["parser"]["functions"])
    unreachable = set(LEDGER["unreachable"])
    assert owed & parser == set()
    assert owed & unreachable == set()
    assert parser & unreachable == set()
    assert owed | parser | unreachable == set(GRAPH)


def test_the_parser_subtree_is_only_reached_through_the_parse() -> None:
    """Every excluded name would be unreachable if `parse` were a leaf.

    Which is what makes the exclusion an honest one: those functions are the
    parse, not work quietly left out of the proof.
    """
    after_parse = coverage.reach(GRAPH, coverage.ENTRIES, frozenset({coverage.PARSER_ROOT}))
    for name in LEDGER["parser"]["functions"]:
        assert name not in after_parse, name


def test_what_the_parser_shares_is_owed_a_lemma_anyway() -> None:
    """The exclusion is parser-*exclusive*, not the whole parse subtree.

    `newline_at` and `ct` belong to the matcher as much as to the parser, so
    excluding them because the parser calls them would be quietly dropping
    work. The manifest records exactly which names those are.
    """
    owed = {entry["name"] for entry in LEDGER["post_parse"]}
    parser_reaches = coverage.reach(GRAPH, (coverage.PARSER_ROOT,), frozenset())
    shared = sorted(parser_reaches & owed)
    assert shared == LEDGER["parser"]["shared_with_post_parse"]
    assert parser_reaches <= set(LEDGER["parser"]["functions"]) | owed


def test_the_post_parse_set_is_closed_under_calling() -> None:
    """A function owed a lemma may only call functions also owed one, or the
    parser — otherwise the ledger would have a hole its own arithmetic hides."""
    owed = {entry["name"] for entry in LEDGER["post_parse"]}
    allowed = owed | {coverage.PARSER_ROOT}
    for name in owed:
        for callee in GRAPH[name]:
            assert callee in allowed, f"{name} calls {callee}"


def test_the_counts_are_the_sets() -> None:
    counts = LEDGER["counts"]
    assert counts["declared"] == len(GRAPH)
    assert counts["post_parse"] == len(LEDGER["post_parse"])
    assert counts["parser"] == len(LEDGER["parser"]["functions"])
    assert counts["unreachable"] == len(LEDGER["unreachable"])
    assert counts["reachable"] == counts["declared"] - counts["unreachable"]
    assert counts["proved"] == sum(1 for e in LEDGER["post_parse"] if e["theorem"])


def test_gate_five_is_open_until_every_name_carries_a_theorem() -> None:
    """The completion condition itself, so that closing gate 5 is a fact about
    this file rather than a claim in a plan."""
    missing = [e["name"] for e in LEDGER["post_parse"] if not e["theorem"]]
    assert coverage.complete(LEDGER) == (missing == [])
