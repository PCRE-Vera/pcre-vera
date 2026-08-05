"""The freeze record, held to the files it names.

`THEOREMS.md` is where the identity of the frozen wave 1 artifact is written
down: the artifact's hash, the pinned pcre2's, every corpus's, and the sweep
manifest the campaign that closed M5 ran. A document like that is only worth
something while it is true, and the way it stops being true is silent — a
corpus is regenerated, the hash beside its name is not.

So the numbers are checked rather than trusted. The manifest is not even
checked against a file: it is rebuilt from the five numbers the recorded
command carries, which is the same claim the document makes about it.
"""

from __future__ import annotations

import hashlib
import re

import pytest

from pcrevera.oracle import pin as pin_module
from pcrevera.paths import REPO_ROOT
from pcrevera.sweep import manifest

FROZEN = REPO_ROOT / "THEOREMS.md"

TEXT = FROZEN.read_text()

NAMED = {
    "the artifact sha256": "gen/engine.tir.json",
    "the pin sha256": "oracle/pcre2-pin.toml",
    "oracle/corpus/wave1.json": "oracle/corpus/wave1.json",
    "oracle/corpus/sweep-regressions.json": "oracle/corpus/sweep-regressions.json",
    "conformance/corpus.json": "conformance/corpus.json",
    "conformance/certificates.json": "conformance/certificates.json",
    "conformance/lowering.json": "conformance/lowering.json",
    "conformance/migration.json": "conformance/migration.json",
    "conformance/sweep.json": "conformance/sweep.json",
}
"""Every row of the freeze tables that is a hash of a file in this checkout,
and which file it is."""

FROM_THE_PIN = {
    "the pcre2 version": "version",
    "the pcre2 tarball sha256": "sha256",
}
"""And the two rows that are copied out of the pin rather than computed from a
file. Hashing the pin file catches an edit to it; only reading these back
catches an edit to the copy, which is the failure mode a freeze record has —
it is a document, and documents are edited by hand."""


def rows() -> dict[str, str]:
    """The two-column rows of the document's tables, continuations joined.

    A hash does not fit in a table cell, so it is written across two rows with
    the label blank on the second. Joining with nothing between them is what
    makes the value one string again.
    """
    out: dict[str, str] = {}
    label = ""
    for line in TEXT.splitlines():
        line = line.strip()
        if not line.startswith("|") or not line.endswith("|"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if len(cells) != 2:
            continue
        if cells[0]:
            label = cells[0]
            out[label] = cells[1]
        elif label:
            out[label] += cells[1]
    return out


ROWS = rows()


@pytest.mark.parametrize("label, path", sorted(NAMED.items()))
def test_the_freeze_record_names_this_file(label: str, path: str) -> None:
    held = REPO_ROOT / path
    assert ROWS[label] == hashlib.sha256(held.read_bytes()).hexdigest(), (
        f"THEOREMS.md records a different sha256 for {path}"
    )


@pytest.mark.parametrize("label, field", sorted(FROM_THE_PIN.items()))
def test_the_freeze_record_copies_the_pin_faithfully(label: str, field: str) -> None:
    assert ROWS[label] == getattr(pin_module.load(), field), (
        f"THEOREMS.md records a {label} the pin does not"
    )


def test_the_freeze_record_names_a_sweep_this_seed_produces() -> None:
    """The recorded manifest hash, rebuilt from the recorded command.

    The command is in the document as a reader would run it, so the five
    numbers are read back out of it rather than repeated here: a document that
    said one thing in its command and another in its hash would pass any test
    that took them from the same place.
    """
    command = re.search(r"make sweep SWEEP=\"(.*?)\"", TEXT, re.DOTALL)
    assert command is not None, "THEOREMS.md no longer records the campaign command"
    words = command.group(1).replace("\\\n", " ").split()
    asked = dict(zip(words[::2], words[1::2]))
    recorded = re.search(r"manifest sha256\s+([0-9a-f]{64})", TEXT)
    assert recorded is not None, "THEOREMS.md no longer records the manifest hash"
    built = manifest.build(
        int(asked["--seed"]),
        structured=int(asked["--structured"]),
        hostile=int(asked["--hostile"]),
        subjects=int(asked["--subjects"]),
    )
    assert manifest.digest(built) == recorded.group(1)
