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
import subprocess

import pytest

from pcrevera.oracle import pin as pin_module
from pcrevera.paths import REPO_ROOT
from pcrevera.sweep import manifest

FROZEN = REPO_ROOT / "THEOREMS.md"

TAG = "wave1-frozen"
"""The name the freeze record gives the commit, and the one thing in the record
that is not a property of this checkout."""

ARTIFACT = "gen/engine.tir.json"

TEXT = FROZEN.read_text()

NAMED = {
    "the artifact sha256": "gen/engine.tir.json",
    "the pin sha256": "oracle/pcre2-pin.toml",
    "oracle/corpus/wave1.json": "oracle/corpus/wave1.json",
    "oracle/corpus/sweep-regressions.json": "oracle/corpus/sweep-regressions.json",
    "oracle/corpus/pre-lowering.json": "oracle/corpus/pre-lowering.json",
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


def committed(rev: str, path: str) -> bytes | None:
    """One file as of a revision, or None where there is nothing to read — an
    exported tarball, a checkout without the tag, a machine without git."""
    try:
        done = subprocess.run(
            ["git", "show", f"{rev}:{path}"],
            cwd=REPO_ROOT,
            capture_output=True,
        )
    except OSError:
        return None
    return done.stdout if done.returncode == 0 else None


def test_the_tag_names_the_commit_the_record_describes() -> None:
    """The one row of the freeze table that points outside this checkout.

    Every hash above is checked against a file, which leaves the commit row
    saying something no file can contradict: that those bytes are the ones
    `wave1-frozen` resolves to. A tag left behind by a refreeze is the same
    silent failure the hashes exist to prevent, only worse — the record would
    be true of the working tree and wrong for anyone who followed it.

    So the tag is asked for the whole table rather than the artifact alone, and
    for standing behind HEAD. A commit carrying the right bytecode and last
    month's corpora is not the freeze this document describes, and the corpora
    are half of what the proofs replay; a commit off on its own is not this
    history's freeze at all. What is deliberately not asked is that the tag be
    HEAD, since work goes on after a freeze and that is the point of having
    one.

    While a refreeze is in flight the record describes a working tree that no
    commit holds yet, and there is nothing here to check; the tag is moved as
    the change lands. So the gate is on the state that gets shipped: once the
    recorded artifact is what HEAD carries, the tag has to carry all of it.
    """
    recorded = ROWS["the artifact sha256"]
    head = committed("HEAD", ARTIFACT)
    if head is None or hashlib.sha256(head).hexdigest() != recorded:
        pytest.skip(f"the artifact THEOREMS.md records is not in HEAD, so no {TAG} yet")
    assert (
        subprocess.run(
            ["git", "merge-base", "--is-ancestor", TAG, "HEAD"],
            cwd=REPO_ROOT,
            capture_output=True,
        ).returncode
        == 0
    ), f"{TAG} is not in this history"
    behind = []
    for label, path in sorted(NAMED.items()):
        tagged = committed(TAG, path)
        assert tagged is not None, (
            f"THEOREMS.md names {TAG}, which has no {path} to compare"
        )
        if hashlib.sha256(tagged).hexdigest() != ROWS[label]:
            behind.append(path)
    assert not behind, f"{TAG} is behind the freeze record on {', '.join(behind)}"


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
