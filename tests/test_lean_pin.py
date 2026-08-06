"""The artifact hash, as Lean carries it.

M7's gate 3 embeds `gen/engine.tir.json` in the Lean sources, decodes it and
prints it back byte for byte, so a regenerated artifact fails `lake build`
until somebody looks. The hash beside it is not part of that check — it is a
copy of the number the freeze record names, kept so the Lean side cannot
quietly disagree about which artifact it proved anything about.

A copy is only worth something while it is a copy, which is what this reads
back: the same way the pcre2 pin's two rows are read out of the pin rather
than trusted where THEOREMS.md repeats them.
"""

from __future__ import annotations

import hashlib
import re

from pcrevera.paths import LEAN_DIR, REPO_ROOT

ARTIFACT = REPO_ROOT / "gen" / "engine.tir.json"
LEAN_SOURCE = LEAN_DIR / "Pcrevera" / "Tir" / "Artifact.lean"

TEXT = LEAN_SOURCE.read_text()


def recorded() -> str:
    match = re.search(r'def artifactSha256 : String :=\s*"([0-9a-f]{64})"', TEXT)
    assert match is not None, "Artifact.lean no longer states a hash"
    return match.group(1)


def test_the_lean_pin_is_the_artifact_on_disk() -> None:
    assert recorded() == hashlib.sha256(ARTIFACT.read_bytes()).hexdigest()


def test_lean_embeds_the_artifact_rather_than_a_copy_of_it() -> None:
    """The bytes come from the one file, so there is nothing to keep in step."""
    assert 'include_str "../../../gen/engine.tir.json"' in TEXT
