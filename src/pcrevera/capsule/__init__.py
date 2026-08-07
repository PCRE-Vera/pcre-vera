"""Proof capsules: the versioned, self-contained descriptions of an artifact.

M8 has to move the shipped engine without rewriting what M7 finished, and the
two things cannot both live at `gen/engine.tir.json`. A capsule is the way out.
It is a manifest naming every byte an artifact was built from — the generator
source, the Lean development, the corpora, the oracle provenance — by content
hash, and a content-addressed blob store holding those bytes once no matter how
many manifests name them. Verification materializes a capsule into a build root
of its own and rebuilds it there, so the M7 baseline and today's shipped
artifact are checked by the same code without ever being in the same tree.

Nothing here is trusted. The manifest is data; the verifier recomputes every
number in it from the bytes the blob store hands back.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

SCHEMA_PREFIX = "pcrevera/"
"""Every schema string this package writes starts here, so a file from another
project cannot be mistaken for one of ours."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical(value: object) -> str:
    """The one JSON spelling this package writes and compares.

    Sorted keys and two-space indent, ending in a newline, which is what every
    other committed JSON in the tree already looks like.
    """
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


__all__ = ["SCHEMA_PREFIX", "canonical", "sha256_bytes", "sha256_file"]
