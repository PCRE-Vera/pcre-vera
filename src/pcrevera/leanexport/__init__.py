"""Canonical emission of engine.tir.json and the hash tooling that pins it.

The artifact is the identity everything downstream is tied to: the Lean side
reads it through its own decoder, the printers stamp its SHA-256 into every
file they emit, and CI refuses a checkout whose committed artifact is not what
the generator produces today.

Nothing here is part of the trusted base. It writes a file and hashes it, and
the reader on the other side decides whether it believes what it read.
"""

from __future__ import annotations

import hashlib

from ..paths import GEN_DIR
from ..tir import ir, serialize

ARTIFACT_PATH = GEN_DIR / "engine.tir.json"
"""Where the committed artifact lives."""


def artifact(built: ir.Program) -> str:
    """The canonical text of a program, ending in exactly one newline."""
    return serialize.dumps(built)


def digest(text: str) -> str:
    """The SHA-256 of an artifact.

    The canonical encoding is pure ASCII, so asking for ASCII here is a check
    of that claim rather than a choice of codec: a byte above 0x7e would mean
    the serializer had stopped being canonical.
    """
    return hashlib.sha256(text.encode("ascii")).hexdigest()


__all__ = ["ARTIFACT_PATH", "artifact", "digest"]
