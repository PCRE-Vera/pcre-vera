"""The content-addressed store a capsule's bytes live in.

Two manifests that name the same Lean development name the same blobs, so the
tree carries one copy of it however many capsules there are. A blob's name is
its SHA-256 and nothing else: a manifest supplies the logical path a file goes
back to, never the place its bytes are read from, so a manifest cannot point at
a file whose contents are not what its hash says.
"""

from __future__ import annotations

import os
import shutil
from pathlib import Path

from ..paths import REPO_ROOT
from . import sha256_bytes

STORE = REPO_ROOT / "proofs" / "blobs" / "sha256"

DIGEST_LENGTH = 64


class BlobError(ValueError):
    """A digest that is not one, or bytes that are not what a digest says."""


def is_digest(digest: str) -> bool:
    return len(digest) == DIGEST_LENGTH and all(
        c in "0123456789abcdef" for c in digest
    )


def path_for(digest: str, store: Path = STORE) -> Path:
    if not is_digest(digest):
        raise BlobError(f"{digest!r} is not a lowercase sha256")
    return store / digest


def has(digest: str, store: Path = STORE) -> bool:
    return path_for(digest, store).is_file()


def put(data: bytes, store: Path = STORE) -> str:
    """Store bytes and return their digest; storing twice is storing once."""
    digest = sha256_bytes(data)
    target = path_for(digest, store)
    if target.is_file():
        return digest
    target.parent.mkdir(parents=True, exist_ok=True)
    scratch = target.with_name(target.name + f".{os.getpid()}.part")
    scratch.write_bytes(data)
    os.replace(scratch, target)
    return digest


def get(digest: str, store: Path = STORE) -> bytes:
    """The bytes of a blob, checked against the name they were filed under.

    The check is not ceremony. A blob store is a directory, and a directory can
    be edited; a verifier that trusted the file name would report the hash the
    manifest asked for rather than the hash of what it read.
    """
    path = path_for(digest, store)
    if not path.is_file():
        raise BlobError(f"no blob {digest}")
    data = path.read_bytes()
    found = sha256_bytes(data)
    if found != digest:
        raise BlobError(f"blob {digest} holds bytes with sha256 {found}")
    return data


def place(digest: str, destination: Path, store: Path = STORE) -> None:
    """Put a blob at a logical path, sharing the bytes where the system lets us.

    A hard link costs nothing and makes a materialized capsule free; a
    filesystem that refuses one gets a copy and the same result. Either way the
    destination is written fresh, so a leftover from an earlier run cannot
    survive as part of a capsule.
    """
    source = path_for(digest, store)
    get(digest, store)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() or destination.is_symlink():
        destination.unlink()
    try:
        os.link(source, destination)
        return
    except OSError:
        pass
    shutil.copyfile(source, destination)
    if sha256_bytes(destination.read_bytes()) != digest:
        raise BlobError(f"copying blob {digest} did not preserve it")


__all__ = [
    "DIGEST_LENGTH",
    "STORE",
    "BlobError",
    "get",
    "has",
    "is_digest",
    "path_for",
    "place",
    "put",
]
