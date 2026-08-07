"""Cutting a capsule: writing the manifest and the blobs it names.

Cutting is the only operation that reads the working tree. Everything after it
reads the blob store, so once a capsule exists it is a fact about bytes rather
than about a checkout. A published manifest is never edited: a change produces
the next revision beside it, and the blobs the old one names stay where they
are.
"""

from __future__ import annotations

from pathlib import Path

from ..paths import REPO_ROOT
from . import blobs, canonical
from .manifest import MANIFEST_DIR, ManifestError, build, digest, filename, validate


def cut(
    *,
    capsule_name: str,
    role: str,
    artifact_version: int,
    manifest_version: int = 1,
    root: Path = REPO_ROOT,
    store: Path = blobs.STORE,
    manifests: Path = MANIFEST_DIR,
) -> tuple[Path, str]:
    """Write one capsule, and return its manifest path and hash."""
    document = build(
        capsule_name=capsule_name,
        role=role,
        artifact_version=artifact_version,
        manifest_version=manifest_version,
        root=root,
    )
    closure = validate(document)

    path = manifests / filename(document)
    if path.exists():
        held = path.read_text(encoding="utf-8")
        if held != canonical(document):
            raise ManifestError(
                f"{path.name} is published and would change; cut the next "
                "revision instead of editing it"
            )

    for logical, wanted in sorted(closure.items()):
        data = (root / logical).read_bytes()
        found = blobs.put(data, store)
        if found != wanted:
            raise ManifestError(f"{logical} hashes to {found}, not {wanted}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical(document), encoding="utf-8")
    return path, digest(document)


__all__ = ["cut"]
