"""Laying a capsule out on disk, in a root of its own.

Verification never reads the working tree. It writes the capsule's blobs to the
logical paths its manifest gives them, under a directory keyed by the manifest's
own hash, and runs everything there. That is what makes two capsules
independent: the M7 baseline and today's shipped artifact are built from bytes
that cannot have leaked into each other, even though they may share every blob.

The one thing materialization does not carry is the Lean dependency. Batteries
is three hundred megabytes of downloaded package, pinned by `lake-manifest.json`
and the toolchain exactly as CPython is pinned by `generator.python`, and both
are named by the manifest without being vendored into it. It is cloned from a
local cache into a shared directory keyed by that pin, so a capsule build never
reaches the network and never writes to the checkout's own `.lake`.
"""

from __future__ import annotations

import os
import platform
import shutil
import subprocess
from pathlib import Path

from ..paths import REPO_ROOT, TMP_DIR
from . import blobs, sha256_file
from .manifest import ManifestError, normalized

ROOTS = TMP_DIR / "capsule"

LIVE_PACKAGES = REPO_ROOT / "lean" / ".lake" / "packages"


class MaterializeError(RuntimeError):
    """A capsule that could not be laid out from the bytes it names."""


def build_root(capsule_name: str, manifest_digest: str, under: Path = ROOTS) -> Path:
    """Where a capsule is materialized: its name, and what it is.

    The manifest hash is in the directory name because it covers the complete
    source set and the artifact, which is exactly the key a shared `.olean`
    cache is allowed to have. Two runs of the same capsule reuse the build; a
    changed byte anywhere gets a different directory.
    """
    return under / f"{capsule_name}-{manifest_digest[:16]}"


def place(closure: dict[str, str], root: Path, store: Path = blobs.STORE) -> None:
    """Write every file the closure names, under `root` and nowhere else."""
    resolved = root.resolve()
    for logical, digest in sorted(closure.items()):
        destination = (root / normalized(logical)).resolve()
        if not destination.is_relative_to(resolved):
            raise ManifestError(f"{logical} would land outside the capsule root")
        blobs.place(digest, destination, store)


def stale(closure: dict[str, str], root: Path) -> bool:
    """Whether a previously materialized root still holds exactly this capsule.

    Reused only when every named file is there with the right hash and nothing
    else is: a build directory with one extra module in it is a build directory
    that can compile something the manifest does not name.
    """
    if not root.is_dir():
        return True
    present: set[str] = set()
    for where, directories, names in os.walk(root):
        # Pruned rather than filtered afterwards: `.lake/packages` is a symlink
        # into a shared three-hundred-megabyte dependency clone, and walking it
        # would cost more than the whole verification.
        directories[:] = [name for name in directories if name != ".lake"]
        here = Path(where).relative_to(root)
        present |= {(here / name).as_posix() for name in names}
    if present != set(closure):
        return True
    return any(sha256_file(root / logical) != digest for logical, digest in closure.items())


def clone_tree(source: Path, destination: Path) -> None:
    """Copy a directory as cheaply as the filesystem allows.

    APFS and modern Linux filesystems can share the blocks, which turns three
    hundred megabytes into a fraction of a second. Where they cannot, it is an
    ordinary copy and the only cost is time.
    """
    if destination.exists():
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    flag = "-c" if platform.system() == "Darwin" else "--reflink=auto"
    done = subprocess.run(
        ["cp", "-R", flag, str(source), str(destination)], capture_output=True
    )
    if done.returncode == 0:
        return
    shutil.copytree(source, destination)


def lean_dependencies(root: Path, live: Path = LIVE_PACKAGES) -> None:
    """Give the capsule's Lean workspace its pinned packages, offline.

    The shared cache is keyed by the capsule's own `lake-manifest.json`, which
    is what names the dependency revision, so two capsules pinning different
    revisions never share one. If the checkout has no package cache to clone,
    say so: fetching one here would be the download capsule verification is not
    allowed to make.
    """
    workspace = root / "lean" / ".lake"
    packages = workspace / "packages"
    if packages.exists():
        return
    pin = root / "lean" / "lake-manifest.json"
    if not pin.is_file():
        raise MaterializeError("the capsule carries no lake-manifest.json")
    shared = ROOTS / "packages" / sha256_file(pin)[:16]
    if not shared.exists():
        if not live.is_dir():
            raise MaterializeError(
                f"no Lean package cache at {live}; run make lean once before "
                "verifying a capsule offline"
            )
        clone_tree(live, shared)
    workspace.mkdir(parents=True, exist_ok=True)
    os.symlink(shared, packages)


def materialize(
    capsule_name: str,
    manifest_digest: str,
    closure: dict[str, str],
    *,
    under: Path = ROOTS,
    store: Path = blobs.STORE,
) -> Path:
    """The capsule on disk, ready to build, and the root it lives in."""
    root = build_root(capsule_name, manifest_digest, under)
    if stale(closure, root):
        shutil.rmtree(root, ignore_errors=True)
        root.mkdir(parents=True)
        place(closure, root, store)
    return root


__all__ = [
    "LIVE_PACKAGES",
    "ROOTS",
    "MaterializeError",
    "build_root",
    "clone_tree",
    "lean_dependencies",
    "materialize",
    "place",
    "stale",
]
