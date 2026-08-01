"""Where things live on disk.

Every path in the project is derived from the repository root, so a checkout
can sit anywhere and the oracle cache can be redirected to a shared location
on a build machine.
"""

from __future__ import annotations

import os
from pathlib import Path

REPO_ROOT = Path(os.environ.get("PCRETRUSTE_ROOT") or Path(__file__).resolve().parents[2])

ORACLE_DIR = REPO_ROOT / "oracle"
PIN_PATH = ORACLE_DIR / "pcre2-pin.toml"
SHIM_SOURCE = ORACLE_DIR / "pcre2shim" / "shim.c"
CORPUS_DIR = ORACLE_DIR / "corpus"

CONFORMANCE_DIR = REPO_ROOT / "conformance"
GEN_DIR = REPO_ROOT / "gen"
LEAN_DIR = REPO_ROOT / "lean"
TMP_DIR = REPO_ROOT / "tmp"


def oracle_cache() -> Path:
    """Directory holding the downloaded pcre2 tarball and the builds made from it.

    Builds are keyed by the pin contents, so several of them can coexist and
    switching pins never reuses stale objects.
    """
    override = os.environ.get("PCRETRUSTE_ORACLE_CACHE")
    return Path(override) if override else TMP_DIR / "oracle"
