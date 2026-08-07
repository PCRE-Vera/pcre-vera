"""The capsule manifest: what an artifact was built from, by content hash.

A manifest is a strict, closed document. Every field it may carry is declared
here, an unknown one is an error, a repeated JSON key is an error, and every
logical path is normalized and refused if it could escape the root a capsule
materializes into. Nothing in it names a place bytes are read from: a file is a
logical path and a digest, and the digest is where the blob store finds it.

Two roles exist. `proof-baseline` is the immutable capsule whose theorem
inventory has been checked — at M8's start, the completed M7 foundation.
`shipped` is what the Go and JavaScript backends actually consume. They are two
independent documents that may name the same blobs and may never depend on each
other.
"""

from __future__ import annotations

import json
import platform
import subprocess
from pathlib import Path

from ..paths import REPO_ROOT
from . import canonical, sha256_file
from .blobs import is_digest

SCHEMA = "pcrevera/manifest@1"

ROLES = ("proof-baseline", "shipped")

ORACLE_MODES = ("recorded-expectations",)
"""Capsule replay is offline by design. A live comparison belongs to
`make check`, the per-slice sweep or a pin refresh, so the only mode a manifest
may declare is the one that downloads nothing."""

ENVIRONMENT = {"PYTHONHASHSEED": "0", "LC_ALL": "C", "TZ": "UTC"}
"""The environment regeneration is required to reproduce under. Generator code
may not depend on hash-table iteration, locale or timezone, and pinning these
is how that rule stops being a promise."""

ENTRY = "pcrevera.backends"
"""The module whose `generate` writes every file the capsule records, and the
root of the source closure."""

ARTIFACT_PATH = "gen/engine.tir.json"
ARTIFACT_SCHEMA = "tir/1"

LEAN_ROOT = "Pcrevera"

BACKEND_FILES = {
    "go": ("gen/go/**/*.go", "gen/go/go.mod"),
    "javascript": (
        "gen/js/*.mjs",
        "gen/js/test/*.mjs",
        "gen/js/index.d.ts",
        "gen/js/package.json",
        "gen/js/package-lock.json",
    ),
}
"""What each backend is, spelled as patterns rather than walked, so that an
untracked scratch file in a working tree cannot join a capsule. A test holds
these to what the repository actually tracks."""

LEAN_FILES = (
    "lean/Pcrevera/**/*.lean",
    "lean/Pcrevera.lean",
    "lean/CorpusCheck.lean",
    "lean/lakefile.toml",
    "lean/lake-manifest.json",
    "lean/lean-toolchain",
)
"""The library, the replay executable and the three files lake reads. Named
rather than swept, because `lean/**` also holds a scratch directory and a
downloaded dependency, and neither belongs to a capsule."""

CORPORA = (
    "conformance/corpus.json",
    "conformance/certificates.json",
    "conformance/lowering.json",
    "conformance/migration.json",
    "conformance/sweep.json",
    "conformance/layer-i.json",
    "conformance/layer-i-strata.json",
    "gen/lean/bridge.json",
)

EXPECTATIONS = (
    "oracle/corpus/seed.json",
    "oracle/corpus/wave1.json",
    "oracle/corpus/sweep-regressions.json",
    "oracle/corpus/pre-lowering.json",
)

SHIM_FILES = ("oracle/pcre2shim/shim.c",)

PIN_PATH = "oracle/pcre2-pin.toml"

INVENTORY_PATH = "conformance/theorem-inventory.json"
LEDGER_PATH = "conformance/features.json"


class ManifestError(ValueError):
    """A manifest that is not one, with the field that broke it named."""


def normalized(logical: str) -> str:
    """A logical path, or a refusal.

    Refused: anything absolute, anything with a `..` or `.` component, a
    Windows separator, an empty component, or a trailing slash. Materialization
    joins these onto a build root, and a path that can climb out of that root is
    the one bug in a materializer nobody notices until it has overwritten
    something.
    """
    if not logical or logical != logical.strip():
        raise ManifestError(f"{logical!r} is not a logical path")
    if logical.startswith("/") or "\\" in logical or ":" in logical:
        raise ManifestError(f"{logical!r} is not a relative POSIX path")
    parts = logical.split("/")
    if any(part in ("", ".", "..") for part in parts):
        raise ManifestError(f"{logical!r} has an empty or relative component")
    return logical


def _pairs(items: list[tuple[str, object]]) -> dict:
    seen: dict[str, object] = {}
    for key, value in items:
        if key in seen:
            raise ManifestError(f"the key {key!r} appears twice")
        seen[key] = value
    return seen


def loads(text: str) -> dict:
    """Parse a manifest, refusing a repeated key rather than keeping the last."""
    return json.loads(text, object_pairs_hook=_pairs)


def _need(where: dict, name: str, want: type | tuple[type, ...], path: str) -> object:
    if name not in where:
        raise ManifestError(f"{path}{name} is missing")
    value = where[name]
    if isinstance(value, bool) and want is not bool:
        raise ManifestError(f"{path}{name} is a Boolean")
    if not isinstance(value, want):
        raise ManifestError(f"{path}{name} has the wrong type")
    return value


def _closed(where: dict, allowed: set[str], path: str) -> None:
    extra = set(where) - allowed
    if extra:
        raise ManifestError(f"{path} has unknown fields: {', '.join(sorted(extra))}")


def _filemap(where: dict, name: str, path: str) -> dict[str, str]:
    value = _need(where, name, dict, path)
    out: dict[str, str] = {}
    for logical, digest in value.items():
        if not isinstance(digest, str) or not is_digest(digest):
            raise ManifestError(f"{path}{name}[{logical!r}] is not a sha256")
        out[normalized(logical)] = digest
    return out


def validate(document: object) -> dict[str, str]:
    """Every rule a manifest obeys, and the file closure it declares.

    The return value is the closure: logical path to digest, over every section
    that names files. A path may appear once and once only, across all of them,
    because two sections claiming one path with two hashes is a document that
    does not say what the capsule holds.
    """
    if not isinstance(document, dict):
        raise ManifestError("the manifest is not an object")
    _closed(
        document,
        {
            "schema", "manifestVersion", "capsuleName", "role", "artifactVersion",
            "artifact", "generator", "backends", "lean", "inventory",
            "featureLedger", "features", "compileCapabilities", "corpora",
            "sweep", "oracle",
        },
        "the manifest",
    )
    if document.get("schema") != SCHEMA:
        raise ManifestError(f"the manifest is not {SCHEMA}")
    if _need(document, "manifestVersion", int, "") < 1:
        raise ManifestError("manifestVersion is not a version")
    name = _need(document, "capsuleName", str, "")
    if not name or name != normalized(name) or "/" in name:
        raise ManifestError("capsuleName is not a plain name")
    if _need(document, "role", str, "") not in ROLES:
        raise ManifestError(f"role is not one of {', '.join(ROLES)}")
    if _need(document, "artifactVersion", int, "") < 1:
        raise ManifestError("artifactVersion is not a version")

    closure: dict[str, str] = {}

    def claim(logical: str, digest: str, where: str) -> None:
        logical = normalized(logical)
        if not is_digest(digest):
            raise ManifestError(f"{where} names a digest that is not a sha256")
        if logical in closure:
            raise ManifestError(f"{logical} is claimed twice, once by {where}")
        closure[logical] = digest

    artifact = _need(document, "artifact", dict, "")
    _closed(artifact, {"logicalPath", "sha256", "schema"}, "artifact")
    claim(
        _need(artifact, "logicalPath", str, "artifact."),
        _need(artifact, "sha256", str, "artifact."),
        "artifact",
    )
    if _need(artifact, "schema", str, "artifact.") != ARTIFACT_SCHEMA:
        raise ManifestError(f"artifact.schema is not {ARTIFACT_SCHEMA}")

    generator = _need(document, "generator", dict, "")
    _closed(
        generator,
        {"implementation", "python", "lockSha256", "revision", "entry",
         "sourceFiles", "environment"},
        "generator",
    )
    for field in ("implementation", "python", "revision", "entry"):
        if not _need(generator, field, str, "generator."):
            raise ManifestError(f"generator.{field} is empty")
    if not is_digest(_need(generator, "lockSha256", str, "generator.")):
        raise ManifestError("generator.lockSha256 is not a sha256")
    environment = _need(generator, "environment", dict, "generator.")
    if environment != ENVIRONMENT:
        raise ManifestError("generator.environment is not the fixed one")
    for logical, digest in _filemap(generator, "sourceFiles", "generator.").items():
        claim(logical, digest, "generator.sourceFiles")
    if "uv.lock" not in generator["sourceFiles"]:
        raise ManifestError("generator.sourceFiles does not carry uv.lock")
    if generator["sourceFiles"]["uv.lock"] != generator["lockSha256"]:
        raise ManifestError("generator.lockSha256 is not the uv.lock it lists")

    backends = _need(document, "backends", dict, "")
    _closed(backends, set(BACKEND_FILES), "backends")
    for language in BACKEND_FILES:
        for logical, digest in _filemap(backends, language, "backends.").items():
            claim(logical, digest, f"backends.{language}")

    lean = _need(document, "lean", dict, "")
    _closed(lean, {"root", "toolchain", "files"}, "lean")
    if _need(lean, "root", str, "lean.") != LEAN_ROOT:
        raise ManifestError(f"lean.root is not {LEAN_ROOT}")
    if not _need(lean, "toolchain", str, "lean."):
        raise ManifestError("lean.toolchain is empty")
    for logical, digest in _filemap(lean, "files", "lean.").items():
        claim(logical, digest, "lean.files")

    for section, wanted in (("inventory", INVENTORY_PATH), ("featureLedger", LEDGER_PATH)):
        held = _need(document, section, dict, "")
        _closed(held, {"path", "sha256"}, section)
        given = _need(held, "path", str, f"{section}.")
        if given != wanted:
            raise ManifestError(f"{section}.path is not {wanted}")
        claim(given, _need(held, "sha256", str, f"{section}."), section)

    sets = _need(document, "features", dict, "")
    _closed(sets, {"default", "gated", "unsupported"}, "features")
    seen: set[str] = set()
    for kind in ("default", "gated", "unsupported"):
        values = _need(sets, kind, list, "features.")
        if any(not isinstance(v, str) for v in values):
            raise ManifestError(f"features.{kind} holds something that is not a key")
        if sorted(values) != values or len(set(values)) != len(values):
            raise ManifestError(f"features.{kind} is unsorted or repeats")
        if seen & set(values):
            raise ManifestError(f"features.{kind} overlaps another set")
        seen |= set(values)

    masks = _need(document, "compileCapabilities", dict, "")
    _closed(masks, {"default", "gated"}, "compileCapabilities")
    for kind in ("default", "gated"):
        values = _need(masks, kind, list, "compileCapabilities.")
        if any(not isinstance(v, str) for v in values):
            raise ManifestError(f"compileCapabilities.{kind} is not a list of names")
        if sorted(values) != values or len(set(values)) != len(values):
            raise ManifestError(f"compileCapabilities.{kind} is unsorted or repeats")
    if not set(masks["default"]) <= set(masks["gated"]):
        raise ManifestError("the default capability mask is not inside the gated one")

    for logical, digest in _filemap(document, "corpora", "").items():
        claim(logical, digest, "corpora")

    sweep = _need(document, "sweep", dict, "")
    _closed(sweep, {"manifestSha256", "command"}, "sweep")
    if not is_digest(_need(sweep, "manifestSha256", str, "sweep.")):
        raise ManifestError("sweep.manifestSha256 is not a sha256")
    if not _need(sweep, "command", str, "sweep."):
        raise ManifestError("sweep.command is empty")

    oracle = _need(document, "oracle", dict, "")
    _closed(
        oracle,
        {"mode", "pinPath", "pinSha256", "version", "buildId", "shimFiles",
         "expectations"},
        "oracle",
    )
    if _need(oracle, "mode", str, "oracle.") not in ORACLE_MODES:
        raise ManifestError("oracle.mode is not an offline mode")
    if _need(oracle, "pinPath", str, "oracle.") != PIN_PATH:
        raise ManifestError(f"oracle.pinPath is not {PIN_PATH}")
    claim(oracle["pinPath"], _need(oracle, "pinSha256", str, "oracle."), "oracle.pin")
    for field in ("version", "buildId"):
        if not _need(oracle, field, str, "oracle."):
            raise ManifestError(f"oracle.{field} is empty")
    for section in ("shimFiles", "expectations"):
        for logical, digest in _filemap(oracle, section, "oracle.").items():
            claim(logical, digest, f"oracle.{section}")
    if not oracle["shimFiles"] or not oracle["expectations"]:
        raise ManifestError("oracle names no shim source or no expectations")

    return closure


def digest(document: dict) -> str:
    """The manifest's own identity, over its canonical bytes.

    Deliberately not written into any file the manifest hashes: a document that
    contained its own hash could not be hashed.
    """
    from . import sha256_bytes

    return sha256_bytes(canonical(document).encode("utf-8"))


def load(path: Path) -> tuple[dict, dict[str, str]]:
    text = path.read_text(encoding="utf-8")
    document = loads(text)
    if canonical(document) != text:
        raise ManifestError(f"{path} is not in canonical form")
    return document, validate(document)


def _matching(patterns: tuple[str, ...], root: Path) -> list[str]:
    """The files a section's patterns name, sorted, each one required to exist.

    A dotted component is skipped: `lean/**/*.lean` would otherwise reach into
    `.lake/packages` and pull batteries' two hundred and fifty-four modules into
    the capsule, which is a downloaded dependency the toolchain and
    `lake-manifest.json` already pin.
    """
    found: set[str] = set()
    for pattern in patterns:
        if "*" in pattern:
            found |= {
                path.relative_to(root).as_posix()
                for path in root.glob(pattern)
                if path.is_file()
                and not any(part.startswith(".") for part in path.relative_to(root).parts)
            }
        else:
            if not (root / pattern).is_file():
                raise ManifestError(f"{pattern} is missing")
            found.add(pattern)
    return sorted(found)


def _hashes(paths: list[str], root: Path) -> dict[str, str]:
    return {path: sha256_file(root / path) for path in paths}


def oracle_identity(root: Path) -> str:
    """A deterministic id for the oracle a capsule's expectations came from.

    Deliberately not `oracle.build.build_id`, which mixes in the local C
    compiler's version banner: that is the right key for a build directory and
    the wrong one for a manifest, because it would make the same capsule cut
    two different documents on two machines. A capsule never rebuilds pcre2 —
    it replays recorded answers — so what identifies its oracle is the pin, the
    shim and the recipe that turned them into a library.
    """
    from . import sha256_bytes

    parts = [
        sha256_file(root / PIN_PATH),
        *(sha256_file(root / name) for name in SHIM_FILES),
        sha256_file(root / "src" / "pcrevera" / "oracle" / "build.py"),
    ]
    return sha256_bytes("\0".join(parts).encode("ascii"))[:16]


def campaign(root: Path) -> tuple[str, str]:
    """The closing campaign's command and manifest hash, read off the record.

    `THEOREMS.md` is where the milestone's campaign is written down, and the
    hash is rebuilt from the recorded command rather than copied beside it, so
    a document whose command and hash disagree cannot cut a capsule at all.
    """
    import re

    from ..sweep import manifest as sweep

    text = (root / "THEOREMS.md").read_text(encoding="utf-8")
    written = re.search(r'make sweep SWEEP="(.*?)"', text, re.DOTALL)
    recorded = re.search(r"manifest sha256\s+([0-9a-f]{64})", text)
    if written is None or recorded is None:
        raise ManifestError("THEOREMS.md no longer records the closing campaign")
    words = written.group(1).replace("\\\n", " ").split()
    asked = dict(zip(words[::2], words[1::2]))
    rebuilt = sweep.digest(
        sweep.build(
            int(asked["--seed"]),
            structured=int(asked["--structured"]),
            hostile=int(asked["--hostile"]),
            subjects=int(asked["--subjects"]),
        )
    )
    if rebuilt != recorded.group(1):
        raise ManifestError("the recorded campaign command does not build its hash")
    return written.group(0), rebuilt


def revision(root: Path) -> str:
    """The commit this capsule was cut from, or `unknown` off a checkout.

    Provenance and never a substitute for the hashes above it: everything the
    verifier checks, it checks against bytes.
    """
    try:
        done = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True
        )
    except OSError:
        return "unknown"
    return done.stdout.strip() if done.returncode == 0 else "unknown"


def build(
    *,
    capsule_name: str,
    role: str,
    artifact_version: int,
    manifest_version: int = 1,
    root: Path = REPO_ROOT,
) -> dict:
    """A manifest for the live tree, every hash computed from the file it names."""
    from ..oracle import pin as pinning
    from . import features
    from .sources import closure

    sweep_command, sweep_manifest_sha256 = campaign(root)
    ledger = features.load(root / LEDGER_PATH)
    sets = features.sets(ledger)
    masks = features.capability_masks(ledger)

    document = {
        "schema": SCHEMA,
        "manifestVersion": manifest_version,
        "capsuleName": capsule_name,
        "role": role,
        "artifactVersion": artifact_version,
        "artifact": {
            "logicalPath": ARTIFACT_PATH,
            "sha256": sha256_file(root / ARTIFACT_PATH),
            "schema": ARTIFACT_SCHEMA,
        },
        "generator": {
            "implementation": "python",
            "python": platform.python_version(),
            "lockSha256": sha256_file(root / "uv.lock"),
            "revision": revision(root),
            "entry": ENTRY,
            "sourceFiles": _hashes(closure(ENTRY, root), root),
            "environment": dict(ENVIRONMENT),
        },
        "backends": {
            language: _hashes(_matching(patterns, root), root)
            for language, patterns in BACKEND_FILES.items()
        },
        "lean": {
            "root": LEAN_ROOT,
            "toolchain": (root / "lean" / "lean-toolchain").read_text().strip(),
            "files": _hashes(_matching(LEAN_FILES, root), root),
        },
        "inventory": {
            "path": INVENTORY_PATH,
            "sha256": sha256_file(root / INVENTORY_PATH),
        },
        "featureLedger": {
            "path": LEDGER_PATH,
            "sha256": sha256_file(root / LEDGER_PATH),
        },
        "features": sets,
        "compileCapabilities": masks,
        "corpora": _hashes(list(CORPORA), root),
        "sweep": {
            "manifestSha256": sweep_manifest_sha256,
            "command": sweep_command,
        },
        "oracle": {
            "mode": "recorded-expectations",
            "pinPath": PIN_PATH,
            "pinSha256": sha256_file(root / PIN_PATH),
            "version": pinning.load(root / PIN_PATH).version,
            "buildId": oracle_identity(root),
            "shimFiles": _hashes(list(SHIM_FILES), root),
            "expectations": _hashes(list(EXPECTATIONS), root),
        },
    }
    validate(document)
    return document


MANIFEST_DIR = REPO_ROOT / "proofs" / "manifests"


def filename(document: dict) -> str:
    """What a manifest is called: its capsule and its revision, never a date."""
    return f"{document['capsuleName']}.v{document['manifestVersion']}.json"


__all__ = [
    "ARTIFACT_PATH",
    "ARTIFACT_SCHEMA",
    "BACKEND_FILES",
    "CORPORA",
    "ENTRY",
    "ENVIRONMENT",
    "EXPECTATIONS",
    "INVENTORY_PATH",
    "LEAN_FILES",
    "LEAN_ROOT",
    "LEDGER_PATH",
    "MANIFEST_DIR",
    "ORACLE_MODES",
    "PIN_PATH",
    "ROLES",
    "SCHEMA",
    "SHIM_FILES",
    "ManifestError",
    "build",
    "campaign",
    "digest",
    "filename",
    "load",
    "loads",
    "normalized",
    "oracle_identity",
    "revision",
    "validate",
]
