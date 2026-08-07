"""Verifying a capsule, from its own bytes and nothing else.

The eight steps of PLAN-M8.md section 4.3, in order, each one recomputing what
the manifest asserts rather than reading it. The working tree is touched twice
and only twice: once to read the manifest that was asked for, and once at the
end, for a shipped capsule, to require that the files the backends actually
consume are the bytes the capsule holds. Everything in between happens in a
materialized root built from the blob store.

Two capsules therefore verify independently. Sharing a blob is allowed and is
the whole point of the store; needing the other capsule's tree is not, and
there is no way to express it here.
"""

from __future__ import annotations

import json
import os
import platform
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

from ..paths import REPO_ROOT
from . import blobs, features, inventory, leancheck, manifest, materialize, sha256_file


class VerifyError(RuntimeError):
    """A capsule that does not check out, with the step that refused it named."""


@dataclass
class Report:
    capsule: str
    role: str
    manifest_sha256: str
    root: Path
    steps: list[str] = field(default_factory=list)

    def note(self, message: str) -> None:
        self.steps.append(message)


def _environment(root: Path) -> dict[str, str]:
    """The fixed environment every in-capsule run gets.

    The three variables the manifest pins, plus a bytecode ban so a run cannot
    leave a `__pycache__` behind and make the next materialization think the
    capsule has grown a file.
    """
    env = dict(os.environ)
    env.update(manifest.ENVIRONMENT)
    env["PYTHONPATH"] = str(root / "src")
    env["PCREVERA_ROOT"] = str(root)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("PCREVERA_ORACLE_CACHE", None)
    return env


def _python(root: Path, code: str, step: str) -> str:
    done = subprocess.run(
        [sys.executable, "-c", code],
        cwd=root,
        env=_environment(root),
        capture_output=True,
        text=True,
    )
    if done.returncode != 0:
        raise VerifyError(f"{step}: {(done.stderr or done.stdout).strip()}")
    return done.stdout


def _lake(root: Path, arguments: list[str], step: str) -> str:
    env = dict(os.environ)
    env.update(manifest.ENVIRONMENT)
    done = subprocess.run(
        ["lake", *arguments],
        cwd=root / "lean",
        env=env,
        capture_output=True,
        text=True,
    )
    if done.returncode != 0:
        raise VerifyError(f"{step}: {(done.stdout or done.stderr).strip()[-4000:]}")
    return done.stdout


ROUND_TRIP = """
import hashlib, pathlib
from pcrevera.tir import serialize
path = pathlib.Path("gen/engine.tir.json")
text = path.read_text()
program = serialize.loads(text)
printed = serialize.dumps(program)
assert printed == text, "the capsule's decoder does not print its artifact back"
print(hashlib.sha256(path.read_bytes()).hexdigest())
"""

REPLAY = """
from pcrevera.engine import Engine
from pcrevera.engine import migration
from pcrevera.oracle import corpus
from pcrevera.paths import CORPUS_DIR
from pcrevera.sweep import promote

# Each recorded expectation file is read by the reader that owns it, so a
# corrupted one fails as itself rather than as a stray key. Only the wave 1
# corpus is replayed through the engine: the seed corpus is the pcre2 doctrine
# corpus and holds cases outside the subset this engine claims, the sweep
# regressions are replayed by the Lean reference through conformance/sweep.json,
# and the pre-lowering record is what conformance/migration.json is regenerated
# from in step 8.
seed = corpus.load(CORPUS_DIR / "seed.json")
wave1 = corpus.load(CORPUS_DIR / "wave1.json")
kept = promote.regression_cases()
before = migration.before()

failures = corpus.check(Engine(), wave1)
if failures:
    raise SystemExit("wave1: " + "; ".join(
        f"{case.name}: {why}" for case, why in failures[:5]))
print(len(wave1.cases), len(seed.cases), len(kept), len(before["rows"]))
"""


REGENERATE = """
from pcrevera.backends import generate

# Run inside the capsule, against the capsule's own copies: PCREVERA_ROOT sends
# every path in the generator through the materialized root, so what `matches`
# compares is what the manifest names.
sha256, outputs = generate()
stale = sorted(str(out.path) for out in outputs if not out.matches())
if stale:
    raise SystemExit("the generator does not reproduce " + ", ".join(stale))
print(sha256, len(outputs))
"""


def _step_one(path: Path) -> tuple[dict, dict[str, str]]:
    document, closure = manifest.load(path)
    if path.name != manifest.filename(document):
        raise VerifyError(
            f"step 1: {path.name} holds a manifest called "
            f"{manifest.filename(document)}"
        )
    return document, closure


def _step_two(closure: dict[str, str], store: Path) -> None:
    for logical, digest in sorted(closure.items()):
        try:
            blobs.get(digest, store)
        except blobs.BlobError as failure:
            raise VerifyError(f"step 2: {logical}: {failure}") from None


def _step_two_oracle(root: Path, document: dict) -> None:
    """The oracle provenance, recomputed from the bytes the capsule carries.

    Hashing the pin catches an edited pin. It does not catch a *different* pin
    whose hash was updated to match, which is the shape a bad pin refresh
    takes, so the two fields derived from the pin are recomputed as well: the
    release the pin names, and the identity of the build its recorded answers
    came from.
    """
    from ..oracle import pin as pinning

    version = pinning.load(root / document["oracle"]["pinPath"]).version
    if version != document["oracle"]["version"]:
        raise VerifyError(
            f"step 2: the capsule's pin is pcre2 {version}, and the manifest "
            f"says {document['oracle']['version']}"
        )
    identity = manifest.oracle_identity(root)
    if identity != document["oracle"]["buildId"]:
        raise VerifyError(
            f"step 2: the capsule's oracle identity is {identity}, and the "
            f"manifest says {document['oracle']['buildId']}"
        )


def _step_two_backends(root: Path, document: dict) -> None:
    """Every generated backend file naming the artifact it was printed from.

    The printers stamp the artifact's hash into each header, so a backend left
    behind by a regenerated artifact is visible without running the generator.
    Step 8 would catch it too, four minutes later.
    """
    wanted = document["artifact"]["sha256"]
    for language in manifest.BACKEND_FILES:
        for logical in sorted(document["backends"][language]):
            if not logical.endswith((".go", ".mjs")):
                continue
            text = (root / logical).read_text(encoding="utf-8")
            if "Code generated from" in text and wanted not in text:
                raise VerifyError(
                    f"step 2: {logical} was printed from another artifact"
                )


def _step_three(root: Path, document: dict) -> None:
    found = _python(root, ROUND_TRIP, "step 3").strip()
    if found != document["artifact"]["sha256"]:
        raise VerifyError(
            f"step 3: the capsule's artifact hashes to {found}, and the "
            f"manifest says {document['artifact']['sha256']}"
        )


def _step_four(root: Path, document: dict) -> None:
    toolchain = (root / "lean" / "lean-toolchain").read_text().strip()
    if toolchain != document["lean"]["toolchain"]:
        raise VerifyError(f"step 4: the capsule pins {toolchain}, not the recorded one")
    _lake(root, ["build", "--no-cache"], "step 4")


INVENTORY = """
import hashlib, json, pathlib
from pcrevera.capsule import inventory
from pcrevera.tir import coverage, serialize

artifact = pathlib.Path(%r)
program = serialize.loads(artifact.read_text())
sha256 = hashlib.sha256(artifact.read_bytes()).hexdigest()

# Regenerated from the capsule's own sources and its own artifact. This is
# where a stale, invented or removed claim is caught, and it is deliberately
# cheaper than asking Lean: a source hash that no longer matches the module it
# names fails here, before anything is built.
current = inventory.render(inventory.build(program, sha256))
held = pathlib.Path(%r).read_text()
if held != current:
    raise SystemExit("the inventory is not what the capsule's sources produce")

graph = coverage.call_graph(program)
owed = coverage.reach(graph, coverage.ENTRIES, frozenset({coverage.PARSER_ROOT}))
print(json.dumps({"sha256": sha256, "domain": sorted(owed),
                  "opcodes": [e.variants for e in program.enums if e.name == "Op"][0]}))
"""


def _step_five_document(root: Path, document: dict) -> tuple[dict, dict]:
    """The inventory, held to the capsule's own sources and artifact.

    Everything here is cheap enough to run before the Lean build, which is what
    makes a tampered capsule fail in seconds rather than in minutes. What Lean
    adds afterwards is the one thing this cannot do: confirm that a name is a
    declaration the compiler accepts.
    """
    held = json.loads((root / document["inventory"]["path"]).read_text())
    if held["artifact"] != document["artifact"]["sha256"]:
        raise VerifyError("step 5: the inventory names another artifact")
    derived = json.loads(
        _python(
            root,
            INVENTORY % (manifest.ARTIFACT_PATH, document["inventory"]["path"]),
            "step 5",
        )
    )
    if derived["sha256"] != document["artifact"]["sha256"]:
        raise VerifyError(
            f"step 5: the capsule's artifact hashes to {derived['sha256']}, and "
            f"the manifest says {document['artifact']['sha256']}"
        )
    if derived["domain"] != sorted(held["layerI"]["domain"]):
        raise VerifyError(
            "step 5: the inventory's layer I domain is not the artifact's own"
        )
    return held, derived


def _step_five_lean(root: Path, held: dict) -> None:
    try:
        leancheck.run(held, root / "lean")
    except leancheck.CheckError as failure:
        raise VerifyError(f"step 5: {failure}") from None


def _step_six_document(root: Path, document: dict) -> dict:
    """The ledger, and the three sets and two masks the manifest repeats of it.

    The repetition is the point: the manifest is what a reader consults, the
    ledger is what generation consumes, and a capsule where they disagree is a
    capsule whose admission state depends on which one you read.
    """
    try:
        ledger = features.load(root / document["featureLedger"]["path"])
    except features.LedgerError as failure:
        raise VerifyError(f"step 6: {failure}") from None
    if features.sets(ledger) != document["features"]:
        raise VerifyError("step 6: the manifest's feature sets are not the ledger's")
    if features.capability_masks(ledger) != document["compileCapabilities"]:
        raise VerifyError("step 6: the manifest's capability masks are not the ledger's")
    return ledger


def _step_six(ledger: dict, held: dict, opcodes: list[str]) -> None:
    try:
        features.check_against_inventory(ledger, held)
    except features.LedgerError as failure:
        raise VerifyError(f"step 6: {failure}") from None

    known = set(opcodes)
    claimed: set[str] = set()
    for row in ledger["features"]:
        for mode in ("default", "gated"):
            for name in row["capabilities"][mode]:
                if name not in known:
                    raise VerifyError(f"step 6: {row['key']} claims a missing {name}")
                claimed.add(name)
    orphans = sorted(known - claimed)
    if orphans:
        raise VerifyError(f"step 6: no feature claims {', '.join(orphans)}")

    # The rule the default mask exists for, stated where it can name the row
    # that broke it: an opcode reaches the default surface only through a
    # feature whose chain is complete, or through wave 1's named fallback.
    for row in ledger["features"]:
        if not row["capabilities"]["default"]:
            continue
        if not features.admits(row):
            raise VerifyError(
                f"step 6: {row['key']} emits {', '.join(row['capabilities']['default'])}"
                " by default with an incomplete proof chain"
            )


def _step_seven(root: Path, document: dict) -> str:
    """Replay, offline, through the two engines the capsule names.

    The Python engine answers the recorded wave 1 expectations; the Lean
    reference compiles and runs the exported trees and compares bytecode,
    regions, ovector and usage. Neither reaches pcre2: what a capsule replays
    is what was recorded, and a live comparison belongs to `make check`.
    """
    expected = {Path(logical).name for logical in document["oracle"]["expectations"]}
    if expected != {Path(name).name for name in manifest.EXPECTATIONS}:
        raise VerifyError("step 7: the capsule records other expectations than these")
    counted = _python(root, REPLAY, "step 7").split()
    if len(counted) != 4 or any(not part.isdigit() or part == "0" for part in counted):
        raise VerifyError("step 7: a recorded expectation replayed nothing")
    if not document["corpora"]:
        raise VerifyError("step 7: the capsule records no corpora to replay")
    _lake(
        root,
        [
            "exe",
            "corpuscheck",
            str(root / "conformance" / "corpus.json"),
            str(root / "conformance" / "sweep.json"),
            str(root / "gen" / "lean" / "bridge.json"),
        ],
        "step 7",
    )
    return (
        f"{counted[0]} wave 1 cases through the engine, and "
        f"{counted[1]} seed, {counted[2]} regression and {counted[3]} migration "
        "rows read back"
    )


def _step_eight(root: Path, document: dict, closure: dict[str, str], live: Path) -> None:
    recorded = document["generator"]["python"]
    running = platform.python_version()
    if recorded != running:
        raise VerifyError(
            f"step 8: the capsule was generated by CPython {recorded} and this "
            f"is {running}; regeneration is not asked to hope"
        )
    regenerated = _python(root, REGENERATE, "step 8").split()
    if regenerated[0] != document["artifact"]["sha256"]:
        raise VerifyError(
            f"step 8: the generator produces {regenerated[0]}, and the capsule "
            f"holds {document['artifact']['sha256']}"
        )
    if document["role"] != "shipped":
        return
    generated = [document["artifact"]["logicalPath"]]
    for language in manifest.BACKEND_FILES:
        generated.extend(document["backends"][language])
    generated.extend(document["corpora"])
    generated.append(document["inventory"]["path"])
    behind = [
        logical
        for logical in sorted(generated)
        if not (live / logical).is_file()
        or sha256_file(live / logical) != closure[logical]
    ]
    if behind:
        raise VerifyError(
            "step 8: the shipped capsule and the checkout disagree on "
            + ", ".join(behind)
        )


def verify(
    path: Path,
    *,
    live: Path = REPO_ROOT,
    store: Path = blobs.STORE,
    under: Path = materialize.ROOTS,
) -> Report:
    """Run all eight obligations and return what was checked.

    The order is by cost rather than by number. Everything that can be decided
    from the capsule's documents and its artifact runs first, so a tampered
    capsule is refused in seconds; the Lean build, the replay and the
    regeneration follow, and each step's message says which obligation it
    discharged.
    """
    document, closure = _step_one(path)
    _step_two(closure, store)
    digest = manifest.digest(document)
    root = materialize.materialize(
        document["capsuleName"], digest, closure, under=under, store=store
    )
    report = Report(document["capsuleName"], document["role"], digest, root)
    report.note(f"{len(closure)} files materialized under {root}")

    held, derived = _step_five_document(root, document)
    report.note(f"{len(held['claims'])} inventory claims regenerated from the sources")
    _step_six(root, document, held, derived["opcodes"])
    report.note(
        f"{len(document['features']['default'])} default features and "
        f"{len(document['compileCapabilities']['default'])} default capabilities"
    )
    _step_three(root, document)
    report.note("the artifact decodes and prints back to its own bytes")

    materialize.lean_dependencies(root)
    _step_four(root, document)
    report.note(f"the Lean package builds under {document['lean']['toolchain']}")
    _step_five_lean(root, held)
    report.note("lean confirms every declaration the inventory names")
    report.note(_step_seven(root, document))
    _step_eight(root, document, closure, live)
    report.note("the generator reproduces the capsule byte for byte")
    return report


__all__ = ["Report", "VerifyError", "verify"]
