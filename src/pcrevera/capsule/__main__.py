"""Capsule tooling from the command line.

    python -m pcrevera.capsule inventory-check       hold the inventory to Lean
    python -m pcrevera.capsule cut NAME ROLE VER [REV]   write a capsule
    python -m pcrevera.capsule verify MANIFEST...    check capsules, in order

`inventory-check` needs the Lean package built, because it elaborates against
the `.olean` files `lake build` leaves behind; it says so rather than passing
quietly when they are not there. `cut` reads the working tree and is the only
command that does. `verify` reads the manifests it is given and the blob store,
and touches the checkout once at the end, to require that a shipped capsule is
what the backends actually consume.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

from ..paths import REPO_ROOT
from ..tir import serialize
from . import inventory, leancheck
from .cut import cut
from .manifest import ManifestError
from .verify import VerifyError, verify


def inventory_check() -> int:
    """Two questions, and the second is worth nothing without the first.

    Is the committed inventory the one today's sources produce — which catches
    a changed proof whose recorded hash did not move — and does Lean agree
    that every name in it exists and rests on the three axioms.
    """
    if not leancheck.built():
        print("the Lean package is not built; run make lean first", file=sys.stderr)
        return 2
    artifact = REPO_ROOT / "gen" / "engine.tir.json"
    program = serialize.loads(artifact.read_text())
    current = inventory.render(
        inventory.build(program, hashlib.sha256(artifact.read_bytes()).hexdigest())
    )
    if inventory.PATH.read_text(encoding="utf-8") != current:
        print(
            f"{inventory.PATH.name} is not what the sources produce; "
            "run make generate",
            file=sys.stderr,
        )
        return 1
    try:
        reported = leancheck.run(json.loads(current))
    except leancheck.CheckError as failure:
        print(failure, file=sys.stderr)
        return 1
    print(f"lean confirms {len(reported)} inventory declarations")
    return 0


def cut_capsule(argv: list[str]) -> int:
    name, role, version = argv[0], argv[1], int(argv[2])
    revision = int(argv[3]) if len(argv) == 4 else 1
    try:
        path, digest = cut(
            capsule_name=name,
            role=role,
            artifact_version=version,
            manifest_version=revision,
        )
    except (ManifestError, ValueError) as failure:
        print(failure, file=sys.stderr)
        return 1
    print(f"wrote {path.relative_to(REPO_ROOT)}")
    print(f"manifest sha256 {digest}")
    return 0


def verify_capsules(paths: list[str]) -> int:
    for name in paths:
        path = Path(name)
        try:
            report = verify(path)
        except (VerifyError, ManifestError) as failure:
            print(f"{path.name}: {failure}", file=sys.stderr)
            return 1
        print(f"{report.capsule} ({report.role}) manifest {report.manifest_sha256}")
        for step in report.steps:
            print(f"  {step}")
    return 0


def main(argv: list[str]) -> int:
    if argv == ["inventory-check"]:
        return inventory_check()
    if argv[:1] == ["cut"] and len(argv) in (4, 5):
        return cut_capsule(argv[1:])
    if argv[:1] == ["verify"] and len(argv) > 1:
        return verify_capsules(argv[1:])
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
