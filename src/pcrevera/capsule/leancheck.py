"""Asking Lean about the inventory, rather than asking a regex.

The inventory resolves every claim to a fully qualified name by reading the
sources. That is enough to write the file down and not nearly enough to believe
it: a name read out of a source is a string, and what the claim asserts is that
Lean has a declaration by that name whose proof rests on the three axioms and
nothing else. This module elaborates a generated module that asks exactly that,
in the environment a built capsule leaves behind.

It is deliberately separate from `inventory.py`, which never runs anything.
"""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

from ..paths import LEAN_DIR
from . import inventory


class CheckError(RuntimeError):
    """Lean disagreed with the inventory."""


def built(lean_dir: Path = LEAN_DIR) -> bool:
    """Whether this Lean tree has been built, so importing it can work."""
    return (lean_dir / ".lake" / "build" / "lib" / "lean").is_dir()


def run(built_inventory: dict, lean_dir: Path = LEAN_DIR) -> dict[str, list[str]]:
    """Elaborate the inventory's names and return what each depends on.

    Raises on a name Lean does not have, on an elaboration error of any kind,
    on a name the report never mentions, and on any axiom outside the three
    Lean's own foundation provides.
    """
    source = inventory.elaboration_source(built_inventory)
    with tempfile.TemporaryDirectory() as scratch:
        path = Path(scratch) / "InventoryCheck.lean"
        path.write_text(source, encoding="utf-8")
        done = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=lean_dir,
            capture_output=True,
            text=True,
        )
    # Exit status alone is not the check. Lean reports an unknown constant as an
    # `error:` line, and a wrapper that swallowed the status would otherwise
    # leave a run that printed errors looking like a run that passed.
    if done.returncode != 0 or "error:" in done.stdout or done.stderr.strip():
        raise CheckError(
            "lean refused the inventory check:\n"
            + "\n".join(part for part in (done.stdout, done.stderr) if part.strip())
        )
    reported = inventory.axioms_used(done.stdout)

    wanted = [
        decl["lean"]
        for claim in built_inventory["claims"]
        for decl in claim["declarations"]
        if "lean" in decl
    ]
    missing = [name for name in wanted if name not in reported]
    if missing:
        raise CheckError(f"lean reported nothing about {', '.join(sorted(set(missing)))}")

    allowed = set(inventory.AXIOMS)
    beyond = sorted(
        {axiom for used in reported.values() for axiom in used} - allowed
    )
    if beyond:
        raise CheckError(f"axioms beyond the recorded three: {', '.join(beyond)}")
    return reported


__all__ = ["CheckError", "built", "run"]
