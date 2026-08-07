"""The generator's own source closure, computed rather than listed.

A capsule promises that the artifact in it can be rebuilt from the bytes beside
it. That promise is only as good as the file list, and a hand-maintained list of
"the files that matter" is exactly the thing that goes stale: a helper module
added on a Tuesday is in the build and not in the manifest, and every hash in
the manifest still checks out.

So the list is derived. Start at the module the capsule's build entry names,
read its imports, and follow the ones that resolve inside this repository until
nothing new appears. Reading rather than running is deliberate: an import taken
only on some code path belongs to the closure just as much as one taken on
every path, and a runtime trace would miss it.
"""

from __future__ import annotations

import ast
from pathlib import Path

PACKAGE = "pcrevera"

BUILD_METADATA = ("pyproject.toml", "uv.lock")
"""Two files the closure has no import edge to and cannot honestly leave out:
the project definition and the locked dependency set. `generator.lockSha256`
pins the second one again by itself, which is the redundancy the verifier
joins."""


class SourceError(ValueError):
    """An import the closure cannot resolve to a file it can hash."""


def _module_path(root: Path, module: str) -> Path | None:
    """Where a dotted module name lives under `src/`, or None if it is not ours."""
    if module != PACKAGE and not module.startswith(PACKAGE + "."):
        return None
    parts = module.split(".")
    base = root / "src" / Path(*parts)
    if base.is_dir():
        return base / "__init__.py"
    plain = base.with_suffix(".py")
    return plain if plain.is_file() else None


def _resolve(module: str, level: int, name: str | None, package: str) -> str:
    """The absolute module name an `import` line refers to.

    `level` is the number of leading dots, so `from ..engine import spec` inside
    `pcrevera.backends.go` is level 2 with `package` `pcrevera.backends.go`.
    """
    if level == 0:
        return module
    parts = package.split(".")
    if level > len(parts):
        raise SourceError(f"{package}: a relative import climbs past {PACKAGE}")
    base = ".".join(parts[: len(parts) - level + 1])
    tail = module or name or ""
    return f"{base}.{tail}" if tail else base


def _imports(source: str, module: str, is_package: bool) -> set[str]:
    """Every module name a source file imports, made absolute.

    `from . import x` is the awkward case: `x` may be a submodule or a name the
    package's `__init__` defines. Both spellings are emitted and the caller
    keeps whichever resolves to a file, which is what the interpreter does too.
    """
    package = module if is_package else module.rsplit(".", 1)[0]
    found: set[str] = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Import):
            for alias in node.names:
                found.add(alias.name)
        elif isinstance(node, ast.ImportFrom):
            base = _resolve(node.module or "", node.level, None, package)
            found.add(base)
            for alias in node.names:
                found.add(f"{base}.{alias.name}" if base else alias.name)
    return found


def closure(entry: str, root: Path) -> list[str]:
    """Every repository-local module the entry reaches, as logical paths.

    The build metadata is appended, and the whole thing is sorted so two
    machines that walk the graph in different orders still write one manifest.
    """
    seen: dict[str, Path] = {}
    pending = [entry]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = _module_path(root, module)
        if path is None:
            continue
        if not path.is_file():
            raise SourceError(f"{module} resolves to {path}, which is not a file")
        seen[module] = path
        is_package = path.name == "__init__.py"
        pending.extend(_imports(path.read_text(encoding="utf-8"), module, is_package))

    if entry not in seen:
        raise SourceError(f"{entry} is not a module of this repository")

    paths = {path.relative_to(root).as_posix() for path in seen.values()}
    for name in BUILD_METADATA:
        if not (root / name).is_file():
            raise SourceError(f"{name} is missing")
        paths.add(name)
    return sorted(paths)


__all__ = ["BUILD_METADATA", "PACKAGE", "SourceError", "closure"]
