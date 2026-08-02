"""Write the generated files, or check that the committed ones are current.

    python -m pcretruste.backends build     write them
    python -m pcretruste.backends verify    fail on any that has drifted

The generated Go and JavaScript are committed, so that a diff is reviewable
and the libraries are usable without running the generator. `verify` is what
keeps that honest: it regenerates everything in memory and refuses a checkout
where a committed file is not what today's generator produces.
"""

from __future__ import annotations

import sys

from ..paths import REPO_ROOT
from . import generate


def main(argv: list[str]) -> int:
    if len(argv) != 1 or argv[0] not in ("build", "verify"):
        print(__doc__, file=sys.stderr)
        return 2

    sha256, outputs = generate()
    if argv[0] == "build":
        for output in outputs:
            output.write()
            print(f"wrote {output.path.relative_to(REPO_ROOT)}")
        print(f"artifact sha256 {sha256}")
        return 0

    stale = [output for output in outputs if not output.matches()]
    for output in stale:
        where = output.path.relative_to(REPO_ROOT)
        missing = not output.path.exists()
        print(
            f"{where} is {'missing' if missing else 'not what the generator produces'}",
            file=sys.stderr,
        )
    if stale:
        print("run: make generate", file=sys.stderr)
        return 1
    print(f"the committed files match the generator, artifact sha256 {sha256}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
