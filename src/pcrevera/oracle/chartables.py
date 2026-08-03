"""Reading pcre2's shipped character tables out of their C source.

The tables decide what `\\w`, `\\s`, `\\b`, the POSIX classes, and caseless
matching mean in byte mode, so the pin records them and the tests check them.
This parser exists for one job: comparing the tables the release ships against
the tables the linked library ended up using, which is a stronger statement
than either hash on its own.
"""

from __future__ import annotations

import re
from pathlib import Path

_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
_ARRAY_START = "default_tables)[] = {"


def parse(path: Path) -> bytes:
    """The bytes of `PRIV(default_tables)` as written in pcre2_chartables.c."""
    source = path.read_text()
    head, separator, rest = source.partition(_ARRAY_START)
    if not separator:
        raise ValueError(f"{path} does not declare PRIV(default_tables)")
    body, separator, _ = rest.partition("};")
    if not separator:
        raise ValueError(f"the table in {path} is not terminated")

    body = _COMMENT.sub(" ", body)
    values = [int(token, 0) for token in body.split(",") if token.strip()]
    if any(value < 0 or value > 255 for value in values):
        raise ValueError(f"{path} holds a value outside a byte")
    return bytes(values)
