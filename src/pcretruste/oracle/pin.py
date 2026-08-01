"""The pinned pcre2 reference build, as data.

Nothing in this module decides anything about pcre2; it only reads
oracle/pcre2-pin.toml and hands the record to the builder and to the checks.
The pin file's own digest is part of the build key, so editing the pin always
produces a fresh build directory instead of reusing objects from the old one.
"""

from __future__ import annotations

import hashlib
import tomllib
from dataclasses import dataclass
from pathlib import Path

from ..paths import PIN_PATH

SCHEMA = 1

NEWLINE_CODES = {
    1: "CR",
    2: "LF",
    3: "CRLF",
    4: "ANY",
    5: "ANYCRLF",
    6: "NUL",
}

BSR_CODES = {
    1: "UNICODE",
    2: "ANYCRLF",
}

# Checked field by field against pcre2_config(), by name.
NUMERIC_FIELDS = (
    "unicode",
    "jit",
    "link_size",
    "effective_link_size",
    "parens_nest_limit",
    "match_limit",
    "depth_limit",
    "heap_limit",
    "never_backslash_c",
    "compiled_widths",
    "tables_length",
)


@dataclass(frozen=True)
class Limits:
    """What the harness asks pcre2 to enforce on every match."""

    match_limit: int
    depth_limit: int
    heap_limit_kib: int

    def shim_arguments(self) -> list[str]:
        return [
            f"--match-limit={self.match_limit}",
            f"--depth-limit={self.depth_limit}",
            f"--heap-limit={self.heap_limit_kib}",
        ]


@dataclass(frozen=True)
class Pin:
    path: Path
    digest: str
    version: str
    release_tag: str
    tarball: str
    url: str
    sha256: str
    chartables_source: str
    chartables_source_sha256: str
    cflags: str
    configure: tuple[str, ...]
    make_target: str
    library: str
    include_dir: str
    expect: dict[str, object]
    limits: Limits

    @property
    def source_directory(self) -> str:
        """The directory name the release tarball unpacks into."""
        return f"pcre2-{self.version}"


# Every section of the pin is a closed, typed set of fields. A pin is a
# statement about a build, so a key nothing reads is not a harmless extra: it
# reads as pinned while pinning nothing, which is the failure mode this whole
# file exists to prevent. Coercion is out for the same reason: `sha256 = 47` is
# a mistake, not a number to be turned into a string.
SOURCE_FIELDS: dict[str, type | tuple[type, ...]] = {
    "version": str,
    "release_tag": str,
    "tarball": str,
    "url": str,
    "sha256": str,
    "chartables_source": str,
    "chartables_source_sha256": str,
}

BUILD_FIELDS: dict[str, type | tuple[type, ...]] = {
    "cflags": str,
    "configure": list,
    "make_target": str,
    "library": str,
    "include_dir": str,
}

LIMIT_FIELDS: dict[str, type | tuple[type, ...]] = {
    "match_limit": int,
    "depth_limit": int,
    "heap_limit_kib": int,
}

EXPECT_TYPES: dict[str, type | tuple[type, ...]] = {
    "version_prefix": str,
    "unicode_version": str,
    "newline": str,
    "bsr": str,
    "tables_sha256": str,
    "unicode": int,
    "jit": int,
    "link_size": int,
    "effective_link_size": int,
    "parens_nest_limit": int,
    "match_limit": int,
    "depth_limit": int,
    "heap_limit": int,
    "never_backslash_c": int,
    "compiled_widths": int,
    "tables_length": int,
}

TOP_LEVEL_SECTIONS = ("source", "build", "expect", "limits")


def _check_section(
    table: object, section: str, fields: dict[str, type | tuple[type, ...]]
) -> dict[str, object]:
    if not isinstance(table, dict):
        raise ValueError(f"pin section [{section}] is missing")

    missing = [key for key in fields if key not in table]
    if missing:
        raise ValueError(f"pin section [{section}] is missing: {', '.join(missing)}")
    unknown = [key for key in table if key not in fields]
    if unknown:
        raise ValueError(
            f"pin section [{section}] has fields nothing reads: {', '.join(sorted(unknown))}"
        )
    for key, wanted in fields.items():
        value = table[key]
        # bool is an int in Python and never what a pin means by one.
        if isinstance(value, bool) or not isinstance(value, wanted):
            raise ValueError(
                f"[{section}].{key} must be {getattr(wanted, '__name__', wanted)}, got {value!r}"
            )
    return table


def load(path: Path = PIN_PATH) -> Pin:
    raw_bytes = path.read_bytes()
    raw = tomllib.loads(raw_bytes.decode("utf-8"))

    # Not `!= SCHEMA`: in Python `True` and `1.0` both equal 1, and neither is
    # a schema number.
    schema = raw.get("schema")
    if type(schema) is not int or schema != SCHEMA:
        raise ValueError(f"pin schema {schema!r} is not the expected {SCHEMA}")
    unknown = set(raw) - {"schema", *TOP_LEVEL_SECTIONS}
    if unknown:
        raise ValueError(f"pin has sections nothing reads: {', '.join(sorted(unknown))}")

    source = _check_section(raw.get("source"), "source", SOURCE_FIELDS)
    build = _check_section(raw.get("build"), "build", BUILD_FIELDS)
    expect = _check_section(raw.get("expect"), "expect", EXPECT_TYPES)
    limits = _check_section(raw.get("limits"), "limits", LIMIT_FIELDS)

    if not all(isinstance(flag, str) for flag in build["configure"]):
        raise ValueError("[build].configure must be a list of flags")
    if not build["configure"]:
        raise ValueError("a pin with no configure flags pins nothing")

    return Pin(
        path=path,
        digest=hashlib.sha256(raw_bytes).hexdigest(),
        version=source["version"],
        release_tag=source["release_tag"],
        tarball=source["tarball"],
        url=source["url"],
        sha256=source["sha256"],
        chartables_source=source["chartables_source"],
        chartables_source_sha256=source["chartables_source_sha256"],
        cflags=build["cflags"],
        configure=tuple(build["configure"]),
        make_target=build["make_target"],
        library=build["library"],
        include_dir=build["include_dir"],
        expect=dict(expect),
        # LIMIT_FIELDS is exactly Limits' fields, and the section has just been
        # checked against it, so there is nothing left to spell out.
        limits=Limits(**limits),
    )


def check_configuration(observed: dict[str, object], pin: Pin) -> list[str]:
    """Compare a shim ``config`` response with the pin, field by field.

    Returns one human-readable line per disagreement, so a caller can report
    every problem at once instead of the first one. An empty list means the
    linked library really is the reference build.
    """
    problems: list[str] = []
    expect = pin.expect

    def text_of(key: str) -> str:
        value = observed.get(key)
        return value.decode("ascii", "replace") if isinstance(value, bytes) else repr(value)

    version = text_of("version")
    prefix = expect["version_prefix"]
    if not version.startswith(str(prefix)):
        problems.append(f"version: pcre2 reports {version!r}, pin expects a {prefix!r} build")

    unicode_version = text_of("unicode_version")
    if unicode_version != expect["unicode_version"]:
        problems.append(
            f"unicode_version: pcre2 reports {unicode_version!r}, "
            f"pin expects {expect['unicode_version']!r}"
        )

    for key in NUMERIC_FIELDS:
        actual = observed.get(key)
        if actual != expect[key]:
            problems.append(f"{key}: pcre2 reports {actual!r}, pin expects {expect[key]!r}")

    for key, codes in (("newline", NEWLINE_CODES), ("bsr", BSR_CODES)):
        code = observed.get(key)
        name = codes.get(code) if isinstance(code, int) else None
        if name != expect[key]:
            problems.append(
                f"{key}: pcre2 reports {name or code!r}, pin expects {expect[key]!r}"
            )

    applied = {
        "applied_match_limit": pin.limits.match_limit,
        "applied_depth_limit": pin.limits.depth_limit,
        "applied_heap_limit": pin.limits.heap_limit_kib,
    }
    for key, wanted in applied.items():
        if observed.get(key) != wanted:
            problems.append(
                f"{key}: harness applies {observed.get(key)!r}, pin expects {wanted!r}"
            )

    tables = observed.get("tables")
    wanted_tables = expect["tables_sha256"]
    if not isinstance(tables, bytes):
        problems.append("tables: the shim did not report the default tables")
    else:
        digest = hashlib.sha256(tables).hexdigest()
        if digest != wanted_tables:
            problems.append(
                f"tables: linked library uses tables with sha256 {digest}, "
                f"pin expects {wanted_tables}"
            )

    return problems
