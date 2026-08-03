"""Encoding and decoding for the pcre2shim line protocol.

The wire format is specified in oracle/README.md and implemented on the other
side by oracle/pcre2shim/shim.c. Byte payloads travel as ``<len>:<hex>`` so
that a pattern or a subject can hold any byte, and so that a line truncated in
transit fails to parse rather than turning into a shorter string.
"""

from __future__ import annotations

from collections.abc import Iterable

PROTOCOL_VERSION = 1

_OPTION_CHARS = set("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")


class ProtocolError(RuntimeError):
    """The shim said something the protocol does not allow."""


def encode_blob(data: bytes) -> str:
    return f"{len(data)}:{data.hex()}"


def decode_blob(token: str) -> bytes:
    count, separator, digits = token.partition(":")
    if not separator or not count.isdigit():
        raise ProtocolError(f"malformed payload: {token!r}")
    expected = int(count)
    if len(digits) != expected * 2:
        raise ProtocolError(
            f"payload declares {expected} bytes but carries {len(digits)} hex digits"
        )
    try:
        data = bytes.fromhex(digits)
    except ValueError as exc:
        raise ProtocolError(f"malformed payload: {token!r}") from exc
    return data


def _checked(name: str, what: str) -> str:
    if not name or not set(name) <= _OPTION_CHARS:
        raise ValueError(f"not {what}: {name!r}")
    return name


def encode_options(names: Iterable[str]) -> str:
    listed = tuple(names)
    if not listed:
        return "-"
    return ",".join(_checked(name, "an option name") for name in listed)


def encode_convention(name: str | None) -> str:
    """A newline or \\R convention, or ``-`` to keep the library default."""
    return "-" if name is None else _checked(name, "a convention name")
