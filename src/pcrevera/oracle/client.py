"""Driving the pcre2 oracle from Python.

One shim process serves any number of requests, so the cost of starting it is
paid once per test session. Every outcome pcre2 can produce is a distinct
value here: a match with its ovector, no match, a compile error with its code
and byte offset, or a match-time error. Nothing collapses into None, because
telling "no match" apart from "the harness gave up" is the whole point.
"""

from __future__ import annotations

import subprocess
import threading
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from types import TracebackType

from .pin import Limits
from .protocol import (
    PROTOCOL_VERSION,
    ProtocolError,
    decode_blob,
    encode_blob,
    encode_convention,
    encode_options,
)

UNSET = -1

# How long a single request may take. Generous, because a pathological pattern
# under the pinned match limit can genuinely take a second or two; finite,
# because a shim that stops answering while holding its pipes open would
# otherwise wedge a whole fuzzing run with no way out.
DEFAULT_TIMEOUT_SECONDS = 120.0


def _shaped(fields: list[str], kind: str, *, exactly: int | None = None,
            at_least: int | None = None) -> list[str]:
    """Insist a response is the kind and the arity it is supposed to be."""
    if fields[0] != kind:
        raise ProtocolError(f"expected a {kind} response, got {fields!r}")
    if exactly is not None and len(fields) != exactly:
        raise ProtocolError(f"a {kind} response has {exactly} fields, got {fields!r}")
    if at_least is not None and len(fields) < at_least:
        raise ProtocolError(f"a {kind} response has at least {at_least} fields, got {fields!r}")
    return fields


def _integer(token: str, what: str) -> int:
    try:
        return int(token)
    except ValueError as exc:
        raise ProtocolError(f"{what} is not a number: {token!r}") from exc


def _check_ovector(offsets: tuple[int, ...], subject_length: int) -> None:
    """Reject an ovector pcre2 could not have produced.

    A damaged response must be an error rather than a differential-test fact.
    The one thing deliberately not checked is start <= end: \\K can legitimately
    move a match's start past its end.
    """
    if offsets[0] == UNSET or offsets[1] == UNSET:
        raise ProtocolError("a match whose own offsets are unset")
    for index in range(0, len(offsets), 2):
        start, end = offsets[index], offsets[index + 1]
        group = index // 2
        if (start == UNSET) != (end == UNSET):
            raise ProtocolError(f"group {group} is half unset: {start}, {end}")
        if start == UNSET:
            continue
        if start < 0 or end < 0 or start > subject_length or end > subject_length:
            raise ProtocolError(
                f"group {group} lies outside a {subject_length} byte subject: {start}, {end}"
            )


class _Watchdog:
    """Kills a process that has stopped taking part, once the clock runs out.

    A small object rather than a closure, so the timer thread holds a process
    and a flag rather than the whole frame of the request it is guarding.
    """

    def __init__(self, process: subprocess.Popen[str], timeout: float) -> None:
        self._process = process
        self._settled = threading.Lock()
        self._done = False
        self.expired = False
        self._timer = threading.Timer(timeout, self._give_up)
        self._timer.start()

    def _give_up(self) -> None:
        with self._settled:
            if self._done:
                return
            self.expired = True
            self._process.kill()

    def stop(self) -> bool:
        """Stand down, and say whether the clock had already run out."""
        with self._settled:
            self._done = True
        self._timer.cancel()
        return self.expired


class OracleError(RuntimeError):
    """The shim failed, rather than reporting a pcre2 outcome."""


@dataclass(frozen=True)
class Match:
    """A successful match: byte offset pairs, one per group, -1 when unset."""

    ovector: tuple[int, ...]

    @property
    def span(self) -> tuple[int, int]:
        return self.ovector[0], self.ovector[1]

    @property
    def group_count(self) -> int:
        return len(self.ovector) // 2 - 1

    def group(self, index: int) -> tuple[int, int]:
        return self.ovector[2 * index], self.ovector[2 * index + 1]


@dataclass(frozen=True)
class NoMatch:
    pass


@dataclass(frozen=True)
class CompileError:
    code: int
    offset: int
    message: str


@dataclass(frozen=True)
class MatchError:
    code: int
    message: str


@dataclass(frozen=True)
class Compiled:
    capture_count: int
    names: tuple[tuple[bytes, int], ...]


MatchOutcome = Match | NoMatch | CompileError | MatchError
CompileOutcome = Compiled | CompileError


class Oracle:
    """A running pcre2shim process."""

    def __init__(
        self, shim: Path, limits: Limits, timeout: float = DEFAULT_TIMEOUT_SECONDS
    ) -> None:
        self._shim = shim
        self._limits = limits
        self._timeout = timeout
        self._process: subprocess.Popen[str] | None = None
        self.library_version = ""

    def __enter__(self) -> Oracle:
        self.start()
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        self.close()

    def start(self) -> None:
        if self._process is not None:
            return
        process = subprocess.Popen(
            [str(self._shim), *self._limits.shim_arguments()],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="ascii",
            bufsize=1,
        )
        # Only adopt the process once the handshake works. A shim that answers
        # something unexpected has to leave nothing running behind it, and has
        # to leave this object startable again rather than half-initialized.
        self._process = process
        try:
            version, library = self._hello()
            if version != PROTOCOL_VERSION:
                raise OracleError(
                    f"shim speaks protocol {version}, this client speaks {PROTOCOL_VERSION}"
                )
        except BaseException:
            process.kill()
            self._discard(process)
            raise
        self.library_version = library

    def close(self) -> None:
        process = self._process
        self._process = None
        if process is None:
            return
        try:
            if process.stdin is not None and not process.stdin.closed:
                process.stdin.write("quit\n")
                process.stdin.flush()
                process.stdin.close()
            process.wait(timeout=10)
        except (BrokenPipeError, subprocess.TimeoutExpired):
            process.kill()
            process.wait()
        finally:
            for stream in (process.stdout, process.stderr):
                if stream is not None:
                    stream.close()

    def _request(self, line: str) -> list[str]:
        process = self._process
        if process is None or process.stdin is None or process.stdout is None:
            raise OracleError("the oracle is not running")

        response = self._exchange(process, line)
        fields = response.rstrip("\n").split(" ")
        if not fields or not fields[0]:
            raise ProtocolError(f"empty response to {line!r}")
        if fields[0] == "error":
            if len(fields) != 2:
                raise ProtocolError(f"unexpected error response: {fields!r}")
            raise OracleError(decode_blob(fields[1]).decode("ascii", "replace"))
        return fields

    def _exchange(self, process: subprocess.Popen[str], line: str) -> str:
        """Send one request, return one whole response line.

        The watchdog covers the write as well as the read, because a shim that
        stopped reading blocks us just as thoroughly as one that stopped
        answering: the pipe fills on a large pattern and the write never
        returns. The two sides settle who won under a lock, so an answer that
        arrives as the clock runs out is never thrown away, and a watchdog that
        fires first never has its kill undone.
        """
        assert process.stdin is not None and process.stdout is not None
        watchdog = _Watchdog(process, self._timeout)
        try:
            try:
                process.stdin.write(line + "\n")
                process.stdin.flush()
                response = process.stdout.readline()
            except (OSError, ValueError):
                # A broken or closed pipe: the shim is gone, and why it went is
                # settled below rather than here.
                response = ""
        finally:
            expired = watchdog.stop()

        if expired:
            # The shim was killed, so it is gone whatever the read came back
            # with. A whole line that landed as the clock ran out is still a
            # real answer; anything shorter is the timeout.
            self._discard(process)
            if not response.endswith("\n"):
                raise OracleError(f"the oracle stopped answering after {self._timeout} seconds")
            return response

        if not response.endswith("\n"):
            # Including the empty string. A response without its terminator is
            # a line that was cut short, never a shorter answer.
            raise OracleError(f"the oracle died mid-answer: {self._diagnosis()}")
        return response

    def _discard(self, process: subprocess.Popen[str]) -> None:
        """Let go of a process that is already dead, closing its pipes."""
        self._process = None
        process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream is not None and not stream.closed:
                stream.close()

    def _diagnosis(self) -> str:
        """Why the shim stopped answering. Called only once it has stopped."""
        process = self._process
        if process is None:
            return "already closed"
        try:
            status = process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            process.kill()
            return "stopped answering without exiting"
        if process.stderr is not None:
            message = process.stderr.read().strip()
            if message:
                return message
        return f"exit status {status}"

    def _hello(self) -> tuple[int, str]:
        fields = _shaped(self._request("hello"), "hello", exactly=3)
        return _integer(fields[1], "the protocol version"), decode_blob(fields[2]).decode(
            "ascii", "replace"
        )

    def config(self) -> dict[str, object]:
        """The linked library's configuration, as pcre2_config() reports it."""
        fields = _shaped(self._request("config"), "config")
        values: dict[str, object] = {}
        for field in fields[1:]:
            key, separator, value = field.partition("=")
            if not separator:
                raise ProtocolError(f"unexpected config field: {field!r}")
            values[key] = decode_blob(value) if ":" in value else _integer(value, key)
        return values

    @staticmethod
    def _pattern_fields(
        pattern: bytes, options: Sequence[str], newline: str | None, bsr: str | None
    ) -> list[str]:
        """The four fields both requests start with, as the shim reads them."""
        return [
            encode_blob(pattern),
            encode_options(options),
            encode_convention(newline),
            encode_convention(bsr),
        ]

    def compile(
        self,
        pattern: bytes,
        *,
        options: Sequence[str] = (),
        newline: str | None = "LF",
        bsr: str | None = "UNICODE",
    ) -> CompileOutcome:
        fields = self._request(
            " ".join(["compile", *self._pattern_fields(pattern, options, newline, bsr)])
        )
        if fields[0] == "cerror":
            return _compile_error(fields)
        _shaped(fields, "compiled", at_least=3)

        capture_count = _integer(fields[1], "the capture count")
        name_count = _integer(fields[2], "the group name count")
        if capture_count < 0 or name_count < 0:
            raise ProtocolError(f"negative counts in a compile response: {fields!r}")
        entries = fields[3:]
        if len(entries) != name_count:
            raise ProtocolError(f"expected {name_count} group names, got {len(entries)}")
        names = []
        for entry in entries:
            number, separator, blob = entry.partition(",")
            if not separator:
                raise ProtocolError(f"unexpected name entry: {entry!r}")
            group = _integer(number, "a group number")
            if not 1 <= group <= capture_count:
                raise ProtocolError(
                    f"group name {blob!r} names group {group}, "
                    f"but the pattern has {capture_count}"
                )
            names.append((decode_blob(blob), group))
        return Compiled(capture_count=capture_count, names=tuple(names))

    def match(
        self,
        pattern: bytes,
        subject: bytes,
        *,
        start: int = 0,
        options: Sequence[str] = (),
        match_options: Sequence[str] = (),
        newline: str | None = "LF",
        bsr: str | None = "UNICODE",
    ) -> MatchOutcome:
        if start < 0:
            raise ValueError("a start offset is a byte index, so it cannot be negative")
        fields = self._request(
            " ".join(
                [
                    "match",
                    *self._pattern_fields(pattern, options, newline, bsr),
                    encode_blob(subject),
                    str(start),
                    encode_options(match_options),
                ]
            )
        )
        if fields[0] == "nomatch":
            _shaped(fields, "nomatch", exactly=1)
            return NoMatch()
        if fields[0] == "cerror":
            return _compile_error(fields)
        if fields[0] == "merror":
            _shaped(fields, "merror", exactly=3)
            return MatchError(
                code=_integer(fields[1], "an error code"),
                message=decode_blob(fields[2]).decode("ascii", "replace"),
            )
        _shaped(fields, "match", at_least=2)

        pair_count = _integer(fields[1], "the pair count")
        offsets = tuple(_integer(value, "an offset") for value in fields[2:])
        if pair_count < 1 or len(offsets) != pair_count * 2:
            raise ProtocolError(f"expected {pair_count} offset pairs, got {len(offsets)}")
        _check_ovector(offsets, len(subject))
        return Match(ovector=offsets)


def _compile_error(fields: list[str]) -> CompileError:
    _shaped(fields, "cerror", exactly=4)
    return CompileError(
        code=_integer(fields[1], "an error code"),
        offset=_integer(fields[2], "an error offset"),
        message=decode_blob(fields[3]).decode("ascii", "replace"),
    )
