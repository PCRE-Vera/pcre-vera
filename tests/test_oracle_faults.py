"""What the harness does when the shim misbehaves.

The shim is our own code, so none of this should ever happen. That is exactly
why it is worth testing: a harness that answers questions about pcre2 by
misreading a damaged response would be reporting fiction, and the failure would
show up as a wrong differential result rather than as an error.
"""

from __future__ import annotations

import errno
import os
import time
from pathlib import Path

import pytest

from pcretruste.oracle import Limits, Oracle, OracleError
from pcretruste.oracle.protocol import ProtocolError

LIMITS = Limits(match_limit=1000, depth_limit=100, heap_limit_kib=1024)

HELLO = "hello 1 5:31302e3437\n"


def fake_shim(
    tmp_path: Path,
    responses: list[str],
    *,
    afterwards: str = "exit",
    pid_file: Path | None = None,
    name: str = "fake-shim",
) -> Path:
    """A stand-in that answers with a fixed script, then stops.

    ``afterwards`` is "exit" to close its pipes once the script runs out, or
    "hang" to go quiet while holding them open and reading nothing more.
    Responses carry their own line ending, so a script can end in a truncated
    one.
    """
    lines = [
        "#!/usr/bin/env python3",
        "import os, sys, time",
        f"responses = {responses!r}",
        f"pid_file = {str(pid_file) if pid_file is not None else None!r}",
        "if pid_file:",
        "    with open(pid_file, 'w') as handle:",
        "        handle.write(str(os.getpid()))",
        "for response in responses:",
        "    sys.stdin.readline()",
        "    sys.stdout.write(response)",
        "    sys.stdout.flush()",
        f"if {afterwards!r} == 'hang':",
        "    time.sleep(3600)",
    ]
    script = tmp_path / name
    script.write_text("\n".join(lines) + "\n")
    script.chmod(0o755)
    return script


def running(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except OSError as error:
        return error.errno != errno.ESRCH
    return True


def test_oracle_reports_a_shim_that_says_nothing(tmp_path):
    oracle = Oracle(fake_shim(tmp_path, []), LIMITS)
    with pytest.raises(OracleError):
        oracle.start()


def test_oracle_refuses_a_shim_speaking_another_protocol(tmp_path):
    oracle = Oracle(fake_shim(tmp_path, ["hello 2 5:31302e3437\n"]), LIMITS)
    with pytest.raises(OracleError, match="protocol"):
        oracle.start()


def test_oracle_gives_up_on_a_shim_that_stops_answering(tmp_path):
    """The failure that would otherwise wedge a whole fuzzing run.

    A shim that keeps its pipes open while answering nothing cannot be noticed
    by watching for end of input; only a clock notices it. The request here is
    small enough to fit the pipe, so it is the read that blocks.
    """
    with Oracle(fake_shim(tmp_path, [HELLO], afterwards="hang"), LIMITS, timeout=1.0) as oracle:
        started = time.monotonic()
        with pytest.raises(OracleError, match="stopped answering"):
            oracle.match(b"a", b"a")
        assert time.monotonic() - started < 30


def test_oracle_leaves_no_child_behind_after_a_failed_start(tmp_path):
    """A failed start has to be a clean no-op, not a half-open oracle."""
    pid_file = tmp_path / "pid"
    shim = fake_shim(tmp_path, ["hello 2 5:31302e3437\n"], afterwards="hang", pid_file=pid_file)
    oracle = Oracle(shim, LIMITS)

    with pytest.raises(OracleError):
        oracle.start()

    assert oracle._process is None
    pid = int(pid_file.read_text())
    for _ in range(100):
        if not running(pid):
            break
        time.sleep(0.05)
    assert not running(pid), f"the shim from the failed handshake is still running as {pid}"

    # Starting again has to be possible, and has to fail the same way.
    with pytest.raises(OracleError):
        oracle.start()
    oracle.close()


@pytest.mark.parametrize(
    "response",
    [
        "match two 0 1",  # a pair count that is not a number
        "match 2 0 1",  # a pair count that does not match the offsets
        "match 0",  # no pairs at all, which a match always has
        "match",  # no pair count at all
        "error",  # an error with no message
        "matched 1 0 1",  # a response kind that does not exist
        "",  # nothing at all
    ],
)
def test_oracle_refuses_a_damaged_response(tmp_path, response):
    with Oracle(fake_shim(tmp_path, [HELLO, response + "\n"]), LIMITS) as oracle:
        with pytest.raises(ProtocolError):
            oracle.match(b"a", b"a")


@pytest.mark.parametrize(
    "response",
    [
        "match 1 -1 -1",  # a successful match with no offsets of its own
        "match 2 0 1 -1 1",  # a group unset at one end only
        "match 1 0 9",  # an offset past the end of the subject we sent
        "match 1 -2 1",  # a negative offset that is not the unset marker
    ],
)
def test_oracle_refuses_an_ovector_pcre2_could_not_have_produced(tmp_path, response):
    """Wrong offsets would become differential-test facts if they were accepted."""
    with Oracle(fake_shim(tmp_path, [HELLO, response + "\n"]), LIMITS) as oracle:
        with pytest.raises(ProtocolError):
            oracle.match(b"a", b"ab")


@pytest.mark.parametrize(
    "response",
    [
        "compiled 1 2 1,1:61",  # fewer name entries than the count promised
        "compiled 1 1 2,1:61",  # a name for a group the pattern does not have
        "compiled -1 0",  # a negative capture count
    ],
)
def test_oracle_refuses_a_damaged_compile_response(tmp_path, response):
    with Oracle(fake_shim(tmp_path, [HELLO, response + "\n"]), LIMITS) as oracle:
        with pytest.raises(ProtocolError):
            oracle.compile(b"(a)")


def test_oracle_refuses_a_damaged_config_response(tmp_path):
    with Oracle(fake_shim(tmp_path, [HELLO, "config jit=maybe\n"]), LIMITS) as oracle:
        with pytest.raises(ProtocolError):
            oracle.config()


def test_oracle_gives_up_on_a_shim_that_stops_reading(tmp_path):
    """The other half of a wedged run: the write blocks, not the read.

    The same silent shim, but the pattern is large enough to fill the pipe, so
    the request never even gets sent — which no amount of watching stdout would
    notice.
    """
    with Oracle(fake_shim(tmp_path, [HELLO], afterwards="hang"), LIMITS, timeout=1.0) as oracle:
        started = time.monotonic()
        with pytest.raises(OracleError, match="stopped answering"):
            oracle.match(b"a" * 500_000, b"a")
        assert time.monotonic() - started < 30


def test_oracle_refuses_a_response_cut_short(tmp_path):
    """A line without its terminator is a truncated answer, not a shorter one."""
    with Oracle(fake_shim(tmp_path, [HELLO, "nomatch"]), LIMITS) as oracle:
        with pytest.raises(OracleError, match="mid-answer"):
            oracle.match(b"a", b"b")
