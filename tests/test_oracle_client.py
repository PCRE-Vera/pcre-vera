"""The harness itself: does it say back exactly what pcre2 said?"""

from __future__ import annotations

import subprocess

import pytest

from pcrevera.oracle import Compiled, CompileError, Match, MatchError, NoMatch, Oracle, OracleError


def test_oracle_reports_its_library_version(oracle: Oracle, pin):
    assert oracle.library_version.startswith(pin.version)


def test_oracle_returns_offsets_for_every_group(oracle: Oracle):
    outcome = oracle.match(b"(a)(b)?", b"a")
    assert isinstance(outcome, Match)
    assert outcome.group_count == 2
    assert outcome.span == (0, 1)
    assert outcome.group(1) == (0, 1)
    assert outcome.group(2) == (-1, -1), "an unset group is -1, never PCRE2_UNSET"


def test_oracle_distinguishes_no_match_from_failure(oracle: Oracle):
    assert isinstance(oracle.match(b"a", b"b"), NoMatch)
    assert isinstance(oracle.match(b"a", b"abc", start=99), MatchError)


def test_oracle_carries_compile_errors_with_their_offsets(oracle: Oracle):
    outcome = oracle.match(b"a(b", b"whatever")
    assert isinstance(outcome, CompileError)
    assert outcome.code == 114
    assert outcome.offset == 3
    assert "parenthesis" in outcome.message


def test_oracle_reports_group_names(oracle: Oracle):
    outcome = oracle.compile(b"(?<first>a)(b)(?<third>c)")
    assert isinstance(outcome, Compiled)
    assert outcome.capture_count == 3
    assert sorted(outcome.names) == [(b"first", 1), (b"third", 3)]


def test_oracle_handles_arbitrary_bytes(oracle: Oracle):
    subject = bytes(range(256))
    outcome = oracle.match(b"\\x00\\x01", subject)
    assert isinstance(outcome, Match)
    assert outcome.span == (0, 2)

    outcome = oracle.match(bytes([0xFF]), subject)
    assert isinstance(outcome, Match)
    assert outcome.span == (255, 256)


def test_oracle_honours_the_newline_convention(oracle: Oracle):
    subject = b"a\r\nb"
    assert isinstance(oracle.match(b"a$", subject, options=("MULTILINE",), newline="CRLF"), Match)
    assert isinstance(oracle.match(b"a$", subject, options=("MULTILINE",), newline="LF"), NoMatch)


def test_oracle_refuses_an_option_it_does_not_know(oracle: Oracle):
    """An unknown option is an error, never a bit that quietly goes missing."""
    with pytest.raises(OracleError):
        oracle.match(b"a", b"a", options=("NOT_AN_OPTION",))


def test_oracle_survives_a_refused_request(oracle: Oracle):
    """A rejected request must not desynchronise the stream."""
    with pytest.raises(OracleError):
        oracle.match(b"a", b"a", options=("NOT_AN_OPTION",))
    assert isinstance(oracle.match(b"a", b"a"), Match)


def test_oracle_start_offset_must_be_an_index(oracle: Oracle):
    with pytest.raises(ValueError):
        oracle.match(b"a", b"a", start=-1)


def test_oracle_answers_every_line_exactly_once(oracle_build, pin):
    """One line in, one line out, even for nonsense.

    A request that produced no response, or two, would shift every later answer
    onto the wrong case, which is the one harness bug that would corrupt
    differential results silently rather than loudly.
    """
    process = subprocess.Popen(
        [str(oracle_build.shim), *pin.limits.shim_arguments()],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        encoding="ascii",
        bufsize=1,
    )
    requests = [
        "",
        "   ",
        "nonsense",
        "hello extra",
        "config extra",
        "match",
        "match 1:61 - LF UNICODE 1:61 0 -",
        "match 1:61 - LF UNICODE 1:61 0 - extra",
        "match 1:61 - LF UNICODE 1:61 -1 -",
        "compile 2:2861 - LF UNICODE",
        "hello",
    ]
    try:
        assert process.stdin is not None and process.stdout is not None
        answers = []
        for request in requests:
            process.stdin.write(request + "\n")
            process.stdin.flush()
            answers.append(process.stdout.readline().rstrip("\n"))
        process.stdin.write("quit\n")
        process.stdin.flush()
        answers.append(process.stdout.readline().rstrip("\n"))
    finally:
        process.stdin.close()
        process.wait(timeout=10)
        process.stdout.close()

    kinds = [answer.split(" ", 1)[0] for answer in answers]
    assert kinds == [
        "error",
        "error",
        "error",
        "error",
        "error",
        "error",
        "match",
        "error",
        "error",
        "cerror",
        "hello",
        "bye",
    ]
