"""The wire format, on its own. No pcre2 involved."""

from __future__ import annotations

import pytest

from pcretruste.oracle.protocol import (
    ProtocolError,
    decode_blob,
    encode_blob,
    encode_convention,
    encode_options,
)


@pytest.mark.parametrize(
    "data",
    [b"", b"a", b"\x00", b"\xff\xfe", bytes(range(256)), b"a\nb", b"line: value"],
)
def test_oracle_blobs_round_trip(data):
    assert decode_blob(encode_blob(data)) == data


def test_oracle_blob_carries_its_length():
    assert encode_blob(b"ab") == "2:6162"
    assert encode_blob(b"") == "0:"


@pytest.mark.parametrize(
    "token",
    [
        "2:61",  # length says two bytes, only one is there
        "1:6162",  # the other way round
        "6162",  # no length at all
        "2:zz61",  # not hex
        ":6162",  # empty length
        "-1:61",  # not a count
    ],
)
def test_oracle_rejects_a_damaged_blob(token):
    """A truncated line has to fail, not decode into a shorter payload."""
    with pytest.raises(ProtocolError):
        decode_blob(token)


def test_oracle_option_lists():
    assert encode_options(()) == "-"
    assert encode_options(("CASELESS",)) == "CASELESS"
    assert encode_options(("CASELESS", "MULTILINE")) == "CASELESS,MULTILINE"


@pytest.mark.parametrize("name", ["", "case less", "CASELESS,MULTILINE", "a-b"])
def test_oracle_rejects_an_unusable_option_name(name):
    with pytest.raises(ValueError):
        encode_options((name,))


def test_oracle_conventions():
    assert encode_convention(None) == "-"
    assert encode_convention("CRLF") == "CRLF"
    with pytest.raises(ValueError):
        encode_convention("cr lf")
