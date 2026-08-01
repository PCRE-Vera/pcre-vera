"""Shared fixtures.

The oracle is built once per session and only when a test actually asks for it,
so the tests that need nothing but Python stay fast.
"""

from __future__ import annotations

from collections.abc import Iterator

import pytest

from pcretruste.oracle import Oracle, OracleBuild, Pin  # noqa: F401 - Oracle is a type here
from pcretruste.oracle import build as build_module
from pcretruste.oracle import pin as pin_module


@pytest.fixture(scope="session")
def pin() -> Pin:
    return pin_module.load()


@pytest.fixture(scope="session")
def oracle_build(pin: Pin) -> OracleBuild:
    return build_module.ensure(pin=pin)


@pytest.fixture(scope="session")
def oracle(oracle_build: OracleBuild, pin: Pin) -> Iterator[Oracle]:
    with build_module.open_oracle(oracle_build, pin) as running:
        yield running


def pytest_collection_modifyitems(items):
    """Mark everything that needs the pinned build, by what it asks for.

    Declaring the marker by hand meant most of the tests that build pcre2 went
    unmarked, so `-m "not oracle"` built it anyway. Asking for the fixture is
    the property; nothing has to remember to say so as well.
    """
    for item in items:
        if {"oracle", "oracle_build"} & set(getattr(item, "fixturenames", ())):
            item.add_marker("oracle")
