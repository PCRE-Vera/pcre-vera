"""Shared fixtures, and the session-wide check that every validator rule fires.

The oracle is built once per session and only when a test actually asks for it,
so the tests that need nothing but Python stay fast.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from pathlib import Path

import pytest

from pcretruste.oracle import Oracle, OracleBuild, Pin  # noqa: F401 - Oracle is a type here
from pcretruste.oracle import build as build_module
from pcretruste.oracle import pin as pin_module
from pcretruste.tir.validate import ValidationError


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


# --- every validator rule really fires, watched rather than grepped ---
#
# TIR-SPEC.md section 15 promises a test that trips each rule. Checking that by
# looking for the rule's number in a test file only proves somebody typed it, so
# instead every ValidationError raised anywhere in the session is recorded, and
# a rule nobody managed to provoke fails the run at the end. V-001 is the one
# exception: the reader raises it, and a syntax error carries no rule number.

TRIPPED: set[str] = set()

_original_init = ValidationError.__init__


def _record(self, rule: str, message: str) -> None:
    TRIPPED.add(rule)
    _original_init(self, rule, message)


ValidationError.__init__ = _record


def rules_in_the_specification() -> set[str]:
    spec = (Path(__file__).parents[1] / "TIR-SPEC.md").read_text()
    return set(re.findall(r"^(V-\d{3})  ", spec, flags=re.MULTILINE)) - {"V-001"}


def pytest_sessionfinish(session, exitstatus):
    # Only on a whole, green run. A run narrowed to one file or one keyword has
    # every right to leave rules untripped, and failing it would make the
    # obvious way to work on a single test unusable.
    narrowed = session.config.option.keyword or session.config.option.file_or_dir
    if exitstatus != 0 or narrowed:
        return
    missing = sorted(rules_in_the_specification() - TRIPPED)
    if missing:
        session.exitstatus = 1
        print(f"\nno test ever tripped these validator rules: {', '.join(missing)}")
