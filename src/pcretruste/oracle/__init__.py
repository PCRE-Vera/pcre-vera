"""The pcre2 oracle: the pinned reference build and the harness that queries it.

DESIGN.md section 2.3 makes one libpcre2 build the arbiter of what "correct
PCRE" means. This package is that arbiter in working form: it builds the pinned
release from source, checks that what got built really is the reference, and
drives it through a line protocol so the rest of the project can ask pcre2 what
a pattern does.
"""

from .build import BuildError, OracleBuild, ensure, open_oracle
from .client import (
    Compiled,
    CompileError,
    Match,
    MatchError,
    NoMatch,
    Oracle,
    OracleError,
    UNSET,
)
from .pin import Limits, Pin, check_configuration
from .pin import load as load_pin

__all__ = [
    "UNSET",
    "BuildError",
    "CompileError",
    "Compiled",
    "Limits",
    "Match",
    "MatchError",
    "NoMatch",
    "Oracle",
    "OracleBuild",
    "OracleError",
    "Pin",
    "check_configuration",
    "ensure",
    "load_pin",
    "open_oracle",
]
