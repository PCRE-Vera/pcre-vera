"""The PCRE engine — pattern parser, bytecode compiler, backtracking matcher — written with the DSL.

The modules under here build one TIR program; `driver` runs it through the
reference interpreter and answers the same two questions the oracle does, so
the differential tests can ask both the same thing.

What is here is the wave 1 subset of DESIGN.md section 2.1 on the backtracking
matcher of section 4.3, under caller-supplied cost, stack and memory limits.
The Pike VM, matcher selection, the memoized configuration and the analysis
accessors that compute those limits are M5; the rest of the section 2.4 API
surface — find-all, match contexts, matchConfig — belongs to the backends and
arrives with them in M4. Wave 2 lands in M8, wave 3 in M10.
"""

from .driver import (
    BadInput,
    CompiledPattern,
    Engine,
    EngineError,
    Limits,
    ResourceExceeded,
    TooLarge,
    Unsupported,
    Usage,
)
from . import spec
from .program import build, program

__all__ = [
    "BadInput",
    "CompiledPattern",
    "Engine",
    "EngineError",
    "Limits",
    "ResourceExceeded",
    "TooLarge",
    "Unsupported",
    "Usage",
    "build",
    "program",
    "spec",
]
