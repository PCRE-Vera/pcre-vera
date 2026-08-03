"""The PCRE engine — pattern parser, bytecode compiler, backtracking matcher — written with the DSL.

The modules under here build one TIR program; `driver` runs it through the
reference interpreter and answers the same two questions the oracle does, so
the differential tests can ask both the same thing.

What is here is the wave 1 subset of DESIGN.md section 2.1 on the backtracking
matcher of section 4.3, under caller-supplied cost, stack and memory limits.
M4 added the two backends around it, and left that surface deliberately
provisional: compile and match, nothing else. The Pike VM, matcher selection,
the memoized configuration, the analysis accessors, the match configuration
argument and the preallocated match context are all M5, and find-all is the
backends' own sugar over match calls. Wave 2 lands in M8, wave 3 in M10.

M5 has started with the resource analysis of DESIGN.md section 5, which is four
modules and one split. `compiler` emits the region tree while it still has the
AST in hand, and stores it on the compiled pattern. `analyzer` walks that tree
and prices every region; `certificate` is the checker that decides whether to
believe what came out, and it prices the program opcode by opcode against the
rules of BOUNDS.md rather than reading the analyzer's working. `bounds` is what
both count in, since the cost model is meant to be one thing.

Compiling now runs both, and a pattern carries a certificate only after the
checker has accepted it. A pattern the rules cannot price still compiles and
simply has none, which is the ExceedsBudget the accessors will report. What is
still missing is those accessors, and the Pike VM with rules of its own.
"""

from .driver import (
    BadInput,
    Certificate,
    CompiledPattern,
    Engine,
    EngineError,
    InternalError,
    Limits,
    Poly,
    Price,
    Region,
    ResourceExceeded,
    TooLarge,
    Unsupported,
    Usage,
)
from . import spec
from .program import build, program

__all__ = [
    "BadInput",
    "Certificate",
    "CompiledPattern",
    "Engine",
    "EngineError",
    "InternalError",
    "Limits",
    "Poly",
    "Price",
    "Region",
    "ResourceExceeded",
    "TooLarge",
    "Unsupported",
    "Usage",
    "build",
    "program",
    "spec",
]
