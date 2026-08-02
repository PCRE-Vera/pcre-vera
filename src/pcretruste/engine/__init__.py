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

M5 has started at the far end of the analysis, with `certificate`: the bound
certificate the analyzer will have to produce, the checker that decides whether
to believe one, and the finite-or-ExceedsBudget arithmetic the accessors report
in. The checker takes the compiled pattern and prices it opcode by opcode
against the rules of BOUNDS.md, so an accepted certificate bounds that program
rather than merely being well formed. `compiler` emits the region tree those
rules compose over, while it still has the AST in hand, and stores it on the
compiled pattern. What is still missing is the analyzer that annotates one.
"""

from .driver import (
    BadInput,
    Certificate,
    CompiledPattern,
    Engine,
    EngineError,
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
