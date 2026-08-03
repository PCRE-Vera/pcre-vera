"""The PCRE engine — pattern parser, bytecode compiler, backtracking matcher — written with the DSL.

The modules under here build one TIR program; `driver` runs it through the
reference interpreter and answers the same two questions the oracle does, so
the differential tests can ask both the same thing.

What is here is the wave 1 subset of DESIGN.md section 2.1 on the backtracking
matcher of section 4.3, under caller-supplied cost, stack and memory limits.
M4 added the two backends around it. M5 has since landed the Pike VM, matcher
selection, the analysis accessors, the match configuration argument and the
preallocated match context; the memoized configuration waits for M9, and
find-all is the backends' own sugar over match calls. Wave 2 lands in M8,
wave 3 in M10.

M5 has started with the resource analysis of DESIGN.md section 5, which is four
modules and one split. `compiler` emits the region tree while it still has the
AST in hand, and stores it on the compiled pattern. `analyzer` walks that tree
and prices every region; `certificate` is the checker that decides whether to
believe what came out, and it prices the program opcode by opcode against the
rules of BOUNDS.md rather than reading the analyzer's working. `bounds` is what
both count in, since the cost model is meant to be one thing.

Compiling now runs both, and a pattern carries a certificate only after the
checker has accepted it. A pattern the rules cannot price still compiles and
simply has none, which is the ExceedsBudget the accessors report. `accessors`
is those accessors — the public reading of the certificate slot, one generated
implementation shared by every backend — and `match` now takes the public
match configuration, of which only the default exists until M9.

`pike` is the lockstep matcher, and selection is live: compilation computes
eligibility, stores it on the compiled pattern, prices the Pike path with the
closed form of BOUNDS.md section 9, and the public `match` routes an eligible
pattern there while `bt_match` stays reachable as the internal testing entry
point. The accessors answer for the selected path. `context` is the
preallocated match context, the memory bound made physical: creation
reserves and zeroes exactly what the certificate prices, and a call on one
reuses it all. What is still missing from M5 is the fuzz-scale bound sweeps.
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
