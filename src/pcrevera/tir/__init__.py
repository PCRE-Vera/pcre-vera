"""TIR: the type model, the JSON codec, the validator, and the reference interpreter.

TIR-SPEC.md at the repository root is the normative definition. This package
implements it, and the rule numbers `validate` reports are that document's.
"""

from . import ir, types
from .interp import Cell, Interpreter, OutOfFuel, Trap, VariantViolation, run
from .ir import Program
from .serialize import TirSyntaxError, dumps, is_canonical, loads
from .validate import ValidationError, validate

__all__ = [
    "Cell",
    "Interpreter",
    "OutOfFuel",
    "Program",
    "TirSyntaxError",
    "Trap",
    "ValidationError",
    "VariantViolation",
    "dumps",
    "ir",
    "is_canonical",
    "loads",
    "run",
    "types",
    "validate",
]
