"""The Python builder API the engine is authored against.

Builds TIR; it has no execution semantics of its own, and it is untrusted, so
the validator is what decides whether what it built means anything. See
`builder.py` for the shape it aims for, and TIR-SPEC.md for the IR itself.
"""

from .builder import (
    Expr,
    FuncBuilder,
    Inout,
    Module,
    Ref,
    SwitchBuilder,
    TypeRef,
    boolean,
    bytes_,
    counter,
    frozen,
    i32,
    inout,
    land,
    lnot,
    lor,
    u8,
    u32,
    vec,
)

__all__ = [
    "Expr",
    "FuncBuilder",
    "Inout",
    "Module",
    "Ref",
    "SwitchBuilder",
    "TypeRef",
    "boolean",
    "bytes_",
    "counter",
    "frozen",
    "i32",
    "inout",
    "land",
    "lnot",
    "lor",
    "u8",
    "u32",
    "vec",
]
