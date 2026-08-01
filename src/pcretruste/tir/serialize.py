"""The canonical JSON encoding of a TIR program, both directions.

TIR-SPEC.md section 14 fixes the encoding down to the byte, because the
artifact's SHA-256 is the identity that ties the Lean proofs, the backends and
CI together. A writer that sorted keys differently on another machine would
move that hash without changing the program.

The reader is deliberately strict in the same spirit as the pin and corpus
loaders: every object has a closed, typed set of keys, so a misspelled field
is an error rather than a silently dropped one. It accepts any whitespace,
since a parser has no business caring; whether a file is *byte* canonical is
what `is_canonical` answers, and it is the question the Lean round-trip
self-check asks.
"""

from __future__ import annotations

import json
import re
from collections.abc import Iterable, Mapping, Sequence
from typing import Any

from . import ir
from .types import (
    BOOL,
    PRIMS,
    EnumDecl,
    EnumType,
    Field,
    FrozenType,
    Prim,
    StructDecl,
    StructType,
    Type,
    VecType,
)

SCHEMA = 1

HEX = re.compile(r"(?:[0-9a-f]{2})*\Z")


class TirSyntaxError(ValueError):
    """The document is not a well-formed TIR artifact.

    Distinct from a validation failure: this one says the JSON does not
    describe a program at all, not that the program it describes is unsound.
    """


# --- writing ---


def dumps(program: ir.Program) -> str:
    """The canonical text of a program, ending in exactly one newline."""
    return _render(_program_json(program), 0) + "\n"


def is_canonical(text: str, program: ir.Program) -> bool:
    return text == dumps(program)


def _render(value: Any, depth: int) -> str:
    pad = "  " * depth
    inner = "  " * (depth + 1)
    if isinstance(value, bool):
        return "true" if value else "false"
    if value is None:
        return "null"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return _render_string(value)
    if isinstance(value, list):
        if not value:
            return "[]"
        items = [inner + _render(item, depth + 1) for item in value]
        return "[\n" + ",\n".join(items) + "\n" + pad + "]"
    if isinstance(value, dict):
        if not value:
            return "{}"
        items = [
            f"{inner}{_render_string(key)}: {_render(value[key], depth + 1)}"
            for key in sorted(value)
        ]
        return "{\n" + ",\n".join(items) + "\n" + pad + "}"
    raise TypeError(f"not encodable as canonical JSON: {value!r}")


SHORT_ESCAPES = {"\b": "\\b", "\t": "\\t", "\n": "\\n", "\f": "\\f", "\r": "\\r"}


def _render_string(text: str) -> str:
    out = ['"']
    for ch in text:
        code = ord(ch)
        if ch in ('"', "\\"):
            out.append("\\" + ch)
        elif ch in SHORT_ESCAPES:
            out.append(SHORT_ESCAPES[ch])
        elif 0x20 <= code <= 0x7E:
            out.append(ch)
        elif code <= 0xFFFF:
            out.append(f"\\u{code:04x}")
        else:
            # Above the BMP, as a surrogate pair, which is what JSON has.
            code -= 0x10000
            out.append(f"\\u{0xD800 + (code >> 10):04x}")
            out.append(f"\\u{0xDC00 + (code & 0x3FF):04x}")
    out.append('"')
    return "".join(out)


def _program_json(p: ir.Program) -> dict[str, Any]:
    return {
        "tir": SCHEMA,
        "enums": [_enum_json(d) for d in sorted(p.enums, key=lambda d: d.name)],
        "structs": [_struct_json(d) for d in sorted(p.structs, key=lambda d: d.name)],
        "consts": [_const_json(d) for d in sorted(p.consts, key=lambda d: d.name)],
        "funcs": [_func_json(d) for d in sorted(p.funcs, key=lambda d: d.name)],
    }


def _enum_json(d: EnumDecl) -> dict[str, Any]:
    return {"name": d.name, "variants": list(d.variants)}


def _struct_json(d: StructDecl) -> dict[str, Any]:
    return {
        "name": d.name,
        "fields": [{"name": f.name, "type": _type_json(f.type)} for f in d.fields],
    }


def _const_json(d: ir.Const) -> dict[str, Any]:
    return {"name": d.name, "type": _type_json(d.type), "value": _const_value_json(d.value)}


def _func_json(d: ir.Func) -> dict[str, Any]:
    return {
        "name": d.name,
        "params": [{"name": p.name, "type": _type_json(p.type), "mode": p.mode} for p in d.params],
        "ret": None if d.ret is None else _type_json(d.ret),
        "body": _body_json(d.body),
    }


def _type_json(t: Type) -> Any:
    if isinstance(t, Prim):
        return t.name
    if isinstance(t, EnumType):
        return {"enum": t.name}
    if isinstance(t, StructType):
        return {"struct": t.name}
    if isinstance(t, VecType):
        return {"vec": {"elem": _type_json(t.elem), "max": t.max}}
    if isinstance(t, FrozenType):
        return {"frozen": _type_json(t.inner)}
    raise TypeError(f"not a TIR type: {t!r}")


def _const_value_json(v: ir.ConstValue) -> Any:
    if isinstance(v, (bool, int)):
        return v
    if isinstance(v, ir.EnumConst):
        return {"variant": v.variant}
    if isinstance(v, ir.StructConst):
        return {"fields": {name: _const_value_json(value) for name, value in v.fields}}
    if isinstance(v, ir.BytesConst):
        return {"bytes": v.data.hex()}
    if isinstance(v, ir.VecConst):
        return {"elems": [_const_value_json(e) for e in v.elems]}
    raise TypeError(f"not a TIR constant value: {v!r}")


def _expr_json(e: ir.Expr) -> Any:
    match e:
        case ir.Lit(type=t, value=value):
            return {t.name: value}
        case ir.Var(name=name):
            return {"var": name}
        case ir.ConstRef(name=name):
            return {"constref": name}
        case ir.FieldRead(base=base, name=name):
            return {"field": {"base": _expr_json(base), "name": name}}
        case ir.IndexRead(base=base, index=index):
            return {"index": {"base": _expr_json(base), "index": _expr_json(index)}}
        case ir.Len(arg=arg):
            return {"len": _expr_json(arg)}
        case ir.Cap(arg=arg):
            return {"cap": _expr_json(arg)}
        case ir.Unary(op=op, arg=arg):
            return {"un": {"op": op, "arg": _expr_json(arg)}}
        case ir.Binary(op=op, left=left, right=right):
            return {"bin": {"op": op, "left": _expr_json(left), "right": _expr_json(right)}}
        case ir.Compare(op=op, left=left, right=right):
            return {"cmp": {"op": op, "left": _expr_json(left), "right": _expr_json(right)}}
        case ir.DivRem(op=op, left=left, right=right, fallback=fallback):
            return {
                op: {
                    "left": _expr_json(left),
                    "right": _expr_json(right),
                    "fallback": _expr_json(fallback),
                }
            }
        case ir.Shift(op=op, arg=arg, count=count):
            return {"shift": {"op": op, "arg": _expr_json(arg), "count": count}}
        case ir.Cast(type=t, arg=arg):
            return {"cast": {"type": _type_json(t), "arg": _expr_json(arg)}}
        case ir.Logical(op=op, left=left, right=right):
            return {op: {"left": _expr_json(left), "right": _expr_json(right)}}
        case ir.EnumVal(type=t, variant=variant):
            return {"enumval": {"type": t, "variant": variant}}
        case ir.StructVal(type=t, fields=fields):
            return {
                "structval": {
                    "type": t,
                    "fields": {name: _expr_json(value) for name, value in fields},
                }
            }
    raise TypeError(f"not a TIR expression: {e!r}")


def _place_json(p: ir.Place) -> Any:
    match p:
        case ir.VarPlace(name=name):
            return {"var": name}
        case ir.FieldPlace(base=base, name=name):
            return {"field": {"base": _place_json(base), "name": name}}
        case ir.IndexPlace(base=base, index=index):
            return {"index": {"base": _place_json(base), "index": _expr_json(index)}}
    raise TypeError(f"not a TIR place: {p!r}")


def _body_json(body: Sequence[ir.Stmt]) -> list[Any]:
    return [_stmt_json(s) for s in body]


def _stmt_json(s: ir.Stmt) -> Any:
    match s:
        case ir.Let(name=name, type=t, init=init):
            return {
                "let": {
                    "name": name,
                    "type": _type_json(t),
                    "init": None if init is None else _expr_json(init),
                }
            }
        case ir.Assign(place=place, value=value):
            return {"assign": {"place": _place_json(place), "value": _expr_json(value)}}
        case ir.Take(dest=dest, src=src):
            return {"take": {"dest": _place_json(dest), "src": _place_json(src)}}
        case ir.Swap(a=a, b=b):
            return {"swap": {"a": _place_json(a), "b": _place_json(b)}}
        case ir.Copy(dest=dest, src=src):
            return {"copy": {"dest": _place_json(dest), "src": _expr_json(src)}}
        case ir.Freeze(dest=dest, src=src):
            return {"freeze": {"dest": _place_json(dest), "src": _place_json(src)}}
        case ir.Push(seq=seq, value=value):
            return {"push": {"seq": _place_json(seq), "value": _expr_json(value)}}
        case ir.Pop(seq=seq, dest=dest):
            return {"pop": {"seq": _place_json(seq), "dest": _place_json(dest)}}
        case ir.Truncate(seq=seq, length=length):
            return {"truncate": {"seq": _place_json(seq), "len": _expr_json(length)}}
        case ir.Reserve(seq=seq, cap=cap):
            return {"reserve": {"seq": _place_json(seq), "cap": _expr_json(cap)}}
        case ir.If(cond=cond, then=then, otherwise=otherwise):
            return {
                "if": {
                    "cond": _expr_json(cond),
                    "then": _body_json(then),
                    "else": _body_json(otherwise),
                }
            }
        case ir.While(cond=cond, variant=variant, body=body):
            return {
                "while": {
                    "cond": _expr_json(cond),
                    "variant": _expr_json(variant),
                    "body": _body_json(body),
                }
            }
        case ir.Switch(value=value, arms=arms, default=default):
            return {
                "switch": {
                    "value": _expr_json(value),
                    "arms": [
                        {"variant": arm.variant, "body": _body_json(arm.body)} for arm in arms
                    ],
                    "default": None if default is None else _body_json(default),
                }
            }
        case ir.Break():
            return {"break": {}}
        case ir.Continue():
            return {"continue": {}}
        case ir.Return(value=value):
            return {"return": {"value": None if value is None else _expr_json(value)}}
        case ir.Call(fn=fn, args=args, dest=dest):
            return {
                "call": {
                    "fn": fn,
                    "args": [_arg_json(a) for a in args],
                    "dest": None if dest is None else _place_json(dest),
                }
            }
    raise TypeError(f"not a TIR statement: {s!r}")


def _arg_json(a: ir.Arg) -> Any:
    if isinstance(a, ir.InArg):
        return {"in": _expr_json(a.expr)}
    return {"inout": _place_json(a.place)}


# --- reading ---


def loads(text: str) -> ir.Program:
    """Decode an artifact. Raises TirSyntaxError on anything it does not admit."""
    return _program(_parse_json(text))


def _parse_json(text: str) -> Any:
    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        seen: dict[str, Any] = {}
        for key, value in pairs:
            if key in seen:
                raise TirSyntaxError(f"duplicate key {key!r}")
            seen[key] = value
        return seen

    def no_floats(literal: str) -> Any:
        raise TirSyntaxError(f"the artifact holds no floats, found {literal}")

    def no_constants(literal: str) -> Any:
        raise TirSyntaxError(f"the artifact holds no {literal}")

    try:
        return json.loads(
            text,
            object_pairs_hook=no_duplicates,
            parse_float=no_floats,
            parse_constant=no_constants,
        )
    except json.JSONDecodeError as exc:
        raise TirSyntaxError(str(exc)) from exc
    except RecursionError as exc:
        # Text nested past what the parser's own stack takes. No program is
        # anywhere near that deep — rule V-044 caps nesting at 64 — so this is
        # a decoding failure like any other and not a rule to report.
        raise TirSyntaxError("the artifact nests deeper than it can be read") from exc


def _obj(
    value: Any, what: str, required: Iterable[str], optional: Iterable[str] = ()
) -> Mapping[str, Any]:
    """A JSON object with a closed set of keys, and nothing else."""
    if not isinstance(value, dict):
        raise TirSyntaxError(f"{what} must be an object, got {value!r}")
    required = tuple(required)
    missing = [key for key in required if key not in value]
    if missing:
        raise TirSyntaxError(f"{what} is missing: {', '.join(missing)}")
    unknown = set(value) - set(required) - set(optional)
    if unknown:
        raise TirSyntaxError(f"{what} has fields nothing reads: {', '.join(sorted(unknown))}")
    return value


def _tagged(value: Any, what: str) -> tuple[str, Any]:
    if not isinstance(value, dict) or len(value) != 1:
        raise TirSyntaxError(f"{what} is a one-key object, got {value!r}")
    ((tag, payload),) = value.items()
    return tag, payload


def _list(value: Any, what: str) -> list[Any]:
    if not isinstance(value, list):
        raise TirSyntaxError(f"{what} must be a list, got {value!r}")
    return value


def _int(value: Any, what: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TirSyntaxError(f"{what} must be an integer, got {value!r}")
    return value


def _name(value: Any, what: str) -> str:
    if not isinstance(value, str):
        raise TirSyntaxError(f"{what} must be a string, got {value!r}")
    if not ir.IDENTIFIER.match(value) or len(value) > ir.MAX_IDENTIFIER:
        raise TirSyntaxError(f"{what} is not an identifier: {value!r}")
    return value


def _program(doc: Any) -> ir.Program:
    top = _obj(doc, "a TIR program", ("tir", "enums", "structs", "consts", "funcs"))
    # Not `!= SCHEMA`: in Python `True` and `1.0` both equal 1, and neither is
    # a schema number. (`1.0` cannot get this far, but the habit is the point.)
    version = top["tir"]
    if type(version) is not int or version != SCHEMA:
        raise TirSyntaxError(f"tir schema {version!r} is not {SCHEMA}")
    return ir.Program(
        enums=tuple(_enum(e) for e in _list(top["enums"], "enums")),
        structs=tuple(_struct(s) for s in _list(top["structs"], "structs")),
        consts=tuple(_const(c) for c in _list(top["consts"], "consts")),
        funcs=tuple(_func(f) for f in _list(top["funcs"], "funcs")),
    )


def _enum(value: Any) -> EnumDecl:
    raw = _obj(value, "an enum", ("name", "variants"))
    name = _name(raw["name"], "an enum name")
    variants = _list(raw["variants"], f"the variants of {name}")
    return EnumDecl(
        name=name,
        variants=tuple(_name(v, f"a variant of {name}") for v in variants),
    )


def _struct(value: Any) -> StructDecl:
    raw = _obj(value, "a struct", ("name", "fields"))
    name = _name(raw["name"], "a struct name")
    fields = []
    for entry in _list(raw["fields"], f"the fields of {name}"):
        field = _obj(entry, f"a field of {name}", ("name", "type"))
        fields.append(
            Field(
                name=_name(field["name"], f"a field name in {name}"),
                type=_type(field["type"]),
            )
        )
    return StructDecl(name=name, fields=tuple(fields))


def _type(value: Any) -> Type:
    if isinstance(value, str):
        if value not in PRIMS:
            raise TirSyntaxError(f"unknown type {value!r}")
        return PRIMS[value]
    tag, payload = _tagged(value, "a type")
    if tag == "enum":
        return EnumType(_name(payload, "an enum type name"))
    if tag == "struct":
        return StructType(_name(payload, "a struct type name"))
    if tag == "frozen":
        return FrozenType(_type(payload))
    if tag == "vec":
        raw = _obj(payload, "a vec type", ("elem", "max"))
        return VecType(elem=_type(raw["elem"]), max=_int(raw["max"], "a vec maximum"))
    raise TirSyntaxError(f"unknown type form {tag!r}")


def _const(value: Any) -> ir.Const:
    raw = _obj(value, "a constant", ("name", "type", "value"))
    name = _name(raw["name"], "a constant name")
    return ir.Const(name=name, type=_type(raw["type"]), value=_const_value(raw["value"], name))


def _const_value(value: Any, what: str) -> ir.ConstValue:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    tag, payload = _tagged(value, f"the value of {what}")
    if tag == "variant":
        return ir.EnumConst(_name(payload, f"a variant in {what}"))
    if tag == "bytes":
        if not isinstance(payload, str) or not HEX.match(payload):
            raise TirSyntaxError(f"{what} is not an even-length lowercase hex string: {payload!r}")
        return ir.BytesConst(bytes.fromhex(payload))
    if tag == "elems":
        return ir.VecConst(
            tuple(_const_value(e, what) for e in _list(payload, f"the elements of {what}"))
        )
    if tag == "fields":
        if not isinstance(payload, dict):
            raise TirSyntaxError(f"the fields of {what} must be an object, got {payload!r}")
        return ir.StructConst(
            tuple(
                (_name(key, f"a field name in {what}"), _const_value(sub, what))
                for key, sub in payload.items()
            )
        )
    raise TirSyntaxError(f"unknown constant form {tag!r} in {what}")


def _func(value: Any) -> ir.Func:
    raw = _obj(value, "a function", ("name", "params", "ret", "body"))
    name = _name(raw["name"], "a function name")
    params = []
    for entry in _list(raw["params"], f"the parameters of {name}"):
        param = _obj(entry, f"a parameter of {name}", ("name", "type", "mode"))
        mode = param["mode"]
        if mode not in ir.PARAM_MODES:
            raise TirSyntaxError(f"a parameter mode is 'in' or 'inout', got {mode!r}")
        params.append(
            ir.Param(
                name=_name(param["name"], f"a parameter name in {name}"),
                type=_type(param["type"]),
                mode=mode,
            )
        )
    return ir.Func(
        name=name,
        params=tuple(params),
        ret=None if raw["ret"] is None else _type(raw["ret"]),
        body=_body(raw["body"], name),
    )


def _body(value: Any, what: str) -> tuple[ir.Stmt, ...]:
    return tuple(_stmt(s) for s in _list(value, f"a body in {what}"))


def _expr(value: Any) -> ir.Expr:
    tag, payload = _tagged(value, "an expression")
    if tag in PRIMS and tag != "bytes":
        t = PRIMS[tag]
        if t == BOOL:
            if not isinstance(payload, bool):
                raise TirSyntaxError(f"a bool literal is true or false, got {payload!r}")
            return ir.Lit(t, payload)
        return ir.Lit(t, _int(payload, f"a {tag} literal"))
    if tag == "var":
        return ir.Var(_name(payload, "a variable"))
    if tag == "constref":
        return ir.ConstRef(_name(payload, "a constant reference"))
    if tag == "field":
        raw = _obj(payload, "a field read", ("base", "name"))
        return ir.FieldRead(base=_expr(raw["base"]), name=_name(raw["name"], "a field name"))
    if tag == "index":
        raw = _obj(payload, "an index", ("base", "index"))
        return ir.IndexRead(base=_expr(raw["base"]), index=_expr(raw["index"]))
    if tag == "len":
        return ir.Len(_expr(payload))
    if tag == "cap":
        return ir.Cap(_expr(payload))
    if tag == "un":
        raw = _obj(payload, "a unary operation", ("op", "arg"))
        return ir.Unary(op=_op(raw["op"], ir.UNARY_OPS), arg=_expr(raw["arg"]))
    if tag == "bin":
        raw = _obj(payload, "a binary operation", ("op", "left", "right"))
        return ir.Binary(
            op=_op(raw["op"], ir.BINARY_OPS), left=_expr(raw["left"]), right=_expr(raw["right"])
        )
    if tag == "cmp":
        raw = _obj(payload, "a comparison", ("op", "left", "right"))
        return ir.Compare(
            op=_op(raw["op"], ir.COMPARE_OPS), left=_expr(raw["left"]), right=_expr(raw["right"])
        )
    if tag in ir.DIVREM_OPS:
        raw = _obj(payload, f"a {tag}", ("left", "right", "fallback"))
        return ir.DivRem(
            op=tag,
            left=_expr(raw["left"]),
            right=_expr(raw["right"]),
            fallback=_expr(raw["fallback"]),
        )
    if tag == "shift":
        raw = _obj(payload, "a shift", ("op", "arg", "count"))
        return ir.Shift(
            op=_op(raw["op"], ir.SHIFT_OPS),
            arg=_expr(raw["arg"]),
            count=_int(raw["count"], "a shift count"),
        )
    if tag == "cast":
        raw = _obj(payload, "a cast", ("type", "arg"))
        return ir.Cast(type=_type(raw["type"]), arg=_expr(raw["arg"]))
    if tag in ir.LOGICAL_OPS:
        raw = _obj(payload, f"a boolean {tag}", ("left", "right"))
        return ir.Logical(op=tag, left=_expr(raw["left"]), right=_expr(raw["right"]))
    if tag == "enumval":
        raw = _obj(payload, "an enum value", ("type", "variant"))
        return ir.EnumVal(
            type=_name(raw["type"], "an enum name"),
            variant=_name(raw["variant"], "a variant name"),
        )
    if tag == "structval":
        raw = _obj(payload, "a struct value", ("type", "fields"))
        fields = raw["fields"]
        if not isinstance(fields, dict):
            raise TirSyntaxError(f"struct value fields must be an object, got {fields!r}")
        return ir.StructVal(
            type=_name(raw["type"], "a struct name"),
            fields=tuple(
                (_name(key, "a field name"), _expr(sub)) for key, sub in fields.items()
            ),
        )
    raise TirSyntaxError(f"unknown expression form {tag!r}")


def _op(value: Any, allowed: Sequence[str]) -> str:
    if value not in allowed:
        raise TirSyntaxError(f"unknown operator {value!r}, expected one of {', '.join(allowed)}")
    return value


def _place(value: Any) -> ir.Place:
    tag, payload = _tagged(value, "a place")
    if tag == "var":
        return ir.VarPlace(_name(payload, "a variable"))
    if tag == "field":
        raw = _obj(payload, "a field place", ("base", "name"))
        return ir.FieldPlace(base=_place(raw["base"]), name=_name(raw["name"], "a field name"))
    if tag == "index":
        raw = _obj(payload, "an index place", ("base", "index"))
        return ir.IndexPlace(base=_place(raw["base"]), index=_expr(raw["index"]))
    raise TirSyntaxError(f"a place is a variable, a field, or an index, got {tag!r}")


def _optional_expr(value: Any) -> ir.Expr | None:
    return None if value is None else _expr(value)


def _stmt(value: Any) -> ir.Stmt:
    tag, payload = _tagged(value, "a statement")
    if tag == "let":
        raw = _obj(payload, "a let", ("name", "type", "init"))
        return ir.Let(
            name=_name(raw["name"], "a local name"),
            type=_type(raw["type"]),
            init=_optional_expr(raw["init"]),
        )
    if tag == "assign":
        raw = _obj(payload, "an assignment", ("place", "value"))
        return ir.Assign(place=_place(raw["place"]), value=_expr(raw["value"]))
    if tag == "take":
        raw = _obj(payload, "a take", ("dest", "src"))
        return ir.Take(dest=_place(raw["dest"]), src=_place(raw["src"]))
    if tag == "swap":
        raw = _obj(payload, "a swap", ("a", "b"))
        return ir.Swap(a=_place(raw["a"]), b=_place(raw["b"]))
    if tag == "copy":
        raw = _obj(payload, "a copy", ("dest", "src"))
        return ir.Copy(dest=_place(raw["dest"]), src=_expr(raw["src"]))
    if tag == "freeze":
        raw = _obj(payload, "a freeze", ("dest", "src"))
        return ir.Freeze(dest=_place(raw["dest"]), src=_place(raw["src"]))
    if tag == "push":
        raw = _obj(payload, "a push", ("seq", "value"))
        return ir.Push(seq=_place(raw["seq"]), value=_expr(raw["value"]))
    if tag == "pop":
        raw = _obj(payload, "a pop", ("seq", "dest"))
        return ir.Pop(seq=_place(raw["seq"]), dest=_place(raw["dest"]))
    if tag == "truncate":
        raw = _obj(payload, "a truncate", ("seq", "len"))
        return ir.Truncate(seq=_place(raw["seq"]), length=_expr(raw["len"]))
    if tag == "reserve":
        raw = _obj(payload, "a reserve", ("seq", "cap"))
        return ir.Reserve(seq=_place(raw["seq"]), cap=_expr(raw["cap"]))
    if tag == "if":
        raw = _obj(payload, "an if", ("cond", "then", "else"))
        return ir.If(
            cond=_expr(raw["cond"]),
            then=_body(raw["then"], "an if"),
            otherwise=_body(raw["else"], "an if"),
        )
    if tag == "while":
        raw = _obj(payload, "a while", ("cond", "variant", "body"))
        return ir.While(
            cond=_expr(raw["cond"]),
            variant=_expr(raw["variant"]),
            body=_body(raw["body"], "a while"),
        )
    if tag == "switch":
        raw = _obj(payload, "a switch", ("value", "arms", "default"))
        arms = []
        for entry in _list(raw["arms"], "switch arms"):
            arm = _obj(entry, "a switch arm", ("variant", "body"))
            arms.append(
                ir.Arm(
                    variant=_name(arm["variant"], "a variant name"),
                    body=_body(arm["body"], "a switch arm"),
                )
            )
        default = raw["default"]
        return ir.Switch(
            value=_expr(raw["value"]),
            arms=tuple(arms),
            default=None if default is None else _body(default, "a switch default"),
        )
    if tag == "break":
        _obj(payload, "a break", ())
        return ir.Break()
    if tag == "continue":
        _obj(payload, "a continue", ())
        return ir.Continue()
    if tag == "return":
        raw = _obj(payload, "a return", ("value",))
        return ir.Return(value=_optional_expr(raw["value"]))
    if tag == "call":
        raw = _obj(payload, "a call", ("fn", "args", "dest"))
        args: list[ir.Arg] = []
        for entry in _list(raw["args"], "call arguments"):
            mode, sub = _tagged(entry, "a call argument")
            if mode == "in":
                args.append(ir.InArg(_expr(sub)))
            elif mode == "inout":
                args.append(ir.InoutArg(_place(sub)))
            else:
                raise TirSyntaxError(f"a call argument is 'in' or 'inout', got {mode!r}")
        dest = raw["dest"]
        return ir.Call(
            fn=_name(raw["fn"], "a function name"),
            args=tuple(args),
            dest=None if dest is None else _place(dest),
        )
    raise TirSyntaxError(f"unknown statement form {tag!r}")


__all__ = ["SCHEMA", "TirSyntaxError", "dumps", "is_canonical", "loads"]
