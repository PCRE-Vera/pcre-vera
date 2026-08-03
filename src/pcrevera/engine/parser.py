"""The pattern parser, written in TIR.

One left-to-right pass over the pattern bytes with an explicit stack of open
groups, producing an AST in a flat arena (DESIGN.md section 4.1). There is no
recursion anywhere: a group pushes a frame, a class runs its own loop, and the
quantifier that follows an item rewrites that item's arena slot in place, which
is what keeps the parent's child list untouched.

Error codes and byte offsets are pcre2's, checked against the pinned build by
the differential tests. Only the message wording is ours, and the engine does
not carry messages at all — the driver holds them.
"""

from __future__ import annotations

from ..dsl import Expr, FuncBuilder, boolean, counter, inout, land, lnot, lor, u8, u32
from . import spec
from .layout import Layout

BACKSLASH = 92


def b(char: str) -> Expr:
    """A pattern byte written as the character it is."""
    return u8(ord(char))


def tmp(f: FuncBuilder, t, init=None):
    """A local whose name nobody has to invent, and nobody may reuse."""
    n = getattr(f, "_tmpn", 0) + 1
    f._tmpn = n
    return f.let(f"tmp{n}", t, init)


def one_of(value: Expr, chars: str) -> Expr:
    """`value` is one of these bytes."""
    test = value == b(chars[0])
    for char in chars[1:]:
        test = lor(test, value == b(char))
    return test


def down(hi: Expr, low: Expr) -> Expr:
    """A loop variant for an index climbing towards a bound."""
    return hi.cast(counter) - low.cast(counter)


def build(L: Layout) -> None:
    _tables(L)
    _nodes(L)
    _classes(L)
    _escapes(L)
    _quantifiers(L)
    _groups(L)
    _parse(L)
    _autopossess(L)


# --- small table lookups ---


def _tables(L: Layout) -> None:
    # The properties the parser asks about a byte, out of one 256-entry table.
    f = L.func("ct", params=[("c", u8), ("bit", u8)], ret=boolean)
    f.ret((L.CTYPE.at(f["c"].cast(u32)) & f["bit"]) != u8(0))

    # Whether a [:name:] really is one, and where its terminator sits. This is
    # pcre2's check_posix_syntax: scanning stops at a ] or at [<terminator>, so
    # `[:a]` is an ordinary class and `[:alpha:]` is not.
    f = L.func("posix_end", params=[("pat", L.frozen_bytes), ("at", u32)], ret=u32)
    end = tmp(f, u32, f["pat"].len())
    term = tmp(f, u8, f["pat"].at(f["at"]))
    i = tmp(f, u32, f["at"] + u32(1))
    with f.while_(i + u32(1) < end, down(end, i)):
        c = tmp(f, u8, f["pat"].at(i))
        with f.if_(
            land(
                c == u8(BACKSLASH),
                lor(
                    f["pat"].at(i + u32(1)) == b("]"),
                    f["pat"].at(i + u32(1)) == u8(BACKSLASH),
                ),
            )
        ):
            f.set(i, i + u32(2))
            f.cont()
        with f.if_(
            lor(
                land(c == b("["), f["pat"].at(i + u32(1)) == term),
                c == b("]"),
            )
        ):
            f.ret(u32(spec.NONE))
        with f.if_(land(c == term, f["pat"].at(i + u32(1)) == b("]"))):
            f.ret(i)
        f.set(i, i + u32(1))
    f.ret(u32(spec.NONE))

    # Which built-in set a POSIX name selects, or 255 for a name that is none.
    f = L.func(
        "posix_set",
        params=[("pat", L.frozen_bytes), ("off", u32), ("nlen", u32)],
        ret=u32,
    )
    p = tmp(f, u32, u32(0))
    total = tmp(f, u32, L.POSIX.len())
    with f.while_(p < total, down(total, p)):
        m = tmp(f, u32, L.POSIX.at(p).cast(u32))
        with f.if_(m == f["nlen"]):
            k = tmp(f, u32, u32(0))
            same = tmp(f, boolean, boolean(True))
            with f.while_(k < m, down(m, k)):
                with f.if_(L.POSIX.at(p + u32(1) + k) != f["pat"].at(f["off"] + k)):
                    f.set(same, boolean(False))
                    f.brk()
                f.set(k, k + u32(1))
            with f.if_(same):
                f.ret(L.POSIX.at(p + u32(1) + m).cast(u32))
        f.set(p, p + u32(2) + m)
    f.ret(u32(255))


# --- the arena ---


def _nodes(L: Layout) -> None:
    f = L.func(
        "alloc_node",
        params=[
            ("w", L.Work, "inout"),
            ("kind", L.Nd),
            ("val", u32),
            ("aux", u32),
            ("nopts", u32),
        ],
        ret=u32,
    )
    w = f["w"]
    n = tmp(f, u32, w.field("nodes").len())
    with f.if_(n >= u32(spec.MAX_NODES)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret(u32(0))
    f.push(
        w.field("nodes"),
        L.Node.of(
            kind=f["kind"],
            val=f["val"],
            aux=f["aux"],
            opts=f["nopts"],
            first=u32(0),
            last=u32(0),
            nxt=u32(0),
        ),
    )
    f.ret(n)

    f = L.func(
        "add_child", params=[("w", L.Work, "inout"), ("parent", u32), ("child", u32)]
    )
    w = f["w"]
    nodes = w.field("nodes")
    with f.if_(nodes.at(f["parent"]).field("first") == u32(0)):
        f.set(nodes.at(f["parent"]).field("first"), f["child"])
    with f.else_():
        prev = tmp(f, u32, nodes.at(f["parent"]).field("last"))
        f.set(nodes.at(prev).field("nxt"), f["child"])
    f.set(nodes.at(f["parent"]).field("last"), f["child"])

    # An ordinary literal byte, folded here when the pattern is caseless so that
    # nothing downstream has to carry the option.
    f = L.func("add_char", params=[("w", L.Work, "inout"), ("c", u32)])
    w = f["w"]
    kind = tmp(f, L.Nd, L.Nd.NdChar)
    value = tmp(f, u32, f["c"])
    with f.if_(lor(f["c"] == u32(0x0A), f["c"] == u32(0x0D))):
        f.set(w.field("hascrlf"), u32(1))
    with f.if_((w.field("opts") & u32(spec.CASELESS)) != u32(0)):
        # Only a byte that has another case needs the caseless opcode, and the
        # byte it carries is the folded one, so matching is a table read.
        with f.if_(L.FLIP.at(f["c"]) != f["c"].cast(u8)):
            f.set(kind, L.Nd.NdCharCI)
            f.set(value, L.LOWER.at(f["c"]).cast(u32))
    f.call("attach_atom", [inout(w), kind, value, u32(0)])

    # Every atom lands the same way: a new node, appended to the current branch,
    # and remembered as the thing a following quantifier repeats.
    f = L.func(
        "attach_atom",
        params=[("w", L.Work, "inout"), ("kind", L.Nd), ("val", u32), ("aux", u32)],
    )
    w = f["w"]
    node = tmp(f, u32, u32(0))
    kind = tmp(f, L.Nd, f["kind"])
    value = tmp(f, u32, f["val"])
    aux = tmp(f, u32, f["aux"])
    f.call("alloc_node", [inout(w), kind, value, aux, u32(0)], dest=node)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    top = tmp(f, u32, w.field("frames").len() - u32(1))
    cat = tmp(f, u32, w.field("frames").at(top).field("cat"))
    f.call("add_child", [inout(w), cat, node])
    f.set(w.field("frames").at(top).field("qual"), node)


# --- character classes ---


def _classes(L: Layout) -> None:
    f = L.func("new_class", params=[("w", L.Work, "inout")], ret=u32)
    w = f["w"]
    with f.if_(w.field("nclass") >= u32(spec.MAX_CLASSES)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret(u32(0))
    k = tmp(f, u32, u32(0))
    with f.while_(k < u32(32), down(u32(32), k)):
        f.push(w.field("classes"), u8(0))
        f.set(k, k + u32(1))
    idx = tmp(f, u32, w.field("nclass"))
    f.set(w.field("nclass"), idx + u32(1))
    f.ret(idx)

    f = L.func("set_add", params=[("w", L.Work, "inout"), ("base", u32), ("c", u32)])
    w = f["w"]
    at = tmp(f, u32, f["base"] + f["c"].cast(u8).shr(3).cast(u32))
    bit = tmp(f, u8, L.BITS.at((f["c"] & u32(7))))
    f.set(w.field("classes").at(at), w.field("classes").at(at) | bit)

    f = L.func(
        "set_range",
        params=[
            ("w", L.Work, "inout"),
            ("base", u32),
            ("lo", u32),
            ("hi", u32),
            ("fold", boolean),
        ],
    )
    w = f["w"]
    c = tmp(f, u32, f["lo"])
    base = tmp(f, u32, f["base"])
    with f.while_(c <= f["hi"], down(f["hi"] + u32(1), c)):
        f.call("set_add", [inout(w), base, c])
        with f.if_(f["fold"]):
            other = tmp(f, u32, L.FLIP.at(c).cast(u32))
            f.call("set_add", [inout(w), base, other])
        f.set(c, c + u32(1))

    f = L.func(
        "set_union",
        params=[
            ("w", L.Work, "inout"),
            ("base", u32),
            ("which", u32),
            ("neg", boolean),
        ],
    )
    w = f["w"]
    k = tmp(f, u32, u32(0))
    src = tmp(f, u32, f["which"] * u32(32))
    with f.while_(k < u32(32), down(u32(32), k)):
        v = tmp(f, u8, L.SETS.at(src + k))
        with f.if_(f["neg"]):
            f.set(v, ~v)
        at = tmp(f, u32, f["base"] + k)
        f.set(w.field("classes").at(at), w.field("classes").at(at) | v)
        f.set(k, k + u32(1))

    _parse_class(L)


def _parse_class(L: Layout) -> None:
    """`[...]`, from the opening bracket to the closing one.

    Returns the class table index; `at` is left just past the `]`. The whole
    thing is one loop over elements, where an element is a byte, a built-in set,
    or a POSIX name, and a `-` between two byte elements makes a range. Case
    folding happens here rather than at match time, so a caseless class is an
    ordinary bitmap by the time anything looks at it.
    """
    f = L.func(
        "parse_class",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
        ],
        ret=u32,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"] + u32(1))
    neg = tmp(f, boolean, boolean(False))
    quoting = tmp(f, boolean, boolean(False))
    # The ^ that negates a class is the first thing in it, and \Q and \E are
    # not things: `[\E^]` negates and `[\Q^\E]` does not.
    f.call("class_skip", [pat, inout(i), inout(quoting)])
    with f.if_(land(land(i < n, pat.at(i) == b("^")), lnot(quoting))):
        f.set(neg, boolean(True))
        f.set(i, i + u32(1))
    idx = tmp(f, u32, u32(0))
    f.call("new_class", [inout(w)], dest=idx)
    with f.if_(w.field("err") != u32(0)):
        f.ret(u32(0))
    f.set(w.field("clselems"), u32(0))
    f.set(w.field("clsrange"), u32(0))
    f.set(w.field("clscrlf"), u32(0))
    base = tmp(f, u32, idx * u32(32))
    fold = tmp(f, boolean, (w.field("opts") & u32(spec.CASELESS)) != u32(0))
    first = tmp(f, boolean, boolean(True))
    closed = tmp(f, boolean, boolean(False))
    # The byte a `-` would start a range from, or NONE when the last element was
    # a set, which is exactly the case pcre2 refuses with "invalid range".
    lit = tmp(f, u32, u32(spec.NONE))
    esc = tmp(f, L.Esc)

    with f.while_(land(i < n, w.field("err") == u32(0)), down(n, i)):
        c = tmp(f, u8, pat.at(i))

        with f.if_(quoting):
            with f.if_(
                land(c == u8(BACKSLASH), land(i + u32(1) < n, pat.at(i + u32(1)) == b("E")))
            ):
                f.set(quoting, boolean(False))
                f.set(i, i + u32(2))
                f.cont()
            # Inside \Q...\E a hyphen is a hyphen, so no range is looked for.
            f.set(first, boolean(False))
            f.set(lit, c.cast(u32))
            f.set(i, i + u32(1))
            f.call("note_element", [inout(w), lit, lit, boolean(False)])
            f.call("set_range", [inout(w), base, lit, lit, fold])
            f.cont()

        with f.if_(land(c == b("]"), lnot(first))):
            f.set(i, i + u32(1))
            f.set(closed, boolean(True))
            f.brk()

        # A POSIX name, but only when it really is one.
        with f.if_(land(c == b("["), i + u32(1) < n)):
            nxt = tmp(f, u8, pat.at(i + u32(1)))
            with f.if_(one_of(nxt, ":.=")):
                stop = tmp(f, u32, u32(spec.NONE))
                f.call("posix_end", [pat, i + u32(1)], dest=stop)
                with f.if_(stop != u32(spec.NONE)):
                    with f.if_(nxt != b(":")):
                        f.set(w.field("err"), u32(spec.E_POSIX_COLLATING))
                        f.set(w.field("erroff"), stop + u32(2))
                        f.cont()
                    f.set(first, boolean(False))
                    f.set(w.field("clsrange"), u32(1))
                    f.call("posix_item", [inout(w), pat, i, stop, base, fold])
                    f.set(i, stop + u32(2))
                    f.call("class_after_set", [inout(w), i, pat])
                    f.cont()

        with f.if_(c == u8(BACKSLASH)):
            with f.if_(i + u32(1) < n):
                q = tmp(f, u8, pat.at(i + u32(1)))
                with f.if_(q == b("Q")):
                    f.set(quoting, boolean(True))
                    f.set(i, i + u32(2))
                    f.cont()
                with f.if_(q == b("E")):
                    f.set(i, i + u32(2))
                    f.cont()
            f.set(first, boolean(False))
            f.call("read_escape", [pat, inout(i), inout(w), boolean(True)], dest=esc)
            with f.if_(w.field("err") != u32(0)):
                f.cont()
            with f.if_(esc.field("kind") == L.Ek.EkChar):
                f.set(lit, esc.field("val"))
                f.call("class_element", [inout(w), inout(i), inout(quoting), pat, base, lit, fold])
                f.cont()
            which = tmp(f, u32, esc.field("val"))
            negated = tmp(f, boolean, esc.field("kind") == L.Ek.EkNegSet)
            f.set(w.field("clsrange"), u32(1))
            f.call("set_union", [inout(w), base, which, negated])
            f.call("class_after_set", [inout(w), i, pat])
            f.cont()

        f.set(first, boolean(False))
        f.set(lit, c.cast(u32))
        f.set(i, i + u32(1))
        f.call("class_element", [inout(w), inout(i), inout(quoting), pat, base, lit, fold])

    with f.if_(w.field("err") != u32(0)):
        f.ret(u32(0))
    with f.if_(lnot(closed)):
        f.set(w.field("err"), u32(spec.E_MISSING_BRACKET))
        f.set(w.field("erroff"), n)
        f.ret(u32(0))
    # pcre2 records an explicitly written CR or LF so that the bumpalong rule
    # of section 4.3 can read it back — except for `[^x]`, which it compiles as
    # "not this character" rather than as a class, and which therefore never
    # reaches the code that records it.
    with f.if_(w.field("clscrlf") != u32(0)):
        alone = tmp(
            f,
            boolean,
            land(neg, land(w.field("clselems") == u32(1), w.field("clsrange") == u32(0))),
        )
        with f.if_(lnot(alone)):
            f.set(w.field("hascrlf"), u32(1))
    with f.if_(neg):
        k = tmp(f, u32, u32(0))
        with f.while_(k < u32(32), down(u32(32), k)):
            at = tmp(f, u32, base + k)
            f.set(w.field("classes").at(at), ~w.field("classes").at(at))
            f.set(k, k + u32(1))
    f.set(f["at"], i)
    f.ret(idx)

    # A `-` right after a set is pcre2's "invalid range in character class",
    # whatever follows it, unless the `-` is the last thing before the `]`.
    f = L.func(
        "class_after_set",
        params=[("w", L.Work, "inout"), ("at", u32), ("pat", L.frozen_bytes)],
    )
    w = f["w"]
    n = tmp(f, u32, f["pat"].len())
    i = tmp(f, u32, f["at"])
    with f.if_(
        land(
            land(i < n, f["pat"].at(i) == b("-")),
            land(i + u32(1) < n, f["pat"].at(i + u32(1)) != b("]")),
        )
    ):
        f.set(w.field("err"), u32(spec.E_INVALID_CLASS_RANGE))
        f.set(w.field("erroff"), i + u32(1))

    # One byte element, plus the range it may start.
    # One byte element, plus the range it may start. \Q and \E are lexer
    # markers rather than class contents, so they are skipped on both sides of
    # the hyphen: `[a\E-z]` is the range a to z and `[a-\E]` is the two
    # characters a and -, exactly as pcre2 reads them.
    f = L.func(
        "class_element",
        params=[
            ("w", L.Work, "inout"),
            ("at", u32, "inout"),
            ("quoting", boolean, "inout"),
            ("pat", L.frozen_bytes),
            ("base", u32),
            ("lo", u32),
            ("fold", boolean),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    base = tmp(f, u32, f["base"])
    lo = tmp(f, u32, f["lo"])
    fold = tmp(f, boolean, f["fold"])
    f.call("class_skip", [pat, inout(i), inout(f["quoting"])])

    with f.if_(land(land(i < n, pat.at(i) == b("-")), lnot(f["quoting"]))):
        j = tmp(f, u32, i + u32(1))
        quoted = tmp(f, boolean, boolean(False))
        f.call("class_skip", [pat, inout(j), inout(quoted)])
        with f.if_(land(j < n, lor(quoted, pat.at(j) != b("]")))):
            hi = tmp(f, u32, u32(spec.NONE))
            with f.if_(quoted):
                f.set(hi, pat.at(j).cast(u32))
                f.set(j, j + u32(1))
            with f.else_():
                with f.if_(pat.at(j) == u8(BACKSLASH)):
                    esc = tmp(f, L.Esc)
                    f.call("read_escape", [pat, inout(j), inout(w), boolean(True)], dest=esc)
                    with f.if_(w.field("err") != u32(0)):
                        f.ret()
                    with f.if_(esc.field("kind") != L.Ek.EkChar):
                        f.set(w.field("err"), u32(spec.E_INVALID_CLASS_RANGE))
                        f.set(w.field("erroff"), j)
                        f.ret()
                    f.set(hi, esc.field("val"))
                with f.else_():
                    # A POSIX name where a byte belongs is a range with no end,
                    # which pcre2 refuses before it looks the name up.
                    with f.if_(land(pat.at(j) == b("["), j + u32(1) < n)):
                        with f.if_(one_of(pat.at(j + u32(1)), ":.=")):
                            stop = tmp(f, u32, u32(spec.NONE))
                            f.call("posix_end", [pat, j + u32(1)], dest=stop)
                            with f.if_(stop != u32(spec.NONE)):
                                f.set(w.field("err"), u32(spec.E_INVALID_CLASS_RANGE))
                                f.set(w.field("erroff"), stop + u32(2))
                                f.ret()
                    f.set(hi, pat.at(j).cast(u32))
                    f.set(j, j + u32(1))
            with f.if_(hi < lo):
                f.set(w.field("err"), u32(spec.E_CLASS_RANGE_ORDER))
                f.set(w.field("erroff"), j)
                f.ret()
            f.call("note_element", [inout(w), lo, hi, boolean(True)])
            f.call("set_range", [inout(w), base, lo, hi, fold])
            f.set(f["quoting"], quoted)
            f.set(f["at"], j)
            f.ret()
    f.call("note_element", [inout(w), lo, lo, boolean(False)])
    f.call("set_range", [inout(w), base, lo, lo, fold])
    f.set(f["at"], i)

    f = L.func(
        "class_skip",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("quoting", boolean, "inout"),
        ],
    )
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    with f.while_(i + u32(1) < n, down(n, i)):
        with f.if_(pat.at(i) != u8(BACKSLASH)):
            f.brk()
        nxt = tmp(f, u8, pat.at(i + u32(1)))
        with f.if_(nxt == b("Q")):
            f.set(f["quoting"], boolean(True))
            f.set(i, i + u32(2))
            f.cont()
        with f.if_(nxt == b("E")):
            f.set(f["quoting"], boolean(False))
            f.set(i, i + u32(2))
            f.cont()
        f.brk()
    f.set(f["at"], i)

    f = L.func(
        "note_element",
        params=[
            ("w", L.Work, "inout"),
            ("lo", u32),
            ("hi", u32),
            ("ranged", boolean),
        ],
    )
    w = f["w"]
    # A range whose two ends are the same character is one character, which is
    # how pcre2's own parser rewrites it before the class is ever built.
    with f.if_(land(f["ranged"], f["lo"] != f["hi"])):
        f.set(w.field("clsrange"), u32(1))
    with f.else_():
        f.set(w.field("clselems"), w.field("clselems") + u32(1))
    with f.if_(
        lor(
            one_of(f["lo"].cast(u8), "\r\n"),
            one_of(f["hi"].cast(u8), "\r\n"),
        )
    ):
        f.set(w.field("clscrlf"), u32(1))

    # [:name:] and [:^name:]. Caseless turns lower and upper into alpha, which
    # is what pcre2 does, and is not the same as folding the resulting bitmap:
    # [[:^lower:]] stays "not a letter" rather than becoming everything.
    f = L.func(
        "posix_item",
        params=[
            ("w", L.Work, "inout"),
            ("pat", L.frozen_bytes),
            ("at", u32),
            ("stop", u32),
            ("base", u32),
            ("fold", boolean),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    off = tmp(f, u32, f["at"] + u32(2))
    negated = tmp(f, boolean, boolean(False))
    with f.if_(pat.at(off) == b("^")):
        f.set(negated, boolean(True))
        f.set(off, off + u32(1))
    which = tmp(f, u32, u32(255))
    nlen = tmp(f, u32, f["stop"] - off)
    f.call("posix_set", [pat, off, nlen], dest=which)
    with f.if_(which == u32(255)):
        f.set(w.field("err"), u32(spec.E_UNKNOWN_POSIX_CLASS))
        f.set(w.field("erroff"), f["stop"] + u32(2))
        f.ret()
    with f.if_(f["fold"]):
        with f.if_(lor(which == u32(spec.SET_INDEX["lower"]), which == u32(spec.SET_INDEX["upper"]))):
            f.set(which, u32(spec.SET_INDEX["alpha"]))
    base = tmp(f, u32, f["base"])
    f.call("set_union", [inout(w), base, which, negated])


# --- escapes ---


def _escapes(L: Layout) -> None:
    f = L.func(
        "read_escape",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
            ("incls", boolean),
        ],
        ret=L.Esc,
    )
    w = f["w"]
    pat = f["pat"]
    incls = f["incls"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"] + u32(1))
    bad = tmp(f, L.Esc, L.Esc.of(kind=L.Ek.EkErr, val=u32(0)))

    with f.if_(i >= n):
        f.set(w.field("err"), u32(spec.E_BACKSLASH_AT_END))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    c = tmp(f, u8, pat.at(i))
    f.set(i, i + u32(1))

    def literal(char: str, value: int) -> None:
        with f.if_(c == b(char)):
            f.set(f["at"], i)
            f.ret(L.Esc.of(kind=L.Ek.EkChar, val=u32(value)))

    literal("n", 0x0A)
    literal("r", 0x0D)
    literal("t", 0x09)
    literal("f", 0x0C)
    literal("a", 0x07)
    literal("e", 0x1B)

    def named_set(char: str, which: str, negated: bool) -> None:
        with f.if_(c == b(char)):
            f.set(f["at"], i)
            f.ret(
                L.Esc.of(
                    kind=L.Ek.EkNegSet if negated else L.Ek.EkSet,
                    val=u32(spec.SET_INDEX[which]),
                )
            )

    named_set("d", "digit", False)
    named_set("D", "digit", True)
    named_set("w", "word", False)
    named_set("W", "word", True)
    named_set("s", "space", False)
    named_set("S", "space", True)
    named_set("h", "hspace", False)
    named_set("H", "hspace", True)
    named_set("v", "vspace", False)
    named_set("V", "vspace", True)

    # \b is a word boundary outside a class and a backspace inside one.
    with f.if_(c == b("b")):
        f.set(f["at"], i)
        with f.if_(incls):
            f.ret(L.Esc.of(kind=L.Ek.EkChar, val=u32(8)))
        f.ret(L.Esc.of(kind=L.Ek.EkWordB, val=u32(0)))

    # Assertions, and the wave 2 and 3 spellings that share their fate inside a
    # class: pcre2 refuses all of them there, so that is a syntax error we
    # reproduce rather than an unsupported construct.
    with f.if_(one_of(c, "BAZzRGKXC")):
        with f.if_(incls):
            f.set(w.field("err"), u32(spec.E_BAD_CLASS_ESCAPE))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.set(f["at"], i)
        with f.if_(c == b("B")):
            f.ret(L.Esc.of(kind=L.Ek.EkNotWordB, val=u32(0)))
        with f.if_(c == b("A")):
            f.ret(L.Esc.of(kind=L.Ek.EkSod, val=u32(0)))
        with f.if_(c == b("Z")):
            f.ret(L.Esc.of(kind=L.Ek.EkEodn, val=u32(0)))
        with f.if_(c == b("z")):
            f.ret(L.Esc.of(kind=L.Ek.EkEod, val=u32(0)))
        with f.if_(c == b("R")):
            f.ret(L.Esc.of(kind=L.Ek.EkBsr, val=u32(0)))
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), i)
        f.ret(bad)

    with f.if_(c == b("N")):
        with f.if_(incls):
            f.set(w.field("err"), u32(spec.E_N_IN_CLASS))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), i)
        f.ret(bad)

    # The five escapes pcre2 spells out as unsupported in its own error.
    with f.if_(one_of(c, "FLlUu")):
        f.set(w.field("err"), u32(spec.E_NO_SUCH_BACKSLASH))
        f.set(w.field("erroff"), i)
        f.ret(bad)

    # \k and \g name a group, which only means anything outside a class;
    # inside one pcre2 reads them as the letters they are. Outside, the whole
    # reference is read the way pcre2 reads it, because a malformed one is a
    # genuine syntax error rather than an unsupported construct.
    with f.if_(one_of(c, "kg")):
        with f.if_(incls):
            f.set(f["at"], i)
            f.ret(L.Esc.of(kind=L.Ek.EkChar, val=c.cast(u32)))
        got = tmp(f, L.Esc)
        f.call("read_gk", [pat, inout(i), inout(w), c == b("g")], dest=got)
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        f.set(f["at"], i)
        f.ret(got)

    # Unicode properties are wave 3 wherever they appear, but their shape is
    # checked first, since pcre2 has its own error for a malformed one.
    with f.if_(one_of(c, "pP")):
        f.call("read_ucp", [pat, i, inout(w)])
        f.ret(bad)

    # \cX: the printable ASCII character X, upper-cased, with bit 0x40 flipped.
    with f.if_(c == b("c")):
        with f.if_(i >= n):
            f.set(w.field("err"), u32(spec.E_C_AT_END))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        d = tmp(f, u8, pat.at(i))
        f.set(i, i + u32(1))
        with f.if_(land(d >= b("a"), d <= b("z"))):
            f.set(d, d - u8(32))
        with f.if_(lor(d < u8(32), d > u8(126))):
            f.set(w.field("err"), u32(spec.E_C_NOT_PRINTABLE))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.set(f["at"], i)
        f.ret(L.Esc.of(kind=L.Ek.EkChar, val=(d ^ u8(0x40)).cast(u32)))

    with f.if_(c == b("x")):
        f.call("read_hex", [pat, inout(i), inout(w)], dest=bad)
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        f.set(f["at"], i)
        f.ret(bad)

    with f.if_(c == b("o")):
        f.call("read_octal_brace", [pat, inout(i), inout(w)], dest=bad)
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        f.set(f["at"], i)
        f.ret(bad)

    isdigit = tmp(f, boolean, boolean(False))
    f.call("ct", [c, u8(spec.CT_DIGIT)], dest=isdigit)
    with f.if_(isdigit):
        f.call("read_digit_escape", [pat, inout(i), inout(w), incls, c], dest=bad)
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        f.set(f["at"], i)
        f.ret(bad)

    # Inside 0x30..0x7a an unknown alphanumeric is an error; everything else
    # stands for itself, which is how pcre2's escape table reads.
    isalpha = tmp(f, boolean, boolean(False))
    f.call("ct", [c, u8(spec.CT_ALPHA)], dest=isalpha)
    with f.if_(isalpha):
        f.set(w.field("err"), u32(spec.E_UNRECOGNIZED_ESCAPE))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    f.set(f["at"], i)
    f.ret(L.Esc.of(kind=L.Ek.EkChar, val=c.cast(u32)))

    _hex(L)
    _octal(L)
    _references(L)


def _hex(L: Layout) -> None:
    f = L.func(
        "read_hex",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
        ],
        ret=L.Esc,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    bad = tmp(f, L.Esc, L.Esc.of(kind=L.Ek.EkErr, val=u32(0)))
    value = tmp(f, u32, u32(0))
    digits = tmp(f, u32, u32(0))
    ishex = tmp(f, boolean, boolean(False))

    with f.if_(land(i < n, pat.at(i) == b("{"))):
        f.set(i, i + u32(1))
        f.call("skip_blanks", [pat, inout(i)])
        with f.while_(i < n, down(n, i)):
            f.call("ct", [pat.at(i), u8(spec.CT_HEX)], dest=ishex)
            with f.if_(lnot(ishex)):
                f.brk()
            with f.if_(value <= u32(0x10FFFF)):
                nybble = tmp(f, u32, u32(0))
                f.call("hex_value", [pat.at(i)], dest=nybble)
                f.set(value, value * u32(16) + nybble)
            f.set(digits, digits + u32(1))
            f.set(i, i + u32(1))
        f.call("skip_blanks", [pat, inout(i)])
        # Which of the two errors this is depends on how the digits ran out:
        # a brace with nothing in it wants digits, anything else is a byte
        # that had no business being there.
        with f.if_(lor(i >= n, pat.at(i) != b("}"))):
            with f.if_(land(digits == u32(0), i >= n)):
                f.set(w.field("err"), u32(spec.E_MISSING_DIGITS))
                f.set(w.field("erroff"), i)
                f.ret(bad)
            f.set(w.field("err"), u32(spec.E_BAD_HEX_DIGIT))
            f.set(w.field("erroff"), i + u32(1))
            f.ret(bad)
        with f.if_(digits == u32(0)):
            f.set(w.field("err"), u32(spec.E_MISSING_DIGITS))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        with f.if_(value > u32(255)):
            f.set(w.field("err"), u32(spec.E_CODE_POINT_TOO_BIG))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.set(f["at"], i + u32(1))
        f.ret(L.Esc.of(kind=L.Ek.EkChar, val=value))

    with f.while_(land(digits < u32(2), i < n), down(u32(2), digits)):
        f.call("ct", [pat.at(i), u8(spec.CT_HEX)], dest=ishex)
        with f.if_(lnot(ishex)):
            f.brk()
        nybble = tmp(f, u32, u32(0))
        f.call("hex_value", [pat.at(i)], dest=nybble)
        f.set(value, value * u32(16) + nybble)
        f.set(digits, digits + u32(1))
        f.set(i, i + u32(1))
    with f.if_(digits == u32(0)):
        f.set(w.field("err"), u32(spec.E_MISSING_DIGITS))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    f.set(f["at"], i)
    f.ret(L.Esc.of(kind=L.Ek.EkChar, val=value))

    f = L.func("skip_blanks", params=[("pat", L.frozen_bytes), ("at", u32, "inout")])
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    with f.while_(i < n, down(n, i)):
        with f.if_(land(pat.at(i) != b(" "), pat.at(i) != u8(9))):
            f.brk()
        f.set(i, i + u32(1))
    f.set(f["at"], i)

    f = L.func("hex_value", params=[("c", u8)], ret=u32)
    with f.if_(f["c"] <= b("9")):
        f.ret((f["c"] - b("0")).cast(u32))
    f.ret(((f["c"] | u8(32)) - b("a") + u8(10)).cast(u32))


def _octal(L: Layout) -> None:
    f = L.func(
        "read_octal_brace",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
        ],
        ret=L.Esc,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    bad = tmp(f, L.Esc, L.Esc.of(kind=L.Ek.EkErr, val=u32(0)))
    with f.if_(lor(i >= n, pat.at(i) != b("{"))):
        f.set(w.field("err"), u32(spec.E_MISSING_OCTAL_BRACE))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    f.set(i, i + u32(1))
    f.call("skip_blanks", [pat, inout(i)])
    value = tmp(f, u32, u32(0))
    digits = tmp(f, u32, u32(0))
    isoct = tmp(f, boolean, boolean(False))
    with f.while_(i < n, down(n, i)):
        f.call("ct", [pat.at(i), u8(spec.CT_OCTAL)], dest=isoct)
        with f.if_(lnot(isoct)):
            f.brk()
        with f.if_(value <= u32(0x10FFFF)):
            f.set(value, value * u32(8) + (pat.at(i) - b("0")).cast(u32))
        f.set(digits, digits + u32(1))
        f.set(i, i + u32(1))
    f.call("skip_blanks", [pat, inout(i)])
    with f.if_(lor(i >= n, pat.at(i) != b("}"))):
        with f.if_(land(digits == u32(0), i >= n)):
            f.set(w.field("err"), u32(spec.E_MISSING_DIGITS))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.set(w.field("err"), u32(spec.E_BAD_OCTAL_DIGIT))
        f.set(w.field("erroff"), i + u32(1))
        f.ret(bad)
    with f.if_(digits == u32(0)):
        f.set(w.field("err"), u32(spec.E_MISSING_DIGITS))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    with f.if_(value > u32(255)):
        f.set(w.field("err"), u32(spec.E_CODE_POINT_TOO_BIG))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    f.set(f["at"], i + u32(1))
    f.ret(L.Esc.of(kind=L.Ek.EkChar, val=value))

    # \1 .. \9 are always back references outside a class; longer numbers are
    # one only when that many groups exist, and otherwise re-read as octal.
    # Whether the group exists is settled at the end of the parse, because a
    # forward reference is legal.
    f = L.func(
        "read_digit_escape",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
            ("incls", boolean),
            ("c", u8),
        ],
        ret=L.Esc,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    c = tmp(f, u8, f["c"])
    bad = tmp(f, L.Esc, L.Esc.of(kind=L.Ek.EkErr, val=u32(0)))
    isdigit = tmp(f, boolean, boolean(False))

    with f.if_(land(lnot(f["incls"]), c != b("0"))):
        j = tmp(f, u32, i - u32(1))
        number = tmp(f, u32, u32(0))
        with f.while_(j < n, down(n, j)):
            f.call("ct", [pat.at(j), u8(spec.CT_DIGIT)], dest=isdigit)
            with f.if_(lnot(isdigit)):
                f.brk()
            with f.if_(number <= u32(spec.MAX_QUANT)):
                f.set(number, number * u32(10) + (pat.at(j) - b("0")).cast(u32))
            f.set(j, j + u32(1))
        with f.if_(
            lor(lor(number < u32(10), c >= b("8")), number <= w.field("ncap"))
        ):
            # A number past pcre2's group ceiling can still be octal when its
            # first digit allows it; when it cannot, this is pcre2's own error.
            with f.if_(number > u32(spec.MAX_QUANT)):
                f.set(w.field("err"), u32(spec.E_NUMBER_TOO_BIG))
                f.set(w.field("erroff"), j)
                f.ret(bad)
            f.call("note_ref", [inout(w), number, j, u32(0)])
            with f.if_(w.field("err") != u32(0)):
                f.ret(bad)
            f.set(f["at"], j)
            f.ret(L.Esc.of(kind=L.Ek.EkNop, val=u32(0)))

    with f.if_(c >= b("8")):
        f.set(f["at"], i)
        f.ret(L.Esc.of(kind=L.Ek.EkChar, val=c.cast(u32)))

    value = tmp(f, u32, (c - b("0")).cast(u32))
    digits = tmp(f, u32, u32(0))
    isoct = tmp(f, boolean, boolean(False))
    with f.while_(land(digits < u32(2), i < n), down(u32(2), digits)):
        f.call("ct", [pat.at(i), u8(spec.CT_OCTAL)], dest=isoct)
        with f.if_(lnot(isoct)):
            f.brk()
        f.set(value, value * u32(8) + (pat.at(i) - b("0")).cast(u32))
        f.set(digits, digits + u32(1))
        f.set(i, i + u32(1))
    with f.if_(value > u32(255)):
        f.set(w.field("err"), u32(spec.E_OCTAL_TOO_BIG))
        f.set(w.field("erroff"), i)
        f.ret(bad)
    f.set(f["at"], i)
    f.ret(L.Esc.of(kind=L.Ek.EkChar, val=value))


def _references(L: Layout) -> None:
    """\\g, \\k and \\p, read to the letter of the pinned build.

    None of the three is supported in wave 1, but each has syntax pcre2
    checks before it looks at meaning, and DESIGN.md section 2.4 wants those
    genuine errors reproduced. So a reference is parsed whole, remembered, and
    judged at the end of the pass alongside the plain numeric ones; only a
    well-formed reference to a group that exists comes back as unsupported.
    """
    f = L.func(
        "note_ref",
        params=[("w", L.Work, "inout"), ("num", u32), ("off", u32), ("nlen", u32)],
    )
    w = f["w"]
    with f.if_(w.field("refs").len() >= u32(spec.MAX_REFS)):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()
    f.push(w.field("refs"), L.Ref.of(num=f["num"], off=f["off"], nlen=f["nlen"]))

    # Whether a signed or unsigned number starts here, which is the question
    # pcre2 answers by trying read_number and falling back to a name.
    f = L.func("ref_number_ahead", params=[("pat", L.frozen_bytes), ("at", u32)], ret=boolean)
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    isdigit = tmp(f, boolean, boolean(False))
    with f.if_(i >= n):
        f.ret(boolean(False))
    c = tmp(f, u8, pat.at(i))
    with f.if_(lor(c == b("+"), c == b("-"))):
        with f.if_(i + u32(1) >= n):
            f.ret(boolean(False))
        f.call("ct", [pat.at(i + u32(1)), u8(spec.CT_DIGIT)], dest=isdigit)
        f.ret(isdigit)
    f.call("ct", [c, u8(spec.CT_DIGIT)], dest=isdigit)
    f.ret(isdigit)

    # A group number, possibly signed and then relative to the groups opened
    # so far. `valerr` is where a bad value is blamed: pcre2 reads a delimited
    # number through a scratch pointer, so those errors point at the opening
    # delimiter, while an undelimited number is blamed just past its digits —
    # which is what NONE selects.
    f = L.func(
        "read_ref_number",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
            ("valerr", u32),
        ],
        ret=u32,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    plus = tmp(f, boolean, pat.at(i) == b("+"))
    minus = tmp(f, boolean, pat.at(i) == b("-"))
    with f.if_(lor(plus, minus)):
        f.set(i, i + u32(1))
    value = tmp(f, u32, u32(0))
    isdigit = tmp(f, boolean, boolean(False))
    with f.while_(i < n, down(n, i)):
        f.call("ct", [pat.at(i), u8(spec.CT_DIGIT)], dest=isdigit)
        with f.if_(lnot(isdigit)):
            f.brk()
        with f.if_(value <= u32(spec.MAX_QUANT)):
            f.set(value, value * u32(10) + (pat.at(i) - b("0")).cast(u32))
        f.set(i, i + u32(1))
    f.set(f["at"], i)
    blame = tmp(f, u32, f["valerr"])
    with f.if_(blame == u32(spec.NONE)):
        f.set(blame, i)
    # A forward reference eats into the room under pcre2's group ceiling,
    # which is how read_number's shrunken max_value behaves.
    limit = tmp(f, u32, u32(spec.MAX_QUANT))
    with f.if_(plus):
        f.set(limit, u32(spec.MAX_QUANT) - w.field("ncap"))
    with f.if_(value > limit):
        f.set(w.field("err"), u32(spec.E_NUMBER_TOO_BIG))
        f.set(w.field("erroff"), blame)
        f.ret(u32(spec.NONE))
    with f.if_(land(lor(plus, minus), value == u32(0))):
        f.set(w.field("err"), u32(spec.E_ZERO_RELATIVE))
        f.set(w.field("erroff"), blame)
        f.ret(u32(spec.NONE))
    with f.if_(minus):
        with f.if_(value > w.field("ncap")):
            f.set(w.field("err"), u32(spec.E_NO_SUCH_GROUP))
            f.set(w.field("erroff"), blame)
            f.ret(u32(spec.NONE))
        f.set(value, w.field("ncap") + u32(1) - value)
    with f.if_(plus):
        f.set(value, w.field("ncap") + value)
    f.ret(value)

    # \g and \k outside a class, `at` sitting just past the letter.
    f = L.func(
        "read_gk",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
            ("isg", boolean),
        ],
        ret=L.Esc,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    bad = tmp(f, L.Esc, L.Esc.of(kind=L.Ek.EkErr, val=u32(0)))
    nop = tmp(f, L.Esc, L.Esc.of(kind=L.Ek.EkNop, val=u32(0)))
    d = tmp(f, u8, u8(0))
    with f.if_(i < n):
        f.set(d, pat.at(i))
    numeric = tmp(f, boolean, boolean(False))
    number = tmp(f, u32, u32(0))

    with f.if_(lnot(lor(d == b("{"), lor(d == b("<"), d == b("'"))))):
        with f.if_(lnot(f["isg"])):
            f.set(w.field("err"), u32(spec.E_BAD_K_ESCAPE))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        # \g also takes a bare number, relative when it is signed.
        f.call("ref_number_ahead", [pat, i], dest=numeric)
        with f.if_(lnot(numeric)):
            f.set(w.field("err"), u32(spec.E_BAD_G_ESCAPE))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.call("read_ref_number", [pat, inout(i), inout(w), u32(spec.NONE)], dest=number)
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        with f.if_(number == u32(0)):
            f.set(w.field("err"), u32(spec.E_NO_SUCH_GROUP))
            f.set(w.field("erroff"), i)
            f.ret(bad)
        f.call("note_ref", [inout(w), number, i, u32(0)])
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        f.set(f["at"], i)
        f.ret(nop)

    term = tmp(f, u8, b("}"))
    with f.if_(d == b("<")):
        f.set(term, b(">"))
    with f.if_(d == b("'")):
        f.set(term, b("'"))
    braced = tmp(f, boolean, d == b("{"))
    j = tmp(f, u32, i + u32(1))
    with f.if_(braced):
        f.call("skip_blanks", [pat, inout(j)])

    # Only \g reads numbers; a braced number is a back reference and an
    # angle-bracketed or quoted one is a subroutine call, but wave 1 refuses
    # both the same way, so all that matters here is validity.
    with f.if_(f["isg"]):
        f.call("ref_number_ahead", [pat, j], dest=numeric)
    with f.if_(numeric):
        f.call("read_ref_number", [pat, inout(j), inout(w), i], dest=number)
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        with f.if_(braced):
            f.call("skip_blanks", [pat, inout(j)])
        with f.if_(lor(j >= n, pat.at(j) != term)):
            f.set(w.field("err"), u32(spec.E_NUMBER_TERMINATOR))
            f.set(w.field("erroff"), j)
            f.ret(bad)
        f.set(j, j + u32(1))
        # \g{0} refers to nothing, but \g<0> recurses the whole pattern, and
        # pcre2 accepts that.
        with f.if_(land(braced, number == u32(0))):
            f.set(w.field("err"), u32(spec.E_NO_SUCH_GROUP))
            f.set(w.field("erroff"), j)
            f.ret(bad)
        f.call("note_ref", [inout(w), number, j, u32(0)])
        with f.if_(w.field("err") != u32(0)):
            f.ret(bad)
        f.set(f["at"], j)
        f.ret(nop)

    # A name, read the way named_group reads one, except that the errors sit
    # where pcre2's read_name leaves its pointer.
    with f.if_(j >= n):
        f.set(w.field("err"), u32(spec.E_NAME_EXPECTED))
        f.set(w.field("erroff"), j)
        f.ret(bad)
    isdigit = tmp(f, boolean, boolean(False))
    f.call("ct", [pat.at(j), u8(spec.CT_DIGIT)], dest=isdigit)
    with f.if_(isdigit):
        f.set(w.field("err"), u32(spec.E_NAME_STARTS_WITH_DIGIT))
        f.set(w.field("erroff"), j + u32(1))
        f.ret(bad)
    start = tmp(f, u32, j)
    isword = tmp(f, boolean, boolean(False))
    with f.while_(j < n, down(n, j)):
        f.call("ct", [pat.at(j), u8(spec.CT_WORD)], dest=isword)
        with f.if_(lnot(isword)):
            f.brk()
        f.set(j, j + u32(1))
    with f.if_(j == start):
        f.set(w.field("err"), u32(spec.E_NAME_EXPECTED))
        f.set(w.field("erroff"), start)
        f.ret(bad)
    nlen = tmp(f, u32, j - start)
    with f.if_(nlen > u32(spec.MAX_NAME)):
        f.set(w.field("err"), u32(spec.E_NAME_TOO_LONG))
        f.set(w.field("erroff"), j)
        f.ret(bad)
    with f.if_(braced):
        f.call("skip_blanks", [pat, inout(j)])
    with f.if_(lor(j >= n, pat.at(j) != term)):
        f.set(w.field("err"), u32(spec.E_BAD_NAME_TERMINATOR))
        f.set(w.field("erroff"), j)
        f.ret(bad)
    f.call("note_ref", [inout(w), u32(spec.NONE), start, nlen])
    with f.if_(w.field("err") != u32(0)):
        f.ret(bad)
    f.set(f["at"], j + u32(1))
    f.ret(nop)

    # \p and \P, whose shape is pcre2's get_ucp. Always ends in an error:
    # malformed is pcre2's own code, well formed is our refusal.
    f = L.func(
        "read_ucp",
        params=[("pat", L.frozen_bytes), ("at", u32), ("w", L.Work, "inout")],
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    with f.if_(i >= n):
        f.set(w.field("err"), u32(spec.E_MALFORMED_UCP))
        f.set(w.field("erroff"), i)
        f.ret()
    c = tmp(f, u8, pat.at(i))
    f.set(i, i + u32(1))
    with f.if_(c == b("{")):
        neg = tmp(f, boolean, boolean(False))
        sig = tmp(f, u32, u32(0))
        closed = tmp(f, boolean, boolean(False))
        with f.while_(i < n, down(n, i)):
            ch = tmp(f, u8, pat.at(i))
            f.set(i, i + u32(1))
            # Unicode's loose matching: blanks, hyphens and underscores in a
            # property name say nothing.
            with f.if_(
                lor(
                    lor(ch == b("_"), ch == b("-")),
                    lor(ch == b(" "), land(ch >= u8(0x09), ch <= u8(0x0D))),
                )
            ):
                f.cont()
            with f.if_(land(land(sig == u32(0), lnot(neg)), ch == b("^"))):
                f.set(neg, boolean(True))
                f.cont()
            with f.if_(ch == b("}")):
                f.set(closed, boolean(True))
                f.brk()
            with f.if_(lor(ch < b("&"), ch > b("z"))):
                f.set(w.field("err"), u32(spec.E_MALFORMED_UCP))
                f.set(w.field("erroff"), i)
                f.ret()
            f.set(sig, sig + u32(1))
            # pcre2's name buffer holds 49 characters, so a longer name can
            # only be malformed.
            with f.if_(sig >= u32(49)):
                f.brk()
        with f.if_(lnot(closed)):
            f.set(w.field("err"), u32(spec.E_MALFORMED_UCP))
            f.set(w.field("erroff"), i)
            f.ret()
        # An empty name is unknown whatever the tables would say.
        with f.if_(sig == u32(0)):
            f.set(w.field("err"), u32(spec.E_UNKNOWN_PROPERTY))
            f.set(w.field("erroff"), i)
            f.ret()
        # Well formed, so this is wave 3's feature rather than a syntax error.
        # The name is not checked against the property tables — those are wave
        # 3's as well — so a name pcre2 would refuse as unknown comes back
        # unsupported instead, a narrowing the differential lane tolerates by
        # skipping what we decline.
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), i)
        f.ret()
    isalpha = tmp(f, boolean, boolean(False))
    f.call("ct", [c, u8(spec.CT_ALPHA)], dest=isalpha)
    with f.if_(lnot(isalpha)):
        f.set(w.field("err"), u32(spec.E_MALFORMED_UCP))
        f.set(w.field("erroff"), i)
        f.ret()
    # One-letter properties have a name table of their own, which is wave 3's
    # for the same reason.
    f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
    f.set(w.field("erroff"), i)


# --- quantifiers ---


def _quantifiers(L: Layout) -> None:
    # `{...}` is a quantifier only when it reads as one; anything else is the
    # literal brace pcre2 also accepts. Spaces inside the braces are skipped,
    # which the pinned build does whether or not EXTENDED is set.
    f = L.func(
        "read_braces",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32),
            ("w", L.Work, "inout"),
        ],
        ret=L.Quant,
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"] + u32(1))
    no = tmp(f, L.Quant, L.Quant.of(ok=boolean(False), lo=u32(0), hi=u32(0), end=u32(0)))
    isdigit = tmp(f, boolean, boolean(False))

    def skip_space() -> None:
        f.call("skip_blanks", [pat, inout(i)])

    lo = tmp(f, u32, u32(0))
    hi = tmp(f, u32, u32(spec.NONE))
    has_lo = tmp(f, boolean, boolean(False))
    has_hi = tmp(f, boolean, boolean(False))
    ends = tmp(f, u32, u32(0))

    skip_space()
    with f.while_(i < n, down(n, i)):
        f.call("ct", [pat.at(i), u8(spec.CT_DIGIT)], dest=isdigit)
        with f.if_(lnot(isdigit)):
            f.brk()
        f.set(has_lo, boolean(True))
        with f.if_(lo <= u32(spec.MAX_QUANT)):
            f.set(lo, lo * u32(10) + (pat.at(i) - b("0")).cast(u32))
        f.set(i, i + u32(1))
    f.set(ends, i)
    lo_end = tmp(f, u32, i)
    skip_space()

    with f.if_(land(i < n, pat.at(i) == b(","))):
        f.set(i, i + u32(1))
        skip_space()
        with f.while_(i < n, down(n, i)):
            f.call("ct", [pat.at(i), u8(spec.CT_DIGIT)], dest=isdigit)
            with f.if_(lnot(isdigit)):
                f.brk()
            with f.if_(lnot(has_hi)):
                f.set(hi, u32(0))
                f.set(has_hi, boolean(True))
            with f.if_(hi <= u32(spec.MAX_QUANT)):
                f.set(hi, hi * u32(10) + (pat.at(i) - b("0")).cast(u32))
            f.set(i, i + u32(1))
        f.set(ends, i)
        skip_space()
    with f.else_():
        f.set(hi, lo)

    with f.if_(lnot(lor(has_lo, has_hi))):
        f.ret(no)
    with f.if_(lor(i >= n, pat.at(i) != b("}"))):
        f.ret(no)
    # A bound that is too large is reported where its own digits ran out, and
    # only once the braces have turned out to be a quantifier at all: `{85125r`
    # never closes, so it is the literal text pcre2 also reads it as.
    with f.if_(lo > u32(spec.MAX_QUANT)):
        f.set(w.field("err"), u32(spec.E_QUANTIFIER_TOO_BIG))
        f.set(w.field("erroff"), lo_end)
        f.ret(no)
    with f.if_(land(has_hi, hi > u32(spec.MAX_QUANT))):
        f.set(w.field("err"), u32(spec.E_QUANTIFIER_TOO_BIG))
        f.set(w.field("erroff"), ends)
        f.ret(no)
    with f.if_(hi < lo):
        f.set(w.field("err"), u32(spec.E_QUANTIFIER_ORDER))
        f.set(w.field("erroff"), ends)
        f.ret(no)
    f.ret(L.Quant.of(ok=boolean(True), lo=lo, hi=hi, end=i + u32(1)))

    # Wrapping the previous item in a repeat rewrites its arena slot, so the
    # parent's child list never has to be touched.
    f = L.func(
        "apply_quant",
        params=[
            ("w", L.Work, "inout"),
            ("lo", u32),
            ("hi", u32),
            ("greedy", boolean),
            ("erroff", u32),
        ],
    )
    w = f["w"]
    top = tmp(f, u32, w.field("frames").len() - u32(1))
    q = tmp(f, u32, w.field("frames").at(top).field("qual"))
    with f.if_(q == u32(0)):
        f.set(w.field("err"), u32(spec.E_NOTHING_TO_REPEAT))
        f.set(w.field("erroff"), f["erroff"])
        f.ret()
    kind = tmp(f, L.Nd, w.field("nodes").at(q).field("kind"))
    repeatable = tmp(f, boolean, boolean(True))
    with f.switch(kind) as arm:
        for name in (
            "NdRepeat",
            "NdCirc",
            "NdCircM",
            "NdDoll",
            "NdDollE",
            "NdDollM",
            "NdSod",
            "NdEod",
            "NdEodn",
            "NdWordB",
            "NdNotWordB",
        ):
            with arm.case(name):
                f.set(repeatable, boolean(False))
        with arm.otherwise():
            pass
    with f.if_(lnot(repeatable)):
        f.set(w.field("err"), u32(spec.E_NOTHING_TO_REPEAT))
        f.set(w.field("erroff"), f["erroff"])
        f.ret()
    inner = tmp(f, u32, u32(0))
    kept = tmp(f, L.Node, w.field("nodes").at(q))
    f.call(
        "alloc_node",
        [
            inout(w),
            kept.field("kind"),
            kept.field("val"),
            kept.field("aux"),
            kept.field("opts"),
        ],
        dest=inner,
    )
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    f.set(w.field("nodes").at(inner).field("first"), kept.field("first"))
    f.set(w.field("nodes").at(inner).field("last"), kept.field("last"))
    f.set(w.field("nodes").at(q).field("kind"), L.Nd.NdRepeat)
    f.set(w.field("nodes").at(q).field("val"), f["lo"])
    f.set(w.field("nodes").at(q).field("aux"), f["hi"])
    f.set(w.field("nodes").at(q).field("opts"), f["greedy"].cast(u32))
    f.set(w.field("nodes").at(q).field("first"), inner)
    f.set(w.field("nodes").at(q).field("last"), inner)


# --- groups ---


def _groups(L: Layout) -> None:
    f = L.func(
        "push_frame",
        params=[
            ("w", L.Work, "inout"),
            ("capno", u32),
            ("nopts", u32),
            ("at", u32),
            ("unsup", u32),
        ],
    )
    w = f["w"]
    with f.if_(w.field("frames").len() > u32(spec.MAX_DEPTH)):
        f.set(w.field("err"), u32(spec.E_TOO_DEEP))
        f.set(w.field("erroff"), f["at"] + u32(1))
        f.ret()
    grp = tmp(f, u32, u32(0))
    cap = tmp(f, u32, f["capno"])
    f.call("alloc_node", [inout(w), L.Nd.NdGroup, cap, u32(0), u32(0)], dest=grp)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    cat = tmp(f, u32, u32(0))
    f.call("alloc_node", [inout(w), L.Nd.NdConcat, u32(0), u32(0), u32(0)], dest=cat)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    f.call("add_child", [inout(w), grp, cat])
    top = tmp(f, u32, w.field("frames").len() - u32(1))
    outer = tmp(f, u32, w.field("frames").at(top).field("cat"))
    f.call("add_child", [inout(w), outer, grp])
    saved = tmp(f, u32, w.field("opts"))
    at = tmp(f, u32, f["at"])
    unsup = tmp(f, u32, f["unsup"])
    f.push(
        w.field("frames"),
        L.Frame.of(
            grp=grp, alt=u32(0), cat=cat, qual=u32(0), opts=saved, at=at, unsup=unsup
        ),
    )
    f.set(w.field("opts"), f["nopts"])

    _open_group(L)


def _open_group(L: Layout) -> None:
    f = L.func(
        "open_group",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"] + u32(1))
    here = tmp(f, u32, f["at"])

    # (*VERB), (*MARK:...) and (*alpha_assertion:...) all start here. Only a
    # bare (*) is an ordinary group whose first item happens to be a star.
    with f.if_(
        land(
            land(i < n, pat.at(i) == b("*")),
            land(i + u32(1) < n, pat.at(i + u32(1)) != b(")")),
        )
    ):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), i + u32(1))
        f.ret()

    with f.if_(lor(i >= n, pat.at(i) != b("?"))):
        with f.if_(w.field("ncap") >= u32(spec.MAX_GROUPS)):
            f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
            f.ret()
        cap = tmp(f, u32, w.field("ncap") + u32(1))
        f.set(w.field("ncap"), cap)
        keep = tmp(f, u32, w.field("opts"))
        f.call("push_frame", [inout(w), cap, keep, here, u32(0)])
        f.set(f["at"], i)
        f.ret()

    j = tmp(f, u32, i + u32(1))
    with f.if_(j >= n):
        f.set(w.field("err"), u32(spec.E_MISSING_PAREN))
        f.set(w.field("erroff"), n)
        f.ret()
    d = tmp(f, u8, pat.at(j))

    # (?#...) is a comment, skipped whole; it leaves the previous item alone,
    # which is why `a(?#x)*` repeats the a and `a(?i)*` does not.
    with f.if_(d == b("#")):
        k = tmp(f, u32, j + u32(1))
        with f.while_(land(k < n, pat.at(k) != b(")")), down(n, k)):
            f.set(k, k + u32(1))
        with f.if_(k >= n):
            f.set(w.field("err"), u32(spec.E_MISSING_COMMENT_PAREN))
            f.set(w.field("erroff"), n)
            f.ret()
        f.set(f["at"], k + u32(1))
        f.ret()

    with f.if_(d == b(":")):
        keep = tmp(f, u32, w.field("opts"))
        f.call("push_frame", [inout(w), u32(0), keep, here, u32(0)])
        f.set(f["at"], j + u32(1))
        f.ret()

    # (?= (?! (?> (?| (?* and the two (?< forms are groups with a body, so the
    # body is parsed and the refusal waits until the group closes. That leaves
    # an unterminated one reported as the missing parenthesis it is.
    body = tmp(f, u32, u32(0))
    with f.if_(one_of(d, "=!>|*")):
        f.set(body, j + u32(1))
    with f.if_(land(d == b("<"), land(j + u32(1) < n, one_of(pat.at(j + u32(1)), "=!*")))):
        f.set(body, j + u32(2))
    with f.if_(body != u32(0)):
        keep = tmp(f, u32, w.field("opts"))
        f.call("push_frame", [inout(w), u32(0), keep, here, body])
        f.set(f["at"], body)
        f.ret()

    # Named groups, in the three spellings pcre2 accepts.
    named = tmp(f, boolean, boolean(False))
    term = tmp(f, u8, b(">"))
    start = tmp(f, u32, u32(0))
    with f.if_(d == b("<")):
        f.set(named, boolean(True))
        f.set(start, j + u32(1))
    with f.if_(d == b("'")):
        f.set(named, boolean(True))
        f.set(term, b("'"))
        f.set(start, j + u32(1))
    with f.if_(land(d == b("P"), land(j + u32(1) < n, pat.at(j + u32(1)) == b("<")))):
        f.set(named, boolean(True))
        f.set(start, j + u32(2))
    with f.if_(named):
        f.call("named_group", [pat, inout(f["at"]), inout(w), start, term, here])
        f.ret()

    # Everything else pcre2 spells with (? and we do not do yet: lookaround,
    # atomic and non-atomic groups, subroutine calls and recursion, callouts,
    # conditionals, branch reset, and the extended class syntax.
    with f.if_(one_of(d, "&+RPC([")):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), j + u32(1))
        f.ret()
    isdigit = tmp(f, boolean, boolean(False))
    f.call("ct", [d, u8(spec.CT_DIGIT)], dest=isdigit)
    with f.if_(land(d == b("-"), j + u32(1) < n)):
        f.call("ct", [pat.at(j + u32(1)), u8(spec.CT_DIGIT)], dest=isdigit)
        with f.if_(isdigit):
            f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
            f.set(w.field("erroff"), j + u32(2))
            f.ret()
        f.set(isdigit, boolean(False))
    with f.if_(isdigit):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), j + u32(1))
        f.ret()

    # Option letters, set before a '-' and cleared after it. A letter the
    # pinned build takes here and we do not — (?n), (?J), (?a) and its ASCII
    # sub-letters, (?r), (?^) — is read like any other, and only refused once
    # the group turns out to be well formed. Otherwise an unterminated (?a
    # would come back as an unsupported option rather than as the missing
    # parenthesis it is.
    on = tmp(f, u32, u32(0))
    off = tmp(f, u32, u32(0))
    neg = tmp(f, boolean, boolean(False))
    ours = tmp(f, boolean, boolean(True))
    ascii_mode = tmp(f, boolean, boolean(False))
    reset = tmp(f, boolean, boolean(False))
    k = tmp(f, u32, j)
    with f.while_(k < n, down(n, k)):
        e = tmp(f, u8, pat.at(k))
        with f.if_(e == b("-")):
            # There is one hyphen in an option setting, it clears what follows
            # it, and it never follows the (?^ that clears everything already.
            with f.if_(lor(neg, reset)):
                f.set(w.field("err"), u32(spec.E_BAD_HYPHEN))
                f.set(w.field("erroff"), k + u32(1))
                f.ret()
            f.set(neg, boolean(True))
            f.set(k, k + u32(1))
            f.cont()
        bit = tmp(f, u32, u32(0))
        for letter, value in spec.INLINE_OPTIONS.items():
            with f.if_(e == u8(letter)):
                f.set(bit, u32(value))
        with f.if_(bit == u32(0)):
            # (?^...) resets every option and only means that as the first
            # thing after the (?, so anywhere else it is not an option letter.
            with f.if_(
                lnot(
                    lor(
                        lor(one_of(e, "aJnr"), land(e == b("^"), k == j)),
                        land(ascii_mode, one_of(e, "DPSTW")),
                    )
                )
            ):
                f.brk()
            f.set(ascii_mode, e == b("a"))
            f.set(reset, e == b("^"))
            f.set(ours, boolean(False))
            f.set(k, k + u32(1))
            f.cont()
        f.set(ascii_mode, boolean(False))
        f.set(reset, boolean(False))
        # (?xx) is pcre2's EXTENDED_MORE, which strips whitespace inside a
        # class as well, so it is a different option rather than a repeat.
        with f.if_(land(e == b("x"), land(k + u32(1) < n, pat.at(k + u32(1)) == b("x")))):
            f.set(ours, boolean(False))
        with f.if_(neg):
            f.set(off, off | bit)
        with f.else_():
            f.set(on, on | bit)
        f.set(k, k + u32(1))

    with f.if_(k >= n):
        f.set(w.field("err"), u32(spec.E_MISSING_PAREN))
        f.set(w.field("erroff"), n)
        f.ret()
    with f.if_(land(pat.at(k) != b(")"), pat.at(k) != b(":"))):
        f.set(w.field("err"), u32(spec.E_UNRECOGNIZED_AFTER_QUERY))
        f.set(w.field("erroff"), k + u32(1))
        f.ret()
    with f.if_(lnot(ours)):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_OPTION))
        f.set(w.field("erroff"), k + u32(1))
        f.ret()

    settled = tmp(f, u32, (w.field("opts") | on) & ~off)
    with f.if_(pat.at(k) == b(":")):
        f.call("push_frame", [inout(w), u32(0), settled, here, u32(0)])
        f.set(f["at"], k + u32(1))
        f.ret()
    f.set(w.field("opts"), settled)
    top = tmp(f, u32, w.field("frames").len() - u32(1))
    f.set(w.field("frames").at(top).field("qual"), u32(0))
    f.set(f["at"], k + u32(1))

    _named_group(L)


def _named_group(L: Layout) -> None:
    f = L.func(
        "named_group",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
            ("start", u32),
            ("term", u8),
            ("here", u32),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    # A group name is a run of word characters, and every way it can go wrong
    # has its own pcre2 code: a leading digit, no name at all, one too long,
    # and a run that stops somewhere other than the terminator.
    n = tmp(f, u32, pat.len())
    start = tmp(f, u32, f["start"])
    isdigit = tmp(f, boolean, boolean(False))
    with f.if_(start < n):
        f.call("ct", [pat.at(start), u8(spec.CT_DIGIT)], dest=isdigit)
    with f.if_(isdigit):
        f.set(w.field("err"), u32(spec.E_NAME_STARTS_WITH_DIGIT))
        f.set(w.field("erroff"), start + u32(1))
        f.ret()
    k = tmp(f, u32, start)
    isword = tmp(f, boolean, boolean(False))
    with f.while_(k < n, down(n, k)):
        f.call("ct", [pat.at(k), u8(spec.CT_WORD)], dest=isword)
        with f.if_(lnot(isword)):
            f.brk()
        f.set(k, k + u32(1))
    nlen = tmp(f, u32, k - start)
    with f.if_(nlen == u32(0)):
        f.set(w.field("err"), u32(spec.E_NAME_EXPECTED))
        f.set(w.field("erroff"), start)
        f.ret()
    with f.if_(nlen > u32(spec.MAX_NAME)):
        f.set(w.field("err"), u32(spec.E_NAME_TOO_LONG))
        f.set(w.field("erroff"), k)
        f.ret()
    with f.if_(lor(k >= n, pat.at(k) != f["term"])):
        f.set(w.field("err"), u32(spec.E_BAD_NAME_TERMINATOR))
        f.set(w.field("erroff"), k)
        f.ret()
    dup = tmp(f, boolean, boolean(False))
    f.call("name_taken", [pat, start, nlen, inout(w)], dest=dup)
    with f.if_(dup):
        f.set(w.field("err"), u32(spec.E_DUPLICATE_NAME))
        f.set(w.field("erroff"), k + u32(1))
        f.ret()
    with f.if_(
        lor(
            w.field("ncap") >= u32(spec.MAX_GROUPS),
            lor(
                w.field("nname") >= u32(spec.MAX_NAMES),
                w.field("names").len() + nlen > u32(spec.MAX_NAME_BYTES),
            ),
        )
    ):
        f.set(w.field("err"), u32(spec.E_PATTERN_TOO_LARGE))
        f.ret()
    cap = tmp(f, u32, w.field("ncap") + u32(1))
    f.set(w.field("ncap"), cap)
    off = tmp(f, u32, w.field("names").len())
    f.push(w.field("nameents"), L.NameEnt.of(off=off, nlen=nlen, grp=cap))
    f.set(w.field("nname"), w.field("nname") + u32(1))
    p = tmp(f, u32, u32(0))
    with f.while_(p < nlen, down(nlen, p)):
        byte = tmp(f, u8, pat.at(start + p))
        f.push(w.field("names"), byte)
        f.set(p, p + u32(1))
    keep = tmp(f, u32, w.field("opts"))
    here = tmp(f, u32, f["here"])
    f.call("push_frame", [inout(w), cap, keep, here, u32(0)])
    f.set(f["at"], k + u32(1))

    f = L.func(
        "name_taken",
        params=[
            ("pat", L.frozen_bytes),
            ("off", u32),
            ("nlen", u32),
            ("w", L.Work, "inout"),
        ],
        ret=boolean,
    )
    w = f["w"]
    e = tmp(f, u32, u32(0))
    total = tmp(f, u32, w.field("nameents").len())
    with f.while_(e < total, down(total, e)):
        ent = tmp(f, L.NameEnt, w.field("nameents").at(e))
        with f.if_(ent.field("nlen") == f["nlen"]):
            k = tmp(f, u32, u32(0))
            same = tmp(f, boolean, boolean(True))
            with f.while_(k < f["nlen"], down(f["nlen"], k)):
                with f.if_(
                    w.field("names").at(ent.field("off") + k) != f["pat"].at(f["off"] + k)
                ):
                    f.set(same, boolean(False))
                    f.brk()
                f.set(k, k + u32(1))
            with f.if_(same):
                f.ret(boolean(True))
        f.set(e, e + u32(1))
    f.ret(boolean(False))


# --- the main pass ---


def _parse(L: Layout) -> None:
    f = L.func(
        "parse",
        params=[
            ("pat", L.frozen_bytes),
            ("popts", u32),
            ("nltype", u32),
            ("w", L.Work, "inout"),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    nil = tmp(f, u32, u32(0))
    f.call("alloc_node", [inout(w), L.Nd.NdNil, u32(0), u32(0), u32(0)], dest=nil)
    grp = tmp(f, u32, u32(0))
    f.call("alloc_node", [inout(w), L.Nd.NdGroup, u32(0), u32(0), u32(0)], dest=grp)
    cat = tmp(f, u32, u32(0))
    f.call("alloc_node", [inout(w), L.Nd.NdConcat, u32(0), u32(0), u32(0)], dest=cat)
    f.call("add_child", [inout(w), grp, cat])
    f.set(w.field("root"), grp)
    f.set(w.field("opts"), f["popts"])
    f.set(w.field("nltype"), f["nltype"])
    popts = tmp(f, u32, f["popts"])
    f.push(
        w.field("frames"),
        L.Frame.of(
            grp=grp, alt=u32(0), cat=cat, qual=u32(0), opts=popts, at=u32(0), unsup=u32(0)
        ),
    )

    i = tmp(f, u32, u32(0))
    quoting = tmp(f, boolean, boolean(False))
    isspace = tmp(f, boolean, boolean(False))
    esc = tmp(f, L.Esc)
    quant = tmp(f, L.Quant)

    with f.while_(land(i < n, w.field("err") == u32(0)), down(n, i)):
        c = tmp(f, u8, pat.at(i))

        with f.if_(quoting):
            with f.if_(
                land(c == u8(BACKSLASH), land(i + u32(1) < n, pat.at(i + u32(1)) == b("E")))
            ):
                f.set(quoting, boolean(False))
                f.set(i, i + u32(2))
                f.cont()
            value = tmp(f, u32, c.cast(u32))
            f.call("add_char", [inout(w), value])
            f.set(i, i + u32(1))
            f.cont()

        with f.if_((w.field("opts") & u32(spec.EXTENDED)) != u32(0)):
            f.call("ct", [c, u8(spec.CT_SPACE)], dest=isspace)
            with f.if_(lor(isspace, c == b("#"))):
                f.call("skip_gaps", [pat, inout(i), inout(w)])
                f.cont()

        with f.if_(c == b("(")):
            f.call("open_group", [pat, inout(i), inout(w)])
            f.cont()

        with f.if_(c == b(")")):
            with f.if_(w.field("frames").len() <= u32(1)):
                f.set(w.field("err"), u32(spec.E_UNMATCHED_PAREN))
                f.set(w.field("erroff"), i + u32(1))
                f.cont()
            f.call("close_group", [inout(w)])
            f.set(i, i + u32(1))
            f.cont()

        with f.if_(c == b("|")):
            f.call("new_branch", [inout(w)])
            f.set(i, i + u32(1))
            f.cont()

        with f.if_(c == b("[")):
            with f.if_(land(i + u32(1) < n, one_of(pat.at(i + u32(1)), ":.="))):
                stop = tmp(f, u32, u32(spec.NONE))
                f.call("posix_end", [pat, i + u32(1)], dest=stop)
                with f.if_(stop != u32(spec.NONE)):
                    bad = tmp(
                        f,
                        u32,
                        u32(spec.E_POSIX_OUTSIDE_CLASS),
                    )
                    with f.if_(pat.at(i + u32(1)) != b(":")):
                        f.set(bad, u32(spec.E_POSIX_COLLATING))
                    f.set(w.field("err"), bad)
                    f.set(w.field("erroff"), stop + u32(2))
                    f.cont()
            idx = tmp(f, u32, u32(0))
            f.call("parse_class", [pat, inout(i), inout(w)], dest=idx)
            with f.if_(w.field("err") != u32(0)):
                f.cont()
            f.call("attach_atom", [inout(w), L.Nd.NdClass, idx, u32(0)])
            f.cont()

        with f.if_(c == b(".")):
            dot = tmp(f, L.Nd, L.Nd.NdAnyNoNL)
            with f.if_((w.field("opts") & u32(spec.DOTALL)) != u32(0)):
                f.set(dot, L.Nd.NdAny)
            f.call("attach_atom", [inout(w), dot, u32(0), u32(0)])
            f.set(i, i + u32(1))
            f.cont()

        with f.if_(c == b("^")):
            circ = tmp(f, L.Nd, L.Nd.NdCirc)
            with f.if_((w.field("opts") & u32(spec.MULTILINE)) != u32(0)):
                f.set(circ, L.Nd.NdCircM)
            f.call("attach_atom", [inout(w), circ, u32(0), u32(0)])
            f.set(i, i + u32(1))
            f.cont()

        with f.if_(c == b("$")):
            doll = tmp(f, L.Nd, L.Nd.NdDoll)
            with f.if_((w.field("opts") & u32(spec.MULTILINE)) != u32(0)):
                f.set(doll, L.Nd.NdDollM)
            with f.else_():
                with f.if_((w.field("opts") & u32(spec.DOLLAR_ENDONLY)) != u32(0)):
                    f.set(doll, L.Nd.NdDollE)
            f.call("attach_atom", [inout(w), doll, u32(0), u32(0)])
            f.set(i, i + u32(1))
            f.cont()

        with f.if_(one_of(c, "*+?{")):
            f.call("quantifier", [pat, inout(i), inout(w)])
            f.cont()

        with f.if_(c == u8(BACKSLASH)):
            with f.if_(i + u32(1) < n):
                q = tmp(f, u8, pat.at(i + u32(1)))
                with f.if_(q == b("Q")):
                    f.set(quoting, boolean(True))
                    f.set(i, i + u32(2))
                    f.cont()
                with f.if_(q == b("E")):
                    f.set(i, i + u32(2))
                    f.cont()
            f.call("read_escape", [pat, inout(i), inout(w), boolean(False)], dest=esc)
            with f.if_(w.field("err") != u32(0)):
                f.cont()
            f.call("attach_escape", [inout(w), esc])
            f.cont()

        value = tmp(f, u32, c.cast(u32))
        f.call("add_char", [inout(w), value])
        f.set(i, i + u32(1))

    with f.if_(w.field("err") != u32(0)):
        f.ret()
    with f.if_(w.field("frames").len() > u32(1)):
        f.set(w.field("err"), u32(spec.E_MISSING_PAREN))
        f.set(w.field("erroff"), n)
        f.ret()
    # A reference is legal ahead of the group it names, so existence is a
    # question for the end of the pass, asked in pattern order because pcre2
    # reports the first reference that has no group. Only when every one of
    # them holds up does the refusal fall back to ours.
    r = tmp(f, u32, u32(0))
    nrefs = tmp(f, u32, w.field("refs").len())
    known = tmp(f, boolean, boolean(False))
    with f.while_(r < nrefs, down(nrefs, r)):
        ref = tmp(f, L.Ref, w.field("refs").at(r))
        missing = tmp(f, boolean, ref.field("num") > w.field("ncap"))
        with f.if_(ref.field("num") == u32(spec.NONE)):
            f.call("name_taken", [pat, ref.field("off"), ref.field("nlen"), inout(w)], dest=known)
            f.set(missing, lnot(known))
        with f.if_(missing):
            f.set(w.field("err"), u32(spec.E_NO_SUCH_GROUP))
            f.set(w.field("erroff"), ref.field("off"))
            f.ret()
        f.set(r, r + u32(1))
    with f.if_(nrefs > u32(0)):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), w.field("refs").at(u32(0)).field("off"))
        f.ret()
    f.call("check_possess", [inout(w)])

    _parse_helpers(L)


def _parse_helpers(L: Layout) -> None:
    # What the lexer makes invisible: a (?#...) comment always, and whitespace
    # and # comments where EXTENDED is in force. A function rather than inline
    # because the gap before a quantifier's lazy marker is one of these too —
    # `a*(?#x)?` is a lazy star, exactly as `a*?` is.
    f = L.func(
        "skip_gaps",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    extended = tmp(f, boolean, (w.field("opts") & u32(spec.EXTENDED)) != u32(0))
    isspace = tmp(f, boolean, boolean(False))
    with f.while_(i < n, down(n, i)):
        c = tmp(f, u8, pat.at(i))
        with f.if_(extended):
            f.call("ct", [c, u8(spec.CT_SPACE)], dest=isspace)
            with f.if_(isspace):
                f.set(i, i + u32(1))
                f.cont()
            with f.if_(c == b("#")):
                j = tmp(f, u32, i + u32(1))
                with f.while_(j < n, down(n, j)):
                    step = tmp(f, u32, u32(0))
                    f.call("newline_at", [pat, j, w.field("nltype")], dest=step)
                    with f.if_(step != u32(0)):
                        f.set(j, j + step)
                        f.brk()
                    f.set(j, j + u32(1))
                f.set(i, j)
                f.cont()
        # An unterminated comment is left where it is, so that the main pass
        # reports it rather than this helper swallowing the rest of the pattern.
        with f.if_(
            lnot(
                land(
                    c == b("("),
                    land(i + u32(2) < n, land(pat.at(i + u32(1)) == b("?"), pat.at(i + u32(2)) == b("#"))),
                )
            )
        ):
            f.brk()
        k = tmp(f, u32, i + u32(3))
        with f.while_(land(k < n, pat.at(k) != b(")")), down(n, k)):
            f.set(k, k + u32(1))
        with f.if_(k >= n):
            f.brk()
        f.set(i, k + u32(1))
    f.set(f["at"], i)

    f = L.func("close_group", params=[("w", L.Work, "inout")])
    w = f["w"]
    gone = tmp(f, L.Frame)
    f.pop(w.field("frames"), gone)
    f.set(w.field("opts"), gone.field("opts"))
    with f.if_(gone.field("unsup") != u32(0)):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), gone.field("unsup"))
        f.ret()
    top = tmp(f, u32, w.field("frames").len() - u32(1))
    f.set(w.field("frames").at(top).field("qual"), gone.field("grp"))

    f = L.func("new_branch", params=[("w", L.Work, "inout")])
    w = f["w"]
    top = tmp(f, u32, w.field("frames").len() - u32(1))
    alt = tmp(f, u32, w.field("frames").at(top).field("alt"))
    with f.if_(alt == u32(0)):
        made = tmp(f, u32, u32(0))
        f.call("alloc_node", [inout(w), L.Nd.NdAlt, u32(0), u32(0), u32(0)], dest=made)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        grp = tmp(f, u32, w.field("frames").at(top).field("grp"))
        only = tmp(f, u32, w.field("nodes").at(grp).field("first"))
        f.set(w.field("nodes").at(made).field("first"), only)
        f.set(w.field("nodes").at(made).field("last"), only)
        f.set(w.field("nodes").at(grp).field("first"), made)
        f.set(w.field("nodes").at(grp).field("last"), made)
        f.set(w.field("frames").at(top).field("alt"), made)
        f.set(alt, made)
    branch = tmp(f, u32, u32(0))
    f.call("alloc_node", [inout(w), L.Nd.NdConcat, u32(0), u32(0), u32(0)], dest=branch)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    f.call("add_child", [inout(w), alt, branch])
    f.set(w.field("frames").at(top).field("cat"), branch)
    f.set(w.field("frames").at(top).field("qual"), u32(0))

    f = L.func("attach_escape", params=[("w", L.Work, "inout"), ("esc", L.Esc)])
    w = f["w"]
    esc = f["esc"]
    with f.switch(esc.field("kind")) as arm:
        with arm.case("EkChar"):
            value = tmp(f, u32, esc.field("val"))
            f.call("add_char", [inout(w), value])
        with arm.case("EkSet"):
            f.call("class_from_set", [inout(w), esc.field("val"), boolean(False)])
        with arm.case("EkNegSet"):
            f.call("class_from_set", [inout(w), esc.field("val"), boolean(True)])
        with arm.case("EkSod"):
            f.call("attach_atom", [inout(w), L.Nd.NdSod, u32(0), u32(0)])
        with arm.case("EkEod"):
            f.call("attach_atom", [inout(w), L.Nd.NdEod, u32(0), u32(0)])
        with arm.case("EkEodn"):
            f.call("attach_atom", [inout(w), L.Nd.NdEodn, u32(0), u32(0)])
        with arm.case("EkWordB"):
            f.call("attach_atom", [inout(w), L.Nd.NdWordB, u32(0), u32(0)])
        with arm.case("EkNotWordB"):
            f.call("attach_atom", [inout(w), L.Nd.NdNotWordB, u32(0), u32(0)])
        with arm.case("EkBsr"):
            f.call("attach_atom", [inout(w), L.Nd.NdBsr, u32(0), u32(0)])
        with arm.case("EkNop"):
            f.call("attach_atom", [inout(w), L.Nd.NdNil, u32(0), u32(0)])
        with arm.otherwise():
            pass

    f = L.func(
        "class_from_set",
        params=[("w", L.Work, "inout"), ("which", u32), ("neg", boolean)],
    )
    w = f["w"]
    idx = tmp(f, u32, u32(0))
    f.call("new_class", [inout(w)], dest=idx)
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    base = tmp(f, u32, idx * u32(32))
    which = tmp(f, u32, f["which"])
    neg = tmp(f, boolean, f["neg"])
    f.call("set_union", [inout(w), base, which, neg])
    identity = tmp(f, u32, u32(spec.AP_NONE))
    for (name, negated), value in spec.AP_OF_SET.items():
        with f.if_(land(which == u32(spec.SET_INDEX[name]), neg == boolean(negated))):
            f.set(identity, u32(value))
    f.call("attach_atom", [inout(w), L.Nd.NdClass, idx, identity])

    f = L.func(
        "quantifier",
        params=[
            ("pat", L.frozen_bytes),
            ("at", u32, "inout"),
            ("w", L.Work, "inout"),
        ],
    )
    w = f["w"]
    pat = f["pat"]
    n = tmp(f, u32, pat.len())
    i = tmp(f, u32, f["at"])
    c = tmp(f, u8, pat.at(i))
    lo = tmp(f, u32, u32(0))
    hi = tmp(f, u32, u32(spec.NONE))
    with f.if_(c == b("+")):
        f.set(lo, u32(1))
    with f.if_(c == b("?")):
        f.set(hi, u32(1))
    with f.if_(c == b("{")):
        quant = tmp(f, L.Quant)
        f.call("read_braces", [pat, i, inout(w)], dest=quant)
        with f.if_(w.field("err") != u32(0)):
            f.ret()
        with f.if_(lnot(quant.field("ok"))):
            value = tmp(f, u32, c.cast(u32))
            f.call("add_char", [inout(w), value])
            f.set(f["at"], i + u32(1))
            f.ret()
        f.set(lo, quant.field("lo"))
        f.set(hi, quant.field("hi"))
        f.set(i, quant.field("end") - u32(1))
    f.set(i, i + u32(1))
    # pcre2 reports "nothing to repeat" at the end of the quantifier itself,
    # before the ? or + that only says how it repeats.
    at = tmp(f, u32, i)
    f.call("skip_gaps", [pat, inout(i), inout(w)])

    greedy = tmp(f, boolean, boolean(True))
    possessive = tmp(f, boolean, boolean(False))
    with f.if_(i < n):
        after = tmp(f, u8, pat.at(i))
        with f.if_(after == b("?")):
            f.set(greedy, boolean(False))
            f.set(i, i + u32(1))
        with f.if_(after == b("+")):
            f.set(possessive, boolean(True))
            f.set(i, i + u32(1))
    with f.if_((w.field("opts") & u32(spec.UNGREEDY)) != u32(0)):
        f.set(greedy, lnot(greedy))
    # Whether there is anything here to repeat is settled before the possessive
    # marker is, because that is the order pcre2 settles them in: `*+` at the
    # start of a pattern is "nothing to repeat", not "possessive".
    f.call("apply_quant", [inout(w), lo, hi, greedy, at])
    with f.if_(w.field("err") != u32(0)):
        f.ret()
    with f.if_(possessive):
        f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
        f.set(w.field("erroff"), i)
        f.ret()
    f.set(f["at"], i)


def _autopossess(L: Layout) -> None:
    """Refuse what pcre2's auto-possessification would answer differently.

    `spec.py` says why the eight pairs exist. pcre2 possessifies a repetition
    against the item that follows it in the compiled code, and the arena is
    allocated in parse order, so everything that can follow a repetition sits
    at a higher index than its node — the check walks the arena backwards with
    a running mask of the identities seen so far, and asks each open-ended
    repetition whether an unsafe partner sits anywhere after it. That is an
    over-approximation of "immediately after", which errs the right way:
    refusing a pattern too often is a smaller sin than answering one wrongly,
    and the wave 2 machinery is what makes the exact question worth asking.

    One thing breaks the index order: pcre2 compiles a counted repetition of a
    group by replicating the group's code, so inside such a group "after" can
    also mean the front of the group, or of any group, on the next copy. The
    pinned build really does mis-possessify `(?:\\s\\R*){2}`. Whenever some
    group is repeated the check therefore falls back to comparing against the
    identities of the whole pattern, which is exact enough until wave 2.
    """
    f = L.func("identity_of", params=[("kind", L.Nd), ("aux", u32)], ret=u32)
    with f.switch(f["kind"]) as arm:
        with arm.case("NdClass"):
            f.ret(f["aux"])
        with arm.case("NdAnyNoNL"):
            f.ret(u32(spec.AP_DOT))
        with arm.case("NdAny"):
            f.ret(u32(spec.AP_DOTALL))
        with arm.case("NdBsr"):
            f.ret(u32(spec.AP_ANYNL))
        with arm.otherwise():
            f.ret(u32(spec.AP_NONE))

    f = L.func("check_possess", params=[("w", L.Work, "inout")])
    w = f["w"]
    total = tmp(f, u32, w.field("nodes").len())
    used = tmp(f, u32, u32(0))
    identity = tmp(f, u32, u32(0))
    grouprep = tmp(f, boolean, boolean(False))
    i = tmp(f, u32, u32(1))
    with f.while_(i < total, down(total, i)):
        node = tmp(f, L.Node, w.field("nodes").at(i))
        f.call("identity_of", [node.field("kind"), node.field("aux")], dest=identity)
        for value in range(spec.AP_NOT_DIGIT, spec.AP_VSPACE + 1):
            with f.if_(identity == u32(value)):
                f.set(used, used | u32(1 << value))
        with f.if_(node.field("kind") == L.Nd.NdRepeat):
            with f.if_(
                w.field("nodes").at(node.field("first")).field("kind") == L.Nd.NdGroup
            ):
                f.set(grouprep, boolean(True))
        f.set(i, i + u32(1))
    after = tmp(f, u32, u32(0))
    f.set(i, total - u32(1))
    with f.while_(i > u32(0), i.cast(counter)):
        node = tmp(f, L.Node, w.field("nodes").at(i))
        # Only a repetition with something to give back is in question, so an
        # exact count never is. Laziness is no protection: where the two items
        # really are disjoint, a lazy repetition consumes the same run a
        # possessive one would, and pcre2 rewrites it that way too.
        with f.if_(
            land(
                node.field("kind") == L.Nd.NdRepeat,
                node.field("aux") > node.field("val"),
            )
        ):
            body = tmp(f, L.Node, w.field("nodes").at(node.field("first")))
            f.call("identity_of", [body.field("kind"), body.field("aux")], dest=identity)
            partners = tmp(f, u32, u32(0))
            for left, mask in sorted(
                (left, spec.ap_partners(left)) for left in spec.AP_UNSOUND
            ):
                with f.if_(identity == u32(left)):
                    f.set(partners, u32(mask))
            ahead = tmp(f, u32, after)
            with f.if_(grouprep):
                f.set(ahead, used)
            with f.if_((partners & ahead) != u32(0)):
                f.set(w.field("err"), u32(spec.E_UNSUPPORTED_FEATURE))
                f.set(w.field("erroff"), u32(0))
                f.ret()
        f.call("identity_of", [node.field("kind"), node.field("aux")], dest=identity)
        for value in range(spec.AP_NOT_DIGIT, spec.AP_VSPACE + 1):
            with f.if_(identity == u32(value)):
                f.set(after, after | u32(1 << value))
        f.set(i, i - u32(1))
