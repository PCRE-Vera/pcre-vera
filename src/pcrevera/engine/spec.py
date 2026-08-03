"""The numbers and tables the engine is built from.

Plain Python data, shared by the TIR program that this package emits and by the
driver that runs it. Nothing here executes at match time: the tables become
frozen IR constants and the limits become the declared maxima of IR arrays, so
a backend sees the same values without ever consulting this file.

The byte sets are the ones the pinned pcre2 build reports for the default C
locale tables (DESIGN.md section 2.3), read out of it byte by byte rather than
copied from documentation.
"""

from __future__ import annotations

from ..tir.types import CEILING

# --- documented portable limits (DESIGN.md section 2.4) ---
#
# All of them sit far below the IR array ceiling, and all are pre-checked, so an
# oversized pattern comes back as PatternTooLarge in every language rather than
# hitting an allocation wall somewhere.

MAX_PATTERN = 4096
"""Pattern length in bytes."""

MAX_DEPTH = 250
"""Group nesting depth, the same default as pcre2's parse depth."""

MAX_NODES = 2 * MAX_PATTERN + 16
"""AST nodes, index 0 reserved as the nil node.

Sized from the pattern length rather than picked: no pattern byte produces more
than two nodes, so this and the three limits below are safety nets that a valid
pattern reaches only after the length limit has already refused it. Pattern
length and nesting depth are the two limits a caller can actually hit, plus the
group count, which the ovector fixes.
"""

MAX_CODE = 4 * MAX_NODES + 16
"""Bytecode instructions: no node emits more than four."""

MAX_CLASSES = MAX_PATTERN
"""Character class bitmaps, 32 bytes each."""

MAX_GROUPS = 255
"""Capturing groups."""

MAX_NAMES = 255
"""Named groups."""

MAX_NAME_BYTES = 4096
"""Total bytes of group names."""

MAX_NAME = 128
"""Bytes in one group name, as in pcre2."""

MAX_REPS = MAX_PATTERN
"""Counted repetitions, each with a counter and a position register."""

MAX_REFS = MAX_PATTERN // 2
"""Group references seen during the parse, kept so that a reference to a group
that never appears can be reported the way pcre2 reports it. Two pattern bytes
is the least a reference can cost, so this is another safety net behind the
length limit."""

MAX_JOBS = 2048
"""Depth of the code generator's explicit work stack."""

MAX_PATCHES = 4096
"""Pending jump patches during code generation."""

MAX_QUANT = 65535
"""The largest bound a {m,n} quantifier may name, as in pcre2."""

MAX_OVEC = 2 * (MAX_GROUPS + 1)
MAX_REGS = MAX_OVEC + 2 * MAX_REPS

BT_SIZE = 12
"""IR bytes of one backtrack entry: three u32."""

UNDO_SIZE = 8
"""IR bytes of one undo entry: two u32."""

REG_SIZE = 4
"""IR bytes of one register, which is what zeroing or restoring one is charged.

The matcher charges it, the checker prices it and the corpus predicts it, so it
is here rather than spelled out three times: DESIGN.md section 5 wants one cost
model shared by the analyzer, both matchers and the Lean accounting, and a
number the three copies could drift apart on is the easiest way to lose that."""

GROW_MIN = 4
"""Elements the first growth of a vector reserves."""

GROW_FACTOR = 2
"""What every growth after the first multiplies the capacity by.

TIR-SPEC.md section 11.3 fixes the schedule so that the peak is the same in
every target; these two say what it is, for the matcher that follows it and the
checker that has to bound it."""

MAX_STACK = CEILING // BT_SIZE
"""Declared maximum of the backtrack stack: the whole allocation ceiling divided
by what one entry weighs. The caller's stack and memory limits are the real
bounds; a fixed number here would be a hidden third limit that could refuse a
run the caller's budgets still allow."""

MAX_TRAIL = CEILING // UNDO_SIZE
"""Declared maximum of the undo trail, derived the same way and for the same
reason: only the caller's memory limit decides when the trail is too long."""

# --- resource analysis (DESIGN.md section 5) ---

MAX_REGIONS = MAX_NODES
"""Regions in one compiled pattern.

A region is a source construct the compiler flattened — a group, an alternation
branch, a quantifier body — so the AST arena already bounds how many there can
be."""

MAX_DEGREE = 4
"""The highest power of (n + 1) a bound polynomial carries.

A bound is `base^n` times a polynomial in the subject length, and this is how
many coefficients that polynomial has room for, so it is a field count rather
than a limit anything is compared against. A composition that would need a
higher power has no certificate at all, which is a refusal the checker names.

Four is what the shapes of BOUNDS.md reach: each nested quantifier whose body
can match empty contributes one power, and the per-attempt loop contributes the
last."""

DEGREES = tuple(range(MAX_DEGREE + 1))
"""Those powers, as the suffixes the coefficient fields are named with."""

UNSET = 0xFFFFFFFF
"""What a register holds before anything writes it, reported as -1."""

NONE = 0xFFFFFFFF
"""No such index."""

# --- compile options ---

CASELESS = 1 << 0
MULTILINE = 1 << 1
DOTALL = 1 << 2
EXTENDED = 1 << 3
UNGREEDY = 1 << 4
ANCHORED = 1 << 5
ENDANCHORED = 1 << 6
DOLLAR_ENDONLY = 1 << 7

COMPILE_OPTIONS = {
    "CASELESS": CASELESS,
    "MULTILINE": MULTILINE,
    "DOTALL": DOTALL,
    "EXTENDED": EXTENDED,
    "UNGREEDY": UNGREEDY,
    "ANCHORED": ANCHORED,
    "ENDANCHORED": ENDANCHORED,
    "DOLLAR_ENDONLY": DOLLAR_ENDONLY,
}

# The four options a (?...) group may set or clear, in the letters pcre2 uses.
INLINE_OPTIONS = {
    ord("i"): CASELESS,
    ord("m"): MULTILINE,
    ord("s"): DOTALL,
    ord("x"): EXTENDED,
    ord("U"): UNGREEDY,
}

# --- match options ---

NOTBOL = 1 << 0
NOTEOL = 1 << 1
NOTEMPTY = 1 << 2
NOTEMPTY_ATSTART = 1 << 3
MATCH_ANCHORED = 1 << 4

MATCH_OPTIONS = {
    "NOTBOL": NOTBOL,
    "NOTEOL": NOTEOL,
    "NOTEMPTY": NOTEMPTY,
    "NOTEMPTY_ATSTART": NOTEMPTY_ATSTART,
    "ANCHORED": MATCH_ANCHORED,
}

# --- newline and \R conventions ---

NL_LF = 0
NL_CR = 1
NL_CRLF = 2
NL_ANYCRLF = 3
NL_ANY = 4

NEWLINE_CONVENTIONS = {
    "LF": NL_LF,
    "CR": NL_CR,
    "CRLF": NL_CRLF,
    "ANYCRLF": NL_ANYCRLF,
    "ANY": NL_ANY,
}

BSR_UNICODE = 0
BSR_ANYCRLF = 1

BSR_CONVENTIONS = {"UNICODE": BSR_UNICODE, "ANYCRLF": BSR_ANYCRLF}

# --- outcomes ---

OK = 0
MATCHED = 0
NO_MATCH = 1
RESOURCE_EXCEEDED = 2
BAD_INPUT = 3

# --- compile errors ---
#
# Codes below 1000 are pcre2's own, for the syntax errors we reproduce exactly;
# DESIGN.md section 2.4 forbids repurposing one, so everything that is ours
# lives above the line.

E_BACKSLASH_AT_END = 101
E_C_AT_END = 102
E_UNRECOGNIZED_ESCAPE = 103
E_QUANTIFIER_ORDER = 104
E_QUANTIFIER_TOO_BIG = 105
E_MISSING_BRACKET = 106
E_BAD_CLASS_ESCAPE = 107
E_CLASS_RANGE_ORDER = 108
E_NOTHING_TO_REPEAT = 109
E_UNRECOGNIZED_AFTER_QUERY = 111
E_POSIX_OUTSIDE_CLASS = 112
E_POSIX_COLLATING = 113
E_MISSING_PAREN = 114
E_NO_SUCH_GROUP = 115
E_MISSING_COMMENT_PAREN = 118
E_TOO_DEEP = 119
E_UNMATCHED_PAREN = 122
E_ZERO_RELATIVE = 126
E_UNKNOWN_POSIX_CLASS = 130
E_CODE_POINT_TOO_BIG = 134
E_NO_SUCH_BACKSLASH = 137
E_BAD_NAME_TERMINATOR = 142
E_DUPLICATE_NAME = 143
E_NAME_STARTS_WITH_DIGIT = 144
E_MALFORMED_UCP = 146
E_UNKNOWN_PROPERTY = 147
E_NAME_TOO_LONG = 148
E_INVALID_CLASS_RANGE = 150
E_OCTAL_TOO_BIG = 151
E_MISSING_OCTAL_BRACE = 155
E_BAD_G_ESCAPE = 157
E_NUMBER_TOO_BIG = 161
E_NAME_EXPECTED = 162
E_BAD_OCTAL_DIGIT = 164
E_BAD_HEX_DIGIT = 167
E_C_NOT_PRINTABLE = 168
E_BAD_K_ESCAPE = 169
E_N_IN_CLASS = 171
E_MISSING_DIGITS = 178
E_BAD_HYPHEN = 194
E_NUMBER_TERMINATOR = 219

E_UNSUPPORTED_FEATURE = 1000
E_UNSUPPORTED_OPTION = 1001
E_PATTERN_TOO_LARGE = 1002
E_INTERNAL = 1003

OUR_ERRORS = {
    E_UNSUPPORTED_FEATURE: "UnsupportedFeature",
    E_UNSUPPORTED_OPTION: "UnsupportedOption",
    E_PATTERN_TOO_LARGE: "PatternTooLarge",
    E_INTERNAL: "InternalError",
}

# --- built-in character sets ---
#
# Read out of the pinned pcre2 build with tmp/classes.py; a change here is a
# compatibility change and shows up as a differential failure first.

_ASCII_LOWER = set(range(0x61, 0x7B))
_ASCII_UPPER = set(range(0x41, 0x5B))
_DIGIT = set(range(0x30, 0x3A))
_ALPHA = _ASCII_LOWER | _ASCII_UPPER

SETS: dict[str, frozenset[int]] = {
    "digit": frozenset(_DIGIT),
    "word": frozenset(_ALPHA | _DIGIT | {0x5F}),
    "space": frozenset(set(range(0x09, 0x0E)) | {0x20}),
    "hspace": frozenset({0x09, 0x20, 0xA0}),
    "vspace": frozenset(set(range(0x0A, 0x0E)) | {0x85}),
    "alpha": frozenset(_ALPHA),
    "alnum": frozenset(_ALPHA | _DIGIT),
    "ascii": frozenset(range(0x00, 0x80)),
    "blank": frozenset({0x09, 0x20}),
    "cntrl": frozenset(set(range(0x00, 0x20)) | {0x7F}),
    "graph": frozenset(range(0x21, 0x7F)),
    "lower": frozenset(_ASCII_LOWER),
    "print": frozenset(range(0x20, 0x7F)),
    "punct": frozenset(set(range(0x21, 0x7F)) - _ALPHA - _DIGIT),
    "upper": frozenset(_ASCII_UPPER),
    "xdigit": frozenset(_DIGIT | set(range(0x41, 0x47)) | set(range(0x61, 0x67))),
}

SET_ORDER = (
    "digit",
    "word",
    "space",
    "hspace",
    "vspace",
    "alpha",
    "alnum",
    "ascii",
    "blank",
    "cntrl",
    "graph",
    "lower",
    "print",
    "punct",
    "upper",
    "xdigit",
)

SET_INDEX = {name: index for index, name in enumerate(SET_ORDER)}

# The POSIX names a [:...:] may spell, and the set each one selects. `word` and
# `ascii` are pcre2 extensions to POSIX; pcre2 accepts them, so we do too.
POSIX_NAMES = (
    "alnum",
    "alpha",
    "ascii",
    "blank",
    "cntrl",
    "digit",
    "graph",
    "lower",
    "print",
    "punct",
    "space",
    "upper",
    "word",
    "xdigit",
)


def bitmap(members: frozenset[int] | set[int]) -> bytes:
    """A 256-bit set, low bit first, as the engine reads it."""
    table = bytearray(32)
    for byte in members:
        table[byte >> 3] |= 1 << (byte & 7)
    return bytes(table)


def set_table() -> bytes:
    """Every built-in set, 32 bytes each, indexed by SET_INDEX."""
    return b"".join(bitmap(SETS[name]) for name in SET_ORDER)


def posix_table() -> bytes:
    """Packed POSIX names: a length, the name, then the set index."""
    out = bytearray()
    for name in POSIX_NAMES:
        out.append(len(name))
        out += name.encode("ascii")
        out.append(SET_INDEX[name])
    return bytes(out)


def bit_table() -> bytes:
    """1 << i for i in 0 .. 7, since TIR shifts by constants only."""
    return bytes(1 << i for i in range(8))


def lower_table() -> bytes:
    """ASCII case folding, which is all pcre2 does without PCRE2_UTF."""
    return bytes(byte + 0x20 if byte in _ASCII_UPPER else byte for byte in range(256))


def flip_table() -> bytes:
    """The other case of a byte, or the byte itself when it has none."""
    return bytes(byte ^ 0x20 if byte in _ALPHA else byte for byte in range(256))


# Character properties the parser asks about, one byte per code.
CT_WORD = 1
CT_SPACE = 2
CT_DIGIT = 4
CT_HEX = 8
CT_OCTAL = 16
CT_ALPHA = 32


def ctype_table() -> bytes:
    out = bytearray(256)
    for byte in range(256):
        bits = 0
        if byte in SETS["word"]:
            bits |= CT_WORD
        if byte in SETS["space"]:
            bits |= CT_SPACE
        if byte in _DIGIT:
            bits |= CT_DIGIT
        if byte in SETS["xdigit"]:
            bits |= CT_HEX
        if 0x30 <= byte <= 0x37:
            bits |= CT_OCTAL
        if byte in _ALPHA:
            bits |= CT_ALPHA
        out[byte] = bits
    return bytes(out)


# --- pcre2's auto-possessification, and where it disagrees with itself ---
#
# pcre2 turns a quantifier possessive when it can prove the repeated item and
# the one after it never match the same character — a lazy one too, since a
# lazy repetition over a disjoint pair consumes exactly the run a possessive
# one would. The proof is a
# static table over opcodes (pcre2_auto_possess.c), and for eight pairs that
# table is wrong in 8-bit mode: it treats `.` as excluding every vertical-space
# character rather than the newline convention's, and it forgets that NEL
# (0x85) is not a space and that NBSP (0xa0) is horizontal space. Where the
# proof is right, possessifying changes no answer; where it is wrong, pcre2
# gives a different answer from its own semantics.
#
# The machinery that would let us reproduce it — possessive repetition, which
# is atomic-group behaviour — is wave 2 (DESIGN.md section 2.1), so wave 1
# refuses the patterns that would need it rather than answering them wrongly.

AP_NONE = 0
"""No opcode identity: an ordinary class or literal, which pcre2 compares exactly."""

AP_NOT_DIGIT = 1
AP_DIGIT = 2
AP_NOT_SPACE = 3
AP_SPACE = 4
AP_NOT_WORD = 5
AP_WORD = 6
AP_DOT = 7
AP_DOTALL = 8
AP_ANYNL = 9
AP_NOT_HSPACE = 10
AP_HSPACE = 11
AP_NOT_VSPACE = 12
AP_VSPACE = 13

# Which built-in set escape becomes which identity, negated or not.
AP_OF_SET = {
    ("digit", False): AP_DIGIT,
    ("digit", True): AP_NOT_DIGIT,
    ("space", False): AP_SPACE,
    ("space", True): AP_NOT_SPACE,
    ("word", False): AP_WORD,
    ("word", True): AP_NOT_WORD,
    ("hspace", False): AP_HSPACE,
    ("hspace", True): AP_NOT_HSPACE,
    ("vspace", False): AP_VSPACE,
    ("vspace", True): AP_NOT_VSPACE,
}

# The pairs pcre2's table calls disjoint and the byte semantics do not, as
# (repeated item, following item).
AP_UNSOUND = {
    AP_NOT_SPACE: (AP_ANYNL, AP_HSPACE, AP_VSPACE),
    AP_DOT: (AP_ANYNL,),
    AP_ANYNL: (AP_SPACE, AP_DOT),
    AP_HSPACE: (AP_NOT_SPACE,),
    AP_VSPACE: (AP_NOT_SPACE,),
}


def ap_partners(identity: int) -> int:
    """A bitmask of the identities that make `identity` unsafe to quantify."""
    mask = 0
    for other in AP_UNSOUND.get(identity, ()):
        mask |= 1 << other
    return mask
