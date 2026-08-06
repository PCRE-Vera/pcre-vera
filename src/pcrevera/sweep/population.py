"""Where a sweep case comes from.

One generator, used by the committed shard and by the week-long campaign alike.
The scale is an argument, never a second set of shapes: DESIGN.md section 8
asks for a grammar weighted toward the constructs that break matchers — nested
quantifiers, groups that can match nothing, boundary anchors — and for a
hostile-syntax population beside it, and a smoke test that generated something
else would be reporting on a population nobody is fuzzing.

Every case is a function of the numbers a manifest is generated from — the
seed, how many subjects a case carries, where the structured population ends,
and the case's own index — and of nothing else. That is what lets a failure be
replayed from a line of arguments, a campaign be split across processes without
a shared generator, and the reducer rebuild the case it is shrinking. The short
way to say it is that a case is named by its manifest's hash and its index; the
long way is the four numbers, and a failure record carries all four.

The generator those numbers name is this package's own `Draw`, not `random`,
for the same reason: a manifest hash written into a freeze record must not
depend on which interpreter produced the population.

Three things are laid out rather than sampled. The compile options cycle by
index and the newline/BSR conventions cycle once per pass through them, so the
first sixty-six cases of any sweep — eleven option families by six convention
pairs — already cross every one with every other, each exactly once; the
atom-by-quantifier product opens the population, so no opcode waits on a lucky
draw; and the quantifier matrix follows it, so neither does any shape of the
lowering. Everything past that is the grammar, and the
subjects are built from the bytes the pattern itself mentions, which is what
makes them structure-aware rather than random noise the pattern never looks at.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

from .draw import Draw

ATOMS = (
    "a", "b", ".", "[a-c]", "[^a-c]", r"\d", r"\D", r"\w", r"\W", r"\s", r"\S",
    r"\h", r"\v", r"\R", "[[:alpha:]]", "[[:^digit:]]", r"[\d_]", "[]a]", "[a-]",
    "^", "$", r"\A", r"\z", r"\Z", r"\b", r"\B", r"\Qa.c\E", r"\x41", r"\101",
    r"\cA", "(a)", "(?:ab)", "(?<n>a)", "(a|b)", "(a|)", "(|a)", "(?i)a",
    "(?i:ab)", "(?#x)a",
)
"""One construct each, so that the opening block of any sweep names them all."""

QUANTIFIERS = (
    "", "*", "+", "?", "??", "*?", "+?", "{2}", "{1,3}", "{0,2}", "{2,}", "{2,3}?",
)

QUANT_BODIES = (
    "a", "[ab]", "(a)", "(?:ab)", "(a|b)", "(a|aa)", "(a|)", "(|a)",
    "(?:a?)", "(?:(a)?)", "(?:a*)", "(a*)", "(?:(a)|(b))", "(?<g1>a?)",
)
"""The bodies the quantifier matrix repeats.

A defined grammar rather than a sample: a literal and a class, a capture and a
non-capturing group, alternations of equal and unequal width, alternations with
an empty arm on either side, an optional and a star with and without a capture,
and a body whose two captures are mutually exclusive. Between them they cover
what a copied body can do that a single one cannot — overwrite a group, leave
one unset, and finish an iteration without consuming.

The ones that end in a quantifier of their own are written grouped, because a
quantifier may not follow a quantifier: `a?{1,3}` is pcre2's "nothing to
repeat" and a cell built from it would compare two refusals rather than two
matches."""


def _counts() -> tuple[str, ...]:
    """Every quantifier spelling the lowering has a rule for, greedy and lazy.

    `{m}`, `{m,}` and `{m,n}` for m and n from zero to three, which is enough
    to reach both sides of every boundary in the rewrite: no mandatory copy and
    several, no optional tail and several, an exact count, and the two forms
    that are already canonical. The cap-adjacent counts are `QUANT_OVER_CAP`,
    beside this rather than in it, because they belong to the caps and not to
    the rewrite's own boundaries."""
    out = []
    for low in range(4):
        out.append("{%d}" % low)
        out.append("{%d,}" % low)
        for high in range(low, 4):
            out.append("{%d,%d}" % (low, high))
    return tuple(count + lazy for count in out for lazy in ("", "?"))


QUANT_COUNTS = _counts()

QUANT_OVER_CAP = ("(?:a*){4097}b", "a{32829}b")
"""The far side of two of the compiler's caps: the repetition table, one
counter per copy, and the code generator's walk fuel, which for a body of one
instruction runs out before the code array does — two visits per copy against
one cell, and the fuel is twice the code array.

Only the far side. A candidate that *fits* a cap is a program of tens of
thousands of instructions, and laying one out costs more steps than the
reference interpreter's budget allows — a Python limit rather than an engine
one, but the shard is generated in Python, so a cell that could not be
generated is not a cell. The fitting side is asserted instead in
`tests/test_lowering.py`, off the dry run's own report, and what is here is
what the fallback has to do: compile in counter form, answer what pcre2
answers, and not become PatternTooLarge.

Both counts are exactly one past their cap, and `tests/test_lowering.py` holds
them there: a cap that moved would leave these merely large rather than
adjacent, which is the difference between a boundary witness and a big number.

Both reach their cap through a one-instruction body, which is not decoration.
pcre2 replicates a bounded quantifier and refuses at its own compiled size, so
a body of two instructions runs out of *its* room first — `(?:ab){9000}` is
"regular expression is too large" there and an ordinary counter here — and a
cell the arbiter declines is a cell with nothing to compare against."""

QUANT = tuple(
    "%s%sb" % (body, count)
    for body, count in itertools.product(QUANT_BODIES, QUANT_COUNTS)
) + QUANT_OVER_CAP
"""The matrix itself, each cell followed by a literal so that a subject which
runs out forces backtracking into the copies rather than stopping at the last
one.

What is crossed with what, exactly. Every cell is asked under all six match
option families, including NOTEMPTY, NOTEMPTY_ATSTART and match-time
anchoring, because those cycle per trial and a case carries more trials than
there are families; every cell is asked at a start of zero, one, the middle
and the end, because the matrix lays its offsets out rather than drawing them.
The compile options and the newline and BSR conventions cycle per *case*, so
the matrix covers all eleven families and all six convention pairs across its
cells rather than within each one — crossing those per cell as well would be
eleven populations of it, and the grammar population beside it is where that
breadth already comes from."""

OPTION_SETS = (
    (),
    ("CASELESS",),
    ("MULTILINE",),
    ("DOTALL",),
    ("EXTENDED",),
    ("UNGREEDY",),
    ("ANCHORED",),
    ("ENDANCHORED",),
    ("DOLLAR_ENDONLY",),
    ("MULTILINE", "DOTALL"),
    ("CASELESS", "UNGREEDY"),
)

MATCH_OPTION_SETS = (
    (), ("NOTBOL",), ("NOTEOL",), ("NOTEMPTY",), ("NOTEMPTY_ATSTART",), ("ANCHORED",),
)

CONVENTIONS = (
    ("LF", "UNICODE"),
    ("CR", "UNICODE"),
    ("CRLF", "UNICODE"),
    ("ANYCRLF", "ANYCRLF"),
    ("ANY", "UNICODE"),
    ("LF", "ANYCRLF"),
)
"""Newline convention and BSR convention together, since \\R is read against
both and a sweep that varied one at a time would never ask about the pair."""

GROUPS = ("(", "(?:", "(?i:", "(?s:", "(?m:", "(?x:", "(?<g%d>")
"""What the grammar may wrap a subsequence in. The named form takes a number,
which is how a pattern comes to have two groups with the same name."""

SOUP = (
    "ab()[]{}|*+?.-^$\\,:<>=!#0123456789ixsmUQEnrtdwWSDhvRZzABbcpPkgNXCKG'\"& \t\n"
)
"""The alphabet the hostile population draws from: every metacharacter, every
letter that means something after a backslash, and the whitespace that only
matters under EXTENDED."""

FIXED_SUBJECTS = (
    "", "\n", "\r\n", "a\r\nb", "\r", "\x00", "\x0b", "\x85", "\xa0", "\xff",
)
"""The subjects every case gets whatever its pattern mentions: the empty
subject, every newline shape, and the bytes that sit on a class boundary."""

PAD = ("%s", " %s ", "x%sy", "%s%s", "%s\n%s", "\n%s", "%s\n")
"""How an interesting byte is placed in a subject. A match that only ever
starts at offset zero would never exercise the start-position loop."""


@dataclass(frozen=True)
class Trial:
    """One call to make on a case's compiled pattern."""

    subject: bytes
    match_options: tuple[str, ...]
    start: int


@dataclass(frozen=True)
class Case:
    """One pattern and everything a runner needs to ask about it.

    `index` is its place in the population and `seed` the population it came
    from; those two, with the subject count and where the structured population
    ends, are enough to build this object again, which is what a failure record
    leans on. `maxlen` is the length a preallocated context is created for, and
    it is the longest subject the case carries, so that every trial is one the
    context may be asked about.
    """

    seed: int
    index: int
    family: str
    pattern: bytes
    options: tuple[str, ...]
    newline: str
    bsr: str
    trials: tuple[Trial, ...]
    maxlen: int


def _rng(seed: int, index: int) -> Draw:
    """The one generator a case is allowed to draw from.

    Named with the two numbers rather than seeded with one of them, so that
    neighbouring indices are not neighbouring states, and drawn from this
    repository's own `Draw` rather than from `random`, so that the population —
    and therefore the manifest hash a freeze record carries — does not depend
    on which interpreter ran the generator.
    """
    return Draw(f"pcrevera-sweep:{seed}:{index}")


def _piece(rng: Draw, depth: int) -> str:
    if depth > 0 and rng.chance(45, 100):
        opener = rng.pick(GROUPS)
        if "%d" in opener:
            opener = opener % rng.between(1, 9)
        return opener + _sequence(rng, depth - 1) + ")"
    return rng.pick(ATOMS)


def _sequence(rng: Draw, depth: int) -> str:
    branches = []
    for _ in range(rng.between(1, 2)):
        parts = [
            _piece(rng, depth) + rng.pick(QUANTIFIERS)
            for _ in range(rng.between(1, 3))
        ]
        branches.append("".join(parts))
    return "|".join(branches)


def _mutated(rng: Draw, text: str) -> str:
    """A grammatical pattern with a few bytes moved, which is where the parser's
    error offsets live: most mutations still parse, and the ones that do not
    have to fail at the byte pcre2 fails at."""
    body = list(text)
    for _ in range(rng.between(1, 3)):
        if not body or rng.chance(35, 100):
            body.insert(rng.below(len(body) + 1), rng.pick(SOUP))
        elif rng.chance(1, 2):
            del body[rng.below(len(body))]
        else:
            body[rng.below(len(body))] = rng.pick(SOUP)
    return "".join(body)


CROSS = tuple(
    atom + quant for atom, quant in itertools.product(ATOMS, QUANTIFIERS)
)
"""The atom-by-quantifier product, which opens the structured population."""

LAID_OUT = len(CROSS) + len(QUANT)
"""What every structured population opens with, whatever its size: the
atom-by-quantifier product and the quantifier matrix. Both are laid out rather
than sampled, so no structured population can be smaller than the two of
them."""

STRUCTURED = 2000
HOSTILE = 400
SUBJECTS = 32
"""The shape of a full campaign, stated where a case is built rather than at
every place that builds one. `structured` decides which family an index falls
in and `subjects` how many trials it carries, so two callers defaulting them
differently would rebuild different cases from the same index — which is the
one thing a replay command exists to prevent."""


def _pattern(rng: Draw, index: int, family: str) -> str:
    if family == "cross":
        return CROSS[index]
    if family == "quant":
        return QUANT[index - len(CROSS)]
    if family == "grammar":
        return _sequence(rng, rng.between(0, 3))
    if family == "mutation":
        return _mutated(rng, _sequence(rng, rng.between(0, 2)))
    return "".join(rng.pick(SOUP) for _ in range(rng.between(1, 10)))


def _family(index: int, structured: int) -> str:
    """Which population an index belongs to.

    The product first so the opcodes are covered from the start, then the
    quantifier matrix so the lowering is too, then the grammar, then the
    hostile syntax: mutations of grammatical patterns, and the soup that is
    mostly not a pattern at all.
    """
    if index < len(CROSS):
        return "cross"
    if index < LAID_OUT:
        return "quant"
    if index < structured:
        return "grammar"
    return "mutation" if (index - structured) % 2 == 0 else "soup"


def _alphabet(pattern: str) -> list[str]:
    """The bytes the pattern mentions literally, in the order it mentions them.

    What is wanted is the characters a subject would have to contain for the
    pattern to have anything to say about it, and the cheap reading is the
    right one here: a byte that follows a backslash is part of an escape and
    means a class rather than itself, and a metacharacter means structure. The
    two letters at the end are the ones the grammar's own atoms are written
    with, so a pattern made entirely of escapes still gets subjects it can
    match.
    """
    out: list[str] = []
    skip = False
    for char in pattern:
        if skip:
            skip = False
            continue
        if char == "\\":
            skip = True
            continue
        if char.isalnum() or char in "_ \t\n\r-":
            out.append(char)
    out.extend(("a", "b", "1", " "))
    return list(dict.fromkeys(out))


def _subjects(rng: Draw, pattern: str, count: int) -> tuple[bytes, ...]:
    """`count` subjects for this pattern: some fixed, the rest structure-aware.

    A quarter of them, and never fewer than two, come from `FIXED_SUBJECTS`, so
    every case is asked about the empty subject and the newline shapes however
    the sampling falls. The rest are the pattern's own alphabet placed in the
    shapes of `PAD` and repeated at the counts a quantifier cares about,
    shuffled and cut to length — shuffled rather than truncated in place,
    because the head of that list is always the first letter of the pattern and
    a cut would give every case the same subjects.

    The share matters more than it looks. A case asked for eight subjects and
    given the ten fixed ones would be a case whose subjects have nothing to do
    with its pattern, which is exactly what "structure-aware" is here to avoid;
    the fixed subjects that do not fit are only pulled back in when a thin
    alphabet leaves room for them.
    """
    letters = _alphabet(pattern)
    built: list[str] = []
    for letter in letters:
        for shape in PAD:
            built.append(shape % ((letter,) * shape.count("%s")))
        for repeat in (2, 3, 5, 17):
            built.append(letter * repeat)
        built.append(letter.upper() + letter.lower())
    for first, second in itertools.combinations(letters[:4], 2):
        built.append(first + second)
        built.append(second + first + second)
    pool = [text for text in dict.fromkeys(built) if text not in FIXED_SUBJECTS]
    rng.shuffle(pool)
    share = min(len(FIXED_SUBJECTS), max(2, count // 4))
    chosen = list(FIXED_SUBJECTS[:share]) + pool[: count - share]
    chosen += [text for text in FIXED_SUBJECTS[share:] if text not in chosen]
    return tuple(text.encode("latin-1") for text in chosen[:count])


def _start(rng: Draw, subject: bytes, family: str, position: int) -> int:
    """A start offset inside the subject, weighted toward the beginning.

    Never past the end: an offset outside the subject is the engine's own
    BadInput and pcre2 has no answer to compare it against, so it is tested
    where it belongs — in the corpus, from the side.

    The quantifier matrix lays its offsets out instead of drawing them, so
    that every cell is asked at a nonzero start rather than most of them: a
    lowered quantifier's copies are what a start offset moves through.
    """
    if not subject:
        return 0
    if family == "quant":
        return (0, 1, len(subject) // 2, len(subject))[position % 4]
    return rng.pick([0, 0, 0, 0, 1, len(subject) // 2, len(subject)])


def case(
    seed: int, index: int, *, subjects: int = SUBJECTS, structured: int = STRUCTURED
) -> Case:
    """One case of the population, built from its four numbers alone."""
    rng = _rng(seed, index)
    family = _family(index, structured)
    text = _pattern(rng, index, family)
    trials = tuple(
        Trial(
            subject=subject,
            match_options=MATCH_OPTION_SETS[(index + position) % len(MATCH_OPTION_SETS)],
            start=_start(rng, subject, family, position),
        )
        for position, subject in enumerate(_subjects(rng, text, subjects))
    )
    newline, bsr = CONVENTIONS[(index // len(OPTION_SETS)) % len(CONVENTIONS)]
    return Case(
        seed=seed,
        index=index,
        family=family,
        pattern=text.encode("latin-1"),
        options=OPTION_SETS[index % len(OPTION_SETS)],
        newline=newline,
        bsr=bsr,
        trials=trials,
        maxlen=max((len(trial.subject) for trial in trials), default=0),
    )


def population(
    seed: int,
    *,
    structured: int = STRUCTURED,
    hostile: int = HOSTILE,
    subjects: int = SUBJECTS,
    stride: int = 1,
) -> tuple[Case, ...]:
    """The whole population of a sweep, in index order.

    `structured` counts the product and the grammar together, so asking for two
    thousand patterns gives two thousand however many atoms there are; `hostile`
    is the mutation-and-soup population beside it, which DESIGN.md section 8
    asks for separately because most of it never compiles.

    `stride` keeps one case in every so many, which is how the committed shard
    is a slice of the campaign's population rather than a population of its
    own. The cases it keeps carry their original indices, so a failure found in
    the shard replays at the same numbers a campaign would name.
    """
    if structured < LAID_OUT:
        raise ValueError(
            f"a structured population starts with the {len(CROSS)} atom-quantifier "
            f"pairs and the {len(QUANT)} cells of the quantifier matrix, so it "
            f"cannot hold {structured}"
        )
    return tuple(
        case(seed, index, subjects=subjects, structured=structured)
        for index in range(0, structured + hostile, stride)
    )
