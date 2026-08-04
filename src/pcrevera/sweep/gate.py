"""The completion gate: what a sweep has to have covered, not how big it was.

DESIGN.md section 8 closes M5 on evidence rather than on a total, so this is
the evidence stated as a list of things that must have happened at least once.
Every opcode and every region kind compiled, both matchers selected, patterns
certified and patterns honestly unpriced, every outcome the engine can give,
every option family and every newline/BSR pair exercised, and every kind of
check actually run.

The two enum lists are read from the program rather than written down here, so
an opcode added in wave 2 is a gate the next sweep has to clear rather than a
line somebody has to remember to add.
"""

from __future__ import annotations

from ..engine.program import program
from . import checks
from .checks import Coverage
from .population import CONVENTIONS, OPTION_SETS

UNGATED = frozenset({"cross-matcher-capped", "cross-matcher-unpriced"})
"""The two counts that are honest zeros. A sweep where no Pike-eligible
pattern's backtracking bound was capped or missing has covered everything and
counted neither, so requiring them would be requiring a shortcoming."""

CHECKS = tuple(name for name in checks.CHECKS if name not in UNGATED)
"""Every kind of check the sweep runs, each of which has to have run. The list
is the one `checks` counts by, so a check added there is a gate here rather
than a counter nobody gates.

`cross-backend` is not a check this process performs: it is how many recorded
values the Go and JavaScript runners are held to when they replay the result
document, which is the coverage figure DESIGN.md section 8 asks for by that
name. Everything else is a comparison made here.
"""

OUTCOMES = ("compiled", "syntax", "declined", "match", "nomatch")

SELECTION = ("pike", "backtrack")

CERTIFIED = (
    "backtrack:certified",
    "backtrack:unpriced",
    "pike:certified",
    "pike:unpriced",
)


def _variants(enum: str) -> tuple[str, ...]:
    return tuple(program().enum_map[enum].variants)


def wanted() -> dict[str, tuple[str, ...]]:
    """Every counter that has to be non-zero, by the group it lives in."""
    return {
        "opcodes": _variants("Op"),
        "regions": _variants("Rk"),
        "selection": SELECTION,
        "certified": CERTIFIED,
        "outcomes": OUTCOMES,
        "options": tuple("+".join(one) or "none" for one in OPTION_SETS),
        "conventions": tuple(f"{newline}/{bsr}" for newline, bsr in CONVENTIONS),
        "checks": CHECKS,
    }


def missing(coverage: Coverage) -> list[str]:
    """What the sweep never reached, named as "group: name"."""
    out = []
    for group, names in wanted().items():
        counted = getattr(coverage, group)
        out.extend(f"{group}: {name}" for name in names if not counted.get(name))
    return out


def table(coverage: Coverage) -> str:
    """The coverage report, as the LOG and the console want to read it.

    Everything the sweep counted, not only what the gate asks about, since a
    counter nobody set a rule for is still the thing a reader wants when a
    campaign comes back with a surprise.
    """
    rows = []
    asked = wanted()
    for group in vars(coverage):
        counted = getattr(coverage, group)
        required = set(asked.get(group, ()))
        for name in sorted(set(counted) | required):
            hits = counted.get(name, 0)
            mark = "" if name not in required else ("ok" if hits else "MISSING")
            rows.append((group, name, str(hits), mark))
    widths = [max(len(row[column]) for row in rows) for column in range(4)]
    widths = [max(width, len(head)) for width, head in zip(widths, ("group", "name", "count", "gate"))]
    rule = "+" + "+".join("-" * (width + 2) for width in widths) + "+"
    lines = [rule, _row(("group", "name", "count", "gate"), widths), rule]
    lines += [_row(row, widths) for row in rows]
    lines.append(rule)
    return "\n".join(lines)


def _row(cells, widths) -> str:
    return "| " + " | ".join(cell.ljust(width) for cell, width in zip(cells, widths)) + " |"
