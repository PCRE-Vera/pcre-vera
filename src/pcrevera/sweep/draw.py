"""The generator a case is drawn from, owned by this repository.

`random.Random` seeds reproducibly from a string, but the algorithms on top of
it — how `shuffle` walks, how `randrange` rejects — are CPython's business and
have changed before. A sweep whose manifest hash is written into a freeze
record cannot have its population depend on which interpreter happened to run
it, so the few operations the population needs are written here: SplitMix64
over a SHA-256 seed, an unbiased index, and a Fisher-Yates shuffle.

Small on purpose. This is not a source of randomness anybody should rely on for
anything but spreading cases out, and its whole contract is that the same label
gives the same sequence on every machine, every interpreter, and every year.
"""

from __future__ import annotations

import hashlib

SPAN = 1 << 64
"""How many values a draw can take: the sample space every rejection rule
below counts residues over."""

MASK = SPAN - 1

GAMMA = 0x9E3779B97F4A7C15
"""The odd constant SplitMix64 advances its state by, from Steele, Lea and
Flood's "Fast splittable pseudorandom number generators"."""

MIX_A = 0xBF58476D1CE4E5B9
MIX_B = 0x94D049BB133111EB


def accepted(bound: int) -> int:
    """How many of the `SPAN` possible draws may be folded onto `bound`.

    The largest multiple of `bound` that fits, so that every residue is reached
    exactly as often as every other; the values above it are the ones a draw
    has to throw away. Its own function because the off-by-one here is
    invisible in a histogram and obvious in an equation, and the test asks the
    equation.

    A bound past `SPAN` has no multiple that fits, and a caller who asked for
    one would get a rejection rule that rejects everything — a loop that never
    ends rather than an answer. One draw is one 64-bit value here, and that is
    the range this generator has; asking past it is a mistake, not a request.
    """
    if bound <= 0 or bound > SPAN:
        raise ValueError(f"a draw cannot be spread over {bound} values")
    return SPAN - (SPAN % bound)


class Draw:
    """A deterministic sequence, named rather than seeded with a number.

    Naming it with a string rather than an integer is what keeps neighbouring
    cases apart: two generators started one apart would otherwise share most of
    their output, and the sweep asks for one generator per case.
    """

    __slots__ = ("state",)

    def __init__(self, label: str) -> None:
        self.state = int.from_bytes(hashlib.sha256(label.encode()).digest()[:8], "big")

    def _next(self) -> int:
        self.state = (self.state + GAMMA) & MASK
        z = self.state
        z = ((z ^ (z >> 30)) * MIX_A) & MASK
        z = ((z ^ (z >> 27)) * MIX_B) & MASK
        return z ^ (z >> 31)

    def below(self, bound: int) -> int:
        """A value in `[0, bound)`, with no value more likely than another.

        Draw, reject the tail that would fold one extra time onto the low
        residues, and try again. Unbiased matters less here than being the same
        everywhere, and rejection is the version that is easy to say — but only
        if the tail is counted over the whole sample space, which is `SPAN`
        values rather than the largest one.
        """
        limit = accepted(bound)
        while True:
            value = self._next()
            if value < limit:
                return value % bound

    def between(self, low: int, high: int) -> int:
        """A value in `[low, high]`, both ends included."""
        return low + self.below(high - low + 1)

    def pick(self, items):
        return items[self.below(len(items))]

    def chance(self, numerator: int, denominator: int) -> bool:
        """True that often, written as a fraction so it reads as one."""
        return self.below(denominator) < numerator

    def shuffle(self, items: list) -> None:
        """Fisher-Yates, in place, from the end down."""
        for at in range(len(items) - 1, 0, -1):
            other = self.below(at + 1)
            items[at], items[other] = items[other], items[at]
