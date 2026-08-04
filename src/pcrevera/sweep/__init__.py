"""The differential sweep of DESIGN.md section 8, in one place.

Everything that generates a case lives in `population`, so the smoke test that
runs on every commit and the campaign that runs for an hour cannot drift into
describing different populations. A manifest is the population written down:
seeds, patterns, subjects, options, conventions, start offsets and context
maxima, hashed so that a result can name the exact set of cases it came from.

`checks` is what a case is put through — the semantic comparison against pcre2,
the cross-matcher comparison between the Pike VM and the backtracking matcher,
and the resource comparison against the certificate — and it produces one
replayable record per case. `campaign` runs that over a whole manifest and
counts what was covered; `shard` freezes a small deterministic slice of it into
`conformance/sweep.json`, which the Go and JavaScript runners replay through
their own generated engines.

`reduce` is what a failure gets put through before it is written down,
`failures` is the record that comes out — the case, the disagreement class, the
artifact hash and the pinned pcre2 identity, and the command that replays it —
and `promote` is where a minimized case goes once the bug is fixed: to
`oracle/corpus/wave1.json` when what disagreed was an answer, and to
`oracle/corpus/sweep-regressions.json` when it was an invariant no corpus of
answers asks about. Either way the case stops depending on the seed that
found it.
"""

from . import checks, manifest, population
from .population import Case, Trial

__all__ = ["Case", "Trial", "checks", "manifest", "population"]
