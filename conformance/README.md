# The conformance corpora

Four language-neutral JSON files and a small runner per backend. They are what
makes "the Python interpreter, the generated Go, and the generated JavaScript
agree bit for bit" a thing that gets checked rather than hoped for. A fifth
file, `migration.json`, sits beside them and is a report rather than a
contract; it has no runner, and the section below says why.

All of them are generated — `make generate` writes them — and all of them are
committed, so a change to any of them shows up as a reviewable diff and
`make generate-verify` fails on a checkout where one has drifted.

`corpus.json` is the wave 1 differential corpus of `oracle/corpus/wave1.json`,
restated so that a runner in any language can read it without reimplementing
the loader: every byte string is lowercase hex, every option is the number the
engine takes, and every expectation is one tagged object. Nothing in it is
recorded from a run. The expectations are the hand-written ones the pinned
pcre2 also has to satisfy, so a backend that agrees with this file agrees with
pcre2 for the same reason the Python engine does.

`lowering.json` answers a different question. The engine exercises the backends
broadly but not squarely: every multiplication it performs is on a small
offset, so a JavaScript printer that forgot `Math.imul` would pass all 274
pattern cases and then be wrong the first time a product went past 2^53. So
`src/pcrevera/backends/lowering.py` is a small TIR program that does those
things on purpose, with operands sitting on the boundary — the 32-bit widths,
the sign changes, `INT_MIN / -1`, counter saturation at the cap, the growth
schedule read back through `cap`, a struct written through after being copied —
and this file says what every call has to answer.

`certificates.json` is the bound certificates of DESIGN.md section 5 and
BOUNDS.md, and it has three arrays: one per half of that section, and one for
the public surface the halves exist to serve.

Its `cases` are the checker's: each carries the pattern it prices, the verdict
the checker has to draw, which of its two halves drew it, and the three bounds
it has to evaluate at seven subject lengths from zero to the counter's
saturation point. The half is there because the checker answers two questions
and only one of them needs a certificate — whether the tree describes the
program, and whether the certificate bounds it — and compilation runs the first
on its own. A case names a
pattern rather than a bytecode listing, so every runner compiles it with the
engine it has and the checker is handed the program that engine would really
run, region tree included — two backends that disagree about the bytecode or
about the tree therefore disagree here. The handful of cases about trees no
compiler would emit carry one of their own, which the runner puts in place of
the compiler's.

Its `analysis` entries are the analyzer's, and they hand nothing in: compiling
a pattern is what runs it. Each records the analyzer's verdict, the complexity
class it claimed, and the same three bounds — or, for a pattern with no bound
of a representable shape, that the verdict was a refusal and the slot stayed
empty. What the runners evaluate is both the certificate compilation stored and
the one a direct call to the analyzer returns, so a backend that kept something
other than what it computed disagrees here too.

What it does not record is the price of every region, because that is a great
many numbers to pin from the side and the checker already holds each of them to
the bytecode: a backend whose analyzer under-prices a region never reaches this
file, since compiling refuses to store a certificate the checker did not
accept. Python asks the stronger question — that the whole certificate is
exactly what an independent statement of BOUNDS.md computes — in
`tests/test_certificate.py`.

The verdicts are hand-written and the bounds are recorded, which is the honest
split: what the engine refuses is a contract, and transcribing twenty-one
numbers per case by hand would be copying rather than specifying. The checker's
half of this corpus exists because a certificate has no way in through the
public API, so without it the checker would be the one piece of the engine that
both backends carried and neither ran.

`sweep.json` is the committed shard of the differential sweep of DESIGN.md
section 8, and it is the one file here whose cases nobody wrote. They are
generated: `pcrevera.sweep.population` builds a case out of the numbers a
manifest was generated from and the case's own index, and the shard is one case
in every seven of a small population, kept whole — the pattern, up to eight
subjects with their own match flags and start offsets, the options, the newline
and BSR conventions, and the length a preallocated context is created for.

What it records is everything four implementations have to agree about. The
compile outcome and, per trial, the ovector; the three certified bounds at that
subject length and the cost, stack and memory the run really used; the
backtracking matcher's answer where the Pike VM was the one selected; and a
context's reservation and what each call on it used. A trial marked `edges`
also has its three limits re-run at the observed value and one below, which is
the deterministic budget boundary of section 8; the runners compute those
limits from the recorded bound the same way, so a backend whose accessors
disagree runs at different limits and fails on the numbers rather than passing
quietly.

Its `regressions` are the same records for cases nobody generated either: the
ones the sweep has actually found and a reducer has shrunk, kept in
`oracle/corpus/sweep-regressions.json` because a generated population is
rebuilt from a seed and would stop finding them the moment the seed moved on.
They are replayed through exactly the same battery rather than compared to an
expected answer, and that is the point of keeping them here rather than in the
wave 1 corpus: what each one guards is a certified bound, a limit edge, a
context reservation or the two matchers agreeing, and a corpus of expected
answers never asks any of those. A disagreement about an answer still goes to
`oracle/corpus/wave1.json`, which is what that file is for.

A compile outcome comes in three kinds. `compiled` carries the identity of the
program, `compileError` is a pcre2 error the engine reproduces, and `declined`
is one of our own codes — a construct outside the claimed subset, or a pattern
past a documented limit. pcre2 has no opinion about a decline, per the oracle
policy of DESIGN.md section 1, but every implementation of this engine has to
refuse it with the same code at the same offset, so the case is recorded like
any other and only the comparison with pcre2 is skipped.

The file is generated from the engine alone, with no pcre2 anywhere near it, so
that regenerating a committed file never needs a build of the pinned library.
pcre2's opinion of the same cases is a test rather than a file:
`tests/test_sweep.py` replays the shard through the oracle in the same run that
replays it through the interpreter. The chain is the wave 1 corpus's — pcre2
agrees with Python, and Go and JavaScript agree with the file.

`migration.json` is the odd one out, and says so: it is a report rather than a
contract. Every pattern the three files above name gets a row saying what the
quantifier lowering of DESIGN.md section 4.3 did to it — the blockers the
pre-check found on the original tree, the decision they led to, whether
`pike_ok` accepted the emitted program, what the backtracking analyzer answered
about it whichever path was selected, which certificate the pattern carries and
the class it claims, and the three accessors at a thousand bytes. The columns
are deliberately not recombined: a pattern can be Pike-selected and linear
while the backtracking analyzer answers `ArOverflow` for the same program, and
a schema with one certificate column would have to record that as a
contradiction.

No backend replays it, because nothing in it is a claim about a backend: the
generator writes a row only after reproducing the compiler's recorded decision
from the parsed tree, after `pike_ok` has agreed with every lowering, and after
the counter form left behind by a decline has been found to show the blockers
the pre-check named. `tests/test_migration.py` then reads the census off the
columns. A decision the derivation cannot reproduce fails generation rather
than appearing in the file.

The runners, one row per file and one column per language:

```
+-------------------+---------------------------+---------------------------+
| corpus.json and   | tests/test_conformance.py | the Python interpreter    |
| lowering.json     | gen/go/conformance_test   | the generated Go          |
|                   |   .go                     |                           |
|                   | gen/js/test/conformance   | the generated JavaScript  |
|                   |   .test.mjs               |                           |
+-------------------+---------------------------+---------------------------+
| certificates.json | tests/test_certificate.py | the Python interpreter    |
|                   | gen/go/internal/engine/   | the generated Go          |
|                   |   certificate_test.go     |                           |
|                   | gen/js/test/certificate   | the generated JavaScript  |
|                   |   .test.mjs               |                           |
+-------------------+---------------------------+---------------------------+
| certificates.json | tests/test_certificate.py | the Python interpreter    |
|   `accessors`     | gen/go/conformance_test   | the generated Go          |
|                   |   .go                     |                           |
|                   | gen/js/test/accessors     | the generated JavaScript  |
|                   |   .test.mjs               |                           |
+-------------------+---------------------------+---------------------------+
| sweep.json        | tests/test_sweep.py       | the Python interpreter    |
|                   | gen/go/internal/engine/   | the generated Go          |
|                   |   sweep_test.go           |                           |
|                   | gen/js/test/sweep         | the generated JavaScript  |
|                   |   .test.mjs               |                           |
+-------------------+---------------------------+---------------------------+
```

Both sweep runners sit inside the generated module, and for a reason of their
own: the resource half of the sweep is about the `Usage` a call reports, which
the public API does not return. Reaching the generated entry points keeps every
observed number under test without widening what the wrappers promise, and the
wrappers stay covered by the conformance and accessor runners.

The Go certificate runner sits inside the generated package rather than beside
the wrapper, because TIR field names are printed verbatim and Go cannot reach a
lower-case field from another package, so a certificate has to be built there.
The JavaScript one needs no such thing, and the accessor runners need the
opposite: they live beside the wrappers — `gen/go/conformance_test.go` and
`gen/js/test/accessors.test.mjs` — because their whole point is to reach the
numbers the way an application would.

Its `accessors` entries pin that public surface: the complexity class, and for
every configuration and subject length queried, the status and value each
worst-case accessor answers. A status is the engine's outcome ordinal — 0 for
a number, 3 for BadInput, 4 for the ExceedsBudget that is deliberately not
the runtime ResourceExceeded — so a wrapper that folded two refusals together
disagrees here. A query marked `exercise` must also survive a match on a
subject of that length with the three pinned bounds passed unchanged as the
limits: anything but ResourceExceeded. The gate is the pinned cost bound
itself, which also bounds the work such a run can really do, so no runner is
ever told to walk an exponential search to prove a point.
