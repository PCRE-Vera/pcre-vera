# The conformance corpora

Three language-neutral JSON files and a small runner per backend. They are what
makes "the Python interpreter, the generated Go, and the generated JavaScript
agree bit for bit" a thing that gets checked rather than hoped for.

All three are generated — `make generate` writes them — and all three are
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
offset, so a JavaScript printer that forgot `Math.imul` would pass all 264
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
```

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
