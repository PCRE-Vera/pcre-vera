# The conformance corpora

Two language-neutral JSON files and a small runner per backend. They are what
makes "the Python interpreter, the generated Go, and the generated JavaScript
agree bit for bit" a thing that gets checked rather than hoped for.

Both are generated — `make generate` writes them — and both are committed, so a
change to either shows up as a reviewable diff and `make generate-verify` fails
on a checkout where one has drifted.

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
`src/pcretruste/backends/lowering.py` is a small TIR program that does those
things on purpose, with operands sitting on the boundary — the 32-bit widths,
the sign changes, `INT_MIN / -1`, counter saturation at the cap, the growth
schedule read back through `cap`, a struct written through after being copied —
and this file says what every call has to answer.

The runners:

```
tests/test_conformance.py            the Python interpreter
gen/go/conformance_test.go           the generated Go
gen/js/test/conformance.test.mjs     the generated JavaScript
```

Expected bounds are the other half of what DESIGN.md section 8 asks for, and
they arrive with the M5 analyzer. There is nothing to write down until then.
