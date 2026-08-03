# pcre-vera

An experiment to see if AI can build PCRE-compatible regex engines that aren't garbage.

A generator for a PCRE engine whose cost you can know in advance: one engine,
written once in a small verified-friendly IR, proved in Lean against a
mechanized PCRE specification, and printed out as idiomatic Go and JavaScript.

A compiled pattern can tell you its worst-case cost, stack, and memory before
you ever run it, and every match runs under hard limits.

What that buys, said the way DESIGN.md section 5 insists on saying it, is
deterministically bounded work per call, every instruction charged, every
scratch byte accounted for, and allocation-free matching when a preallocated
context is used.

It does not turn Go or a browser into a hard-realtime system. Garbage
collection, JIT warmup, and scheduling belong to the host runtime and sit
outside the model.

`objective.md` says what this is for. `DESIGN.md` says how it gets built in
detail, from the IR design through the proof layering to the milestones.
`TIR-SPEC.md` defines the IR itself, normatively, and `BOUNDS.md` does the
same for the resource bounds.

## Where the project is

M0 (scaffolding), M1 (the pcre2 oracle), M2 (the TIR core), M3 (the wave 1
engine) and M4 (the Go and JavaScript backends) are done. M5, the Pike VM and
the resource analyzer, has started; the Lean proofs follow from M6 on.

Four things work today, and everything else leans on them.

The first is the language the engine will be written in. `TIR-SPEC.md` pins
every operator's result on every input, evaluation order, the trap list, the
storage sizes, and the linearity rules.

Those are the corners where Go and JavaScript disagree and where a Lean
decoder, a Go printer, and a JS printer would otherwise each guess differently.

`src/pcrevera/tir/` implements it: the type model, a canonical JSON codec
whose output is a function of the program alone, a validator whose 43 rules
each have a test that trips them, and a reference interpreter that follows the
specification literally, checks declared loop variants at run time, and stops
at a step bound rather than hanging.

`src/pcrevera/dsl/` is the untrusted builder API the engine gets authored
against. `tests/golden/toy.tir.json` is a small program — bounded Fibonacci
with an explicit stack — that round-trips from the DSL through the artifact and
back into the interpreter.

The second is the reference the answers are checked against. pcre2 is not one
behavior; it is one build.

`oracle/pcre2-pin.toml` pins the release, its tarball hash, the complete
configure flags, and every field the linked library must report back about
itself, down to the 1088 bytes of default character tables that decide what
`\w` and `\b` mean. The one knob that `pcre2_config` cannot report is pinned by
behavior in the corpus instead.

`make oracle-verify` builds that exact library from source and checks it.
`oracle/pcre2shim/shim.c` answers questions about it over a line protocol so
the rest of the project can ask pcre2 what a pattern does.

The third is the engine itself. `src/pcrevera/engine/` builds one TIR program
— a pattern parser, a bytecode compiler, and a backtracking matcher — and
`driver.py` runs it through the reference interpreter, so it can be tested
years before either backend exists.

It covers the wave 1 subset of DESIGN.md section 2.1: literals, `.`, character
classes with ranges, negation, POSIX names and the `\d \w \s \h \v \R` family,
the anchors, alternation, greedy and lazy quantifiers, capturing, named and
non-capturing groups, `\Q...\E`, inline option groups, and comment groups, with
the eight compile options, five newline conventions, both `\R` conventions, and
the match-time options and start offset.

Anything outside that subset — back references, lookaround, atomic groups,
possessive quantifiers, `\K`, `\p`, subroutine calls, callouts, verbs — is
refused with our own UnsupportedFeature or UnsupportedOption code, never a
repurposed pcre2 one, so a caller can always tell "PCRE says this is wrong"
from "we do not do this yet".

The line sits where pcre2 draws it: a `\g`, `\k` or `\p` whose spelling pcre2
itself rejects, or a reference to a group that does not exist, is that genuine
pcre2 error, and only the well-formed construct is our refusal.

Two edges of that line stay ours for now: a well-shaped `\p` name is not
checked against the Unicode property tables, which arrive with wave 3, and a
pattern that mixes a bad reference with a construct we refuse gets the
refusal, where pcre2 would finish parsing and report the reference.

Eight more shapes are refused for a subtler reason, and `engine/spec.py` names
them: pcre2 makes a quantifier possessive when it can prove the repeated item
and the next one never match the same character. For those eight, the proof is
wrong in 8-bit mode, so pcre2 answers differently from its own semantics.

Reproducing that needs possessive repetition, which is wave 2, so wave 1
declines any pattern where one of the eight repetitions has its unsafe partner
somewhere after it — or anywhere at all when a group is repeated, because
pcre2 replicates repeated groups and can pair items across the copies.

That is broader than the exact next-item question, deliberately: refusing too
often is a smaller sin than answering wrongly.

Every match runs under a cost limit, a stack-entry limit and a scratch-memory
limit, and returns ResourceExceeded rather than running long. Compilation
computes what those limits would have to be, which is the analysis below, and
the accessors on the compiled pattern report it before anything runs.

`oracle/corpus/wave1.json` is 264 hand-written cases that our engine, the
pinned pcre2, and the expectation all have to agree on. A generated sweep in
`tmp/` puts far more than that to both engines at once.

The fourth is the pair of backends. `make generate` writes
`gen/engine.tir.json` — the canonical artifact, whose SHA-256 is the identity
everything downstream is pinned to — and then prints it as a Go package and an
ES module, each stamped with that hash in a header comment and in a constant.
Both are committed, and `make generate-verify` refuses a checkout where one is
not what today's generator produces.

The printers are the dumbest part of the system on purpose: one output
construct per input node, no optimization, no reordering.

`TIR-SPEC.md` section 16 lists what each language gets wrong if lowered
naively, and the two that matter are silently wrong rather than merely slow.
In JavaScript a 32-bit product has to go through `Math.imul`, because a plain
double product loses low bits before any `| 0` could look at them. A copyable
struct has to be cloned when it is read out of storage, because a class instance
is a reference where a Go struct is a value.

Neither of those shows up in the pattern corpus — the engine's own
multiplications are all small — so `conformance/lowering.json` asks about them
directly.

It is 4040 cases over a small TIR program that multiplies at the boundary,
saturates counters at the cap, divides `INT_MIN` by -1, grows vectors one push
at a time and reads the capacity back, writes through a struct it just copied,
fills one sequence of every element type there is — the engine itself only ever
uses two — and overflows a named constant, which Go folds at compile time and
would refuse rather than wrap.

`conformance/corpus.json` is the wave 1 corpus restated in a form any language
can read, and `conformance/certificates.json` does the same for the analysis
below. All three files run against the Python interpreter, the generated Go,
and the generated JavaScript, and all three languages have to give the same
answers.

Compilation now fixes each pattern's execution path: the lockstep Pike VM
when the pattern is eligible — every repetition a pure star whose body has to
consume, nothing variable-width — and the backtracking matcher otherwise.
What works is compile, match on the selected path under the hard limits, and
the analysis accessors of DESIGN.md section 2.4 — `complexityClass`, and the worst-case cost, stack
and memory at a subject length, each answering for the path that will
actually run: a number a caller can pass straight back as the matching limit,
an explicit ExceedsBudget, or BadInput.
The match configuration argument is in its final shape too, though only the
default value exists until M9 activates memoization; the preallocated match
context arrives with the rest of M5.

M5 has started with the resource analysis. DESIGN.md section 5 does not have
one analyzer computing numbers everything then trusts; it has an analyzer that
searches for a bound certificate and a deliberately small checker that decides
whether to believe one.

Only the checker gets proved, which is why it was built first.
`engine/certificate.py` is that checker, `engine/analyzer.py` is the search,
and [BOUNDS.md](BOUNDS.md) is the rule set they both apply: what every opcode
costs, what every region kind composes to, and what a whole call pays for setup,
for its n + 1 starting positions and for the scratch it grows.

They share the arithmetic and state the composition twice, because a checker
whose verdict restated the analyzer's own working would not be worth running.
The subject is the compiled pattern itself, so an accepted certificate is about
the bytecode the matcher would really run.

The region tree those rules compose over is the compiler's. It emits one while
it still has the AST in hand, which is the only moment anything knows that this
stretch of instructions came from that quantifier, and it stores it on the
compiled pattern.

A certificate holds one price per region and no second copy of the tree. That
does not make the tree trusted: the checker reads it back against the bytecode,
so a compiler that emitted a tree not describing its own output would be
refused exactly like a hand-written one.

Compiling a pattern now runs both halves, and what comes out is stored only
after the checker has said `CrOk`.

That means, exactly: for this program, in this configuration, at every subject
length, every start offset and every combination of match options, the matcher
charges no more cost, pushes no more backtrack entries and reserves no more
scratch than the certificate names.

Take one unit off any of those numbers and the checker says which one and why.
A bound comes back as a number or as an explicit refusal, never as a saturated
counter dressed up as a maximum. The two projections with a ceiling of their
own refuse past it too, so any number an accessor gives back is one the caller
can turn round and pass as a limit.

Some patterns get no certificate at all. `(?:a*)*` hands its outer loop more
ways to match at every extra byte of subject, so the pass count is a power of a
polynomial and no bound of this shape has that form. `a*b*c*d*` needs a fifth
power of n where there are four. `(?:a|a){0,44}` needs a coefficient no counter
holds.

Those patterns compile and match like any other and simply have no bound, and
the accessors report the explicit ExceedsBudget for them, which is the honest
answer rather than a number that would be wrong.

## Using it

Go, from `gen/go` (the example is `Example` in `gen/go/example_test.go`, so it
is run rather than admired):

```go
package main

import (
	"fmt"
	"log"

	pcrevera "github.com/PCRE-Vera/pcre-vera/gen/go"
)

func main() {
	re, err := pcrevera.Compile(`(?<user>\w+)@(?<host>[\w.]+)`, pcrevera.Options{})
	if err != nil {
		log.Fatal(err)
	}

	subject := []byte("write to alice@example.org, please")
	ovector, err := re.Match(subject, 0, 0, pcrevera.DefaultLimits(), pcrevera.DefaultConfig)
	if err != nil {
		log.Fatal(err)
	}
	if ovector == nil {
		fmt.Println("no match")
		return
	}

	group := func(n int) string { return string(subject[ovector[2*n]:ovector[2*n+1]]) }
	fmt.Printf("%s is %s at %s\n",
		group(0), group(re.SubexpIndex("user")), group(re.SubexpIndex("host")))
}
```

JavaScript, from `gen/js` (and `gen/js/test/example.test.mjs`):

```js
import { compile, defaultLimits } from "./gen/js/index.mjs";

const re = compile(String.raw`(?<user>\w+)@(?<host>[\w.]+)`);

const subject = new TextEncoder().encode("write to alice@example.org, please");
const ovector = re.match(subject, { limits: defaultLimits() });
if (ovector === null) {
  console.log("no match");
} else {
  const group = (n) =>
    new TextDecoder().decode(subject.subarray(ovector[2 * n], ovector[2 * n + 1]));
  console.log(`${group(0)} is ${group(re.groupIndex("user"))} at ${group(re.groupIndex("host"))}`);
}
```

Both print `alice@example.org is alice at example.org`.

Entries 0 and 1 of the ovector are the whole match, then a pair per capturing
group, with -1 for both ends of a group that did not take part. A subject that
does not match is a nil ovector in Go and `null` in JavaScript, not an error.

Everything else — a budget exhausted, a start offset outside the subject, a
limit past what any target could honor — is an error with a code the two
languages agree on.

Subjects are byte sequences and stay that way until UTF mode arrives in wave 3.
A Go pattern is a string because a Go string already is an arbitrary byte
sequence. A JavaScript pattern may be a string as long as every code unit fits
in a byte — one that does not is asking for UTF mode, and comes back as
UnsupportedFeature at the offset that asked.

## Getting started

```
make setup          # the Python environment, through uv
make oracle-verify  # build the pinned pcre2 and check it against the pin
make test           # the Python tests, seed corpus included
make generate       # rewrite the artifact, both backends, and the corpora
make check          # all of the above, plus lake build, go test, node --test
```

The oracle build downloads a 2 MB tarball and compiles the 8-bit library only,
which takes a few seconds.

`oracle/README.md` covers the protocol, the pin, and the environment variables
for a build machine with a shared cache or no network.

`make check` also runs eslint over the JavaScript, which is the one step that
wants the npm registry, and only the first time. `gen/js/package-lock.json`
pins it and the install is skipped once `node_modules` exists. `make js` on its
own has no dependencies at all.

## Layout

```
+-------------------+------------------------------------------------------+
| objective.md      | what the project is for                              |
| DESIGN.md         | the plan, in full                                    |
| TIR-SPEC.md       | the IR, defined normatively                          |
| BOUNDS.md         | the resource bounds, rule by rule                    |
| LOG.md            | what was asked and what was done, step by step       |
| MISTAKES.md       | what earlier drafts got wrong, kept as a trap list   |
| api-faq.md        | APIs that did not behave the way we first assumed    |
| src/pcrevera/     | the generator and all its tooling                    |
| oracle/           | the pcre2 pin, the C shim, the seed corpus           |
| lean/             | the lake project: the four proof layers              |
| gen/              | the canonical artifact everything is pinned to       |
| gen/go, gen/js    | generated code plus hand-written wrappers            |
| conformance/      | the language-neutral corpora, one runner per backend |
| tmp/              | scratch, never committed                             |
+-------------------+------------------------------------------------------+
```

## What is and is not claimed

Worth saying early, because the point of the exercise is precision.

The theorems, once they exist, will cover the IR artifact under the TIR
semantics. The translation from that artifact to Go and JavaScript is a
separate link, kept small and covered by cross-implementation testing.

The generated libraries are never described as formally verified. They are
generated from a formally verified artifact by a printer that is tested.

Equally, no theorem can relate our specification to the pinned C library. That
correspondence rests on the specification being readable and on differential
testing, feature by feature.

DESIGN.md sections 3.3 and 6 spell both out.
