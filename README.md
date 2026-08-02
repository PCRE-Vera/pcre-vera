# pcre-truste

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
`TIR-SPEC.md` defines the IR itself, normatively.

## Where the project is

M0 (scaffolding), M1 (the pcre2 oracle), M2 (the TIR core) and M3 (the wave 1
engine) are done.

The Go and JavaScript backends arrive in M4, the Pike VM and the resource
analyzer in M5, and the Lean proofs from M6 on.

Three things work today, and everything else leans on them.

The first is the language the engine will be written in. `TIR-SPEC.md` pins
every operator's result on every input, evaluation order, the trap list, the
storage sizes, and the linearity rules.

Those are the corners where Go and JavaScript disagree and where a Lean
decoder, a Go printer, and a JS printer would otherwise each guess differently.

`src/pcretruste/tir/` implements it: the type model, a canonical JSON codec
whose output is a function of the program alone, a validator whose 43 rules
each have a test that trips them, and a reference interpreter that follows the
specification literally, checks declared loop variants at run time, and stops
at a step bound rather than hanging.

`src/pcretruste/dsl/` is the untrusted builder API the engine gets authored
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

The third is the engine itself. `src/pcretruste/engine/` builds one TIR program
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
from "we do not do this yet". The line sits where pcre2 draws it: a `\g`, `\k`
or `\p` whose spelling pcre2 itself rejects, or a reference to a group that
does not exist, is that genuine pcre2 error, and only the well-formed
construct is our refusal. Two edges of that line stay ours for now: a
well-shaped `\p` name is not checked against the Unicode property tables,
which arrive with wave 3, and a pattern that mixes a bad reference with a
construct we refuse gets the refusal, where pcre2 would finish parsing and
report the reference.

Eight more shapes are refused for a subtler reason, and `engine/spec.py` names
them: pcre2 makes a quantifier possessive when it can prove the repeated item
and the next one never match the same character, and for those eight the proof
is wrong in 8-bit mode, so pcre2 answers differently from its own semantics.
Reproducing that needs possessive repetition, which is wave 2, so wave 1
declines any pattern where one of the eight repetitions has its unsafe partner
somewhere after it — or anywhere at all when a group is repeated, because
pcre2 replicates repeated groups and can pair items across the copies. That is
broader than the exact next-item question, deliberately: refusing too often is
a smaller sin than answering wrongly.

Every match runs under a cost limit, a stack-entry limit and a scratch-memory
limit, and returns ResourceExceeded rather than running long. The bounds those
limits are compared against are still the caller's; computing them from the
pattern is M5's analyzer.

`oracle/corpus/wave1.json` is 264 hand-written cases that our engine, the
pinned pcre2, and the expectation all have to agree on. A generated sweep in
`tmp/` puts far more than that to both engines at once.

## Getting started

```
make setup          # the Python environment, through uv
make oracle-verify  # build the pinned pcre2 and check it against the pin
make test           # the Python tests, seed corpus included
make check          # all of the above, plus lake build, go test, node --test
```

The oracle build downloads a 2 MB tarball and compiles the 8-bit library only,
which takes a few seconds. `oracle/README.md` covers the protocol, the pin, and
the environment variables for a build machine with a shared cache or no
network.

## Layout

```
+-------------------+------------------------------------------------------+
| objective.md      | what the project is for                              |
| DESIGN.md         | the plan, in full                                    |
| TIR-SPEC.md       | the IR, defined normatively                          |
| LOG.md            | what was asked and what was done, step by step       |
| MISTAKES.md       | what earlier drafts got wrong, kept as a trap list   |
| api-faq.md        | APIs that did not behave the way we first assumed    |
| src/pcretruste/   | the generator and all its tooling                    |
| oracle/           | the pcre2 pin, the C shim, the seed corpus           |
| lean/             | the lake project: the four proof layers              |
| gen/go, gen/js    | generated code plus hand-written wrappers            |
| conformance/      | the language-neutral corpus (arrives with M4)        |
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
