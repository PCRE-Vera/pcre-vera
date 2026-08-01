# Objective

## What we ship

A Python tool that **generates** a correct, bounded PCRE engine.
It isn't a regex library written by hand in each language: it's a pipeline.
The engine is authored once, in Python, and emitted as an intermediate representation (IR) from which idiomatic Go and JavaScript libraries are produced.
The IR is also consumed by a Lean 4 project that proves the engine implements a mechanized PCRE specification within explicit resource limits.

The generated libraries contain the full pattern parser, so applications compile patterns at runtime, query the compiled pattern for its worst-case cost, and decide whether to run it.
Matching is always against a pre-parsed expression.
Pre-parsing may be expensive, but matching must have bounded, predictable resource consumption per call.
An application must be able to check, before ever running a match, whether a pattern can be evaluated linearly, or to refuse it if evaluation would require more time or stack than the application can budget.

## Why

PCRE has decades of edge cases and its standard library (libpcre2) is a large C codebase.
Reimplementing it by hand in each language is error-prone and means each implementation drifts.
Applications that need PCRE semantics in Go or JavaScript and also need predictable worst-case behavior: realtime systems, request handlers with latency budgets, embedded runtimes: currently have no good option.
This project gives them one: a correct engine, proved in Lean, with concrete resource guarantees, generated once and verified once, not re-implemented per language.

## Correctness

The generated engine must return the same results as the pcre2 library for every supported construct.
This means:

- We pin one specific pcre2 release and build configuration.
  "Correct PCRE" isn't one behavior; it depends on compile-time flags, character tables, the 8-bit vs. 16-bit library, and the release version.
  The objective pins all of these, recorded in the repository, so the ground truth is reproducible.
- The design must define a compatibility policy: what happens when pcre2 releases a new version, what happens when behavior and documentation disagree, and how we handle constructs pcre2 supports but we don't (yet).
- A differential oracle harness that links the pinned pcre2 and compares results field by field: match outcome, capture group offsets, compile errors: must exist before we claim correctness for any feature.
- The Lean proofs must cover the engine's post-parse path: from pattern AST through bytecode execution to match outcome, including resource-exhaustion behavior.
  The specification in Lean defines what "correct PCRE" means for our purposes, and it must be auditable against the pcre2 documentation.
- The IR artifact the code generators consume must be the same artifact the Lean proofs were checked against.
  Hash pinning ties them together.

The parser: pattern text to AST: is a tested link in the first releases, with a parser correctness proof planned as a later milestone.
Until that proof lands, every feature whose full proof chain is incomplete is gated behind an explicit opt-in; the default surface is exactly the proved surface.

## Resource guarantees

The realtime use case is a first-class requirement, not an afterthought.
The engine must provide, for every compiled pattern, concrete numeric bounds that hold for every possible match call:

- **Cost**: a finite upper bound on the work a match call performs, expressed in a deterministic unit: instruction visits, byte comparisons.
  The bound must be a closed-form function of the subject length, evaluated at compile time, exposed through the public API.
  Not a hope, not an average.
- **Stack**: a finite upper bound on the depth of the engine's internal backtracking stack.
  The host-language call stack must be a static constant; any variable-depth state lives on an engine-managed explicit stack with checked capacity.
  The bound must be exposed through the public API.
- **Memory**: a finite upper bound on the scratch memory a match call allocates, covering every per-call array: backtrack stack, thread lists, capture slots, lookaround frames, ovector.
  The bound must be exposed through the public API.
- **Hard limits at match time**: every match call accepts explicit cost, stack, and memory limits in the same units as the analysis.
  A call that would exceed any limit returns a deterministic `ResourceExceeded` instead of a match result: never a blown host stack, never unbounded work.
- **Classification**: the compiled pattern reports its complexity class: linear or not.
  The linear classification must be proved sound.
  Other classifications are conservative advisory labels; they may overestimate, never underestimate.

The design must also address allocation-free matching: a reusable match context preallocated once from the compiled pattern's bounds, so that successive match calls perform no allocation at all.
That is as far as the engine can go on its own, and the documentation must say so wherever the word realtime appears: what we guarantee is deterministically bounded work per call and allocation-free matching when a context is used.
It doesn't turn Go or a browser into a hard-realtime system.
Garbage collection pauses, JIT warmup, and scheduling belong to the host runtime and sit outside our model; latency budgets are the application's judgment of its own runtime.

## API surface

Each generated library must expose, in idiomatic form for its language:

- `compile(pattern, options)` producing a compiled regex or a compile error with pcre2-compatible error codes and byte offsets.
- `match(subject, startOffset, matchOptions, limits)` returning found/not-found plus the ovector: byte offsets of the whole match and every capture group: named groups resolvable to indices, or `ResourceExceeded` when a limit is hit.
- A `find all` iterator built on repeated match calls under a precisely specified advance rule that handles empty matches, \K, and newline conventions correctly.
  The rule must be defined in this document or a companion spec, not left to each backend's interpretation.
- Group-name introspection.
- The analysis accessors described above.

Subjects are byte arrays in every language.
String overloads may arrive with UTF support in a later phase, but the canonical type is bytes so offsets are portable and semantics don't depend on host string encoding.

## Intermediate representation

The IR is the load-bearing design decision.
It must satisfy several constraints simultaneously:

- It must be directly translatable to Go and to JavaScript, with a mapping close to one-to-one: no optimization passes in backends, no reinterpretation.
- It must be directly translatable into Lean as a deep embedding, so the proofs reason about the same artifact the backends consume.
- It must be directly interpretable in Python for testing, long before backends and proofs exist.
- It must be serializable as a single deterministic JSON file whose hash is the identity that ties Python, Lean, Go, and JS together.

The IR describes the *engine*, not individual regexes.
It's the program that parses patterns, compiles bytecode, and runs matchers: authored once in a Python DSL that emits IR, never written by hand.

The IR must be shaped for Go-like targets: explicit stacks, no recursion, C-like control flow, value types.
Backends for Rust and C are planned later; the IR mustn't preclude them.

## Feature staging

We don't implement all of PCRE at once.
The objective adopts a wave-based scope, where each wave adds features to the engine, the proofs, and the backends:

- **Wave 1**: literals, character classes, anchors, alternation, greedy and lazy quantifiers, capturing and non-capturing groups, named groups, inline options, and the core compile-time and match-time options.
  This is the subset for which the linear matcher is intended to cover essentially all patterns, and it's the subset the first Lean proofs target.
- **Wave 2**: backreferences, lookahead, bounded lookbehind, atomic groups, possessive quantifiers.
- **Wave 3**: UTF-8 mode with case folding, Unicode property classes, UCP, conditionals, subroutine calls and recursion: with depth limits threaded through the resource system first.

A feature whose proof chain is incomplete isn't silently "supported": compiling a pattern that needs it fails unless the caller explicitly opts in.
The default surface of every release is exactly what's proved.

## First backends: Go and JavaScript

Go and JavaScript are the primary targets because they cover the two most common cases where PCRE semantics with bounded resources would be valuable: Go for server-side request handlers and embedded systems, JavaScript for browsers and Node.js runtimes.

Both backends must:

- Produce idiomatic, readable code that passes the host language's standard tooling (`go vet`, eslint).
- Implement the same deterministic resource accounting: identical cost units, identical saturation points, identical growth policies: so analysis results are portable.
- Handle integer arithmetic identically despite JavaScript's lack of native 64-bit integers.
  The design must work within JavaScript's number type (`Number.MAX_SAFE_INTEGER` = 2^53 − 1) without BigInt, which is too slow for match hot loops.
- Realize the same trap semantics: bounds-check failures, invalid states: in language-appropriate ways: a panic in Go, a thrown error in JavaScript.
  Never silent corruption.

The generated code is the output of a syntax-directed printer, not a compiler.
It's deliberately kept small: roughly 1500 lines per backend: so it's reviewable by eye and testable by cross-comparison.
A verified backend is a possible future hardening, not a wave 1 requirement.

## Proof strategy

The Lean project must provide, by 1.0, a proof chain from PCRE specification through engine execution to match outcome for every feature reachable without the opt-in flag.
The architecture of the proofs: how they're layered, what's proved first, what's deferred: is a design concern, but the objective requires that:

- The specification is auditable against the pcre2 documentation and the pinned build's behavior.
- The resource bounds are proved sound, not just tested.
- The linear classification is proved sound.
- The proofs are checked by `lake build` in CI, and CI refuses to ship an artifact whose hash doesn't match the one the proofs were checked against.

Parser correctness may be the last link proved; until then, the parser is covered by differential testing and fuzzing against the pinned pcre2.

## Testing

Testing covers every link the proofs don't.
The objective requires:

- Differential testing against the pinned pcre2 build for every supported feature, comparing match outcomes and ovectors field by field.
- Fuzzing: grammar-based pattern generation plus structure-aware subjects, driven continuously, comparing pcre2, the Python IR interpreter, the generated Go, and the generated JS.
  Any disagreement is a bug.
- Resource bound testing: for every fuzz case, instrument and assert that actual cost, stack depth, and scratch memory stay within the analyzer's bounds.
- A language-neutral conformance corpus against which every backend and the Python interpreter must agree bit for bit.

## Open questions for the design phase

These are questions the objective raises but doesn't answer; the design plan (DESIGN.md) must resolve them:

1. How do we scope "same results as pcre2" when our engine and pcre2 meter work differently and hit resource limits at different points?
   What's the oracle policy for runs where one engine exceeds its budget?
2. What's the exact pcre2 configuration: release tag, build flags, character tables: that we pin as ground truth?
3. What's the exact advance rule for the `find all` iterator, especially around empty matches, \K, and CRLF newline handling?
4. How do we represent integer types in the IR so that Go: with 64-bit ints: and JavaScript: with 53-bit safe integers: compute identical results?
5. How do we handle mutation, aliasing, and heap-allocated values in the IR so that the Lean model is simple and the Go/JS translations are natural?
6. What's the exact cost model: what events are charged, and in what units?
7. How do we ensure the IR artifact consumed by Lean is byte-for-byte the same one consumed by the backends?
8. What's the IR's type system and control flow: how do we represent loops, conditionals, function calls, and errors without recursion or exceptions?
9. How do we stage the Lean proofs so that early milestones produce useful theorems without blocking engine development?
10. What's the exact set of compile-time and match-time options we support in wave 1, and what's the behavior of unsupported options?
11. How do we handle the pattern-text-to-AST link before the parser proof lands: what testing and what gating keeps the correctness claim honest?
12. How much of pcre2's error-message text do we reproduce, versus only matching error codes and offsets?
13. Can subroutine calls and recursion: (?R), (?1), (?&name): meet the bounded-resources promise, or should they stay behind an opt-in?

The design plan must answer all of these, and any additional questions that arise.
