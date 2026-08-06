# pcre-vera — design plan

This document describes how we plan to build pcre-vera: a Python tool that
produces a formally verified PCRE engine as an intermediate representation
(IR), from which idiomatic Go and JavaScript libraries are generated. It is
the working plan for the whole project, from the first commit to the first
usable release. The objective it implements is in `objective.md`.

## 1. What we are building, in one page

The deliverable is not a regex library written by hand in each language. It is
a pipeline:

```
+--------------------+      +------------------+      +---------------------+
| engine sources     | ---> | IR artifact      | ---> | Go backend  -> .go  |
| (Python DSL)       |      | engine.tir.json  |      | JS backend  -> .mjs |
+--------------------+      +--------+---------+      +---------------------+
                                     |
                                     v
                            +------------------+
                            | Lean-side TIR    |
                            | JSON decoder     | ---> lake build type-checks
                            +------------------+      the proofs against this
                                                      exact artifact
```

The PCRE engine itself (pattern parser, bytecode compiler, analyzers, and two
matchers) is authored once, in Python, using a small embedded DSL that builds
IR instead of executing directly. The IR is a tiny, typed, structured
imperative language designed so that three consumers can handle it easily:

1. A Lean 4 project, which imports the IR as a deep embedding and proves that
   the engine implements a mechanized PCRE specification, terminates, and
   respects explicit stack and step bounds.
2. Code generators ("backends") that print the IR as readable Go and
   JavaScript. The mapping is close to one-to-one because the IR is shaped
   like a Go-like language from the start.
3. A reference interpreter in Python, used to test the engine long before the
   backends and proofs exist, and later to cross-check them.

A key point that shapes everything: the IR describes the *engine*, not one
regex. The generated Go and JS libraries contain the full pattern parser, so
applications compile patterns at runtime, then query the compiled pattern for
its worst-case cost before deciding to run it. Pre-parsing may be expensive;
matching must be predictable.

The correctness target is PCRE2 semantics against a pinned libpcre2
configuration (section 2.4): for every supported pattern and subject, and for
every execution that completes within the configured resource limits, the
same match, the same group captures, the same byte offsets. When a limit is
hit we return a deterministic ResourceExceeded instead of pcre2's answer.
Our limits and pcre2's match_limit and depth_limit meter different
implementation events, so no numeric setting makes them "equivalent"; the
oracle policy is therefore: pcre2 runs with generous limits, result
equality is asserted only for runs where our engine completes within its
own budgets, and the behavior of the limits themselves is tested against
our Lean semantics (which defines them), not against pcre2's counters.

## 2. Scope

### 2.1 Pattern features

We stage features in three waves. The wave 1 subset is chosen so the linear
matcher can handle essentially all of it, which keeps the first Lean
proofs tractable. Three documented carve-outs route a wave 1 pattern to the
backtracking matcher instead:

- a counted repetition whose lowered form exceeds one of the section 4.3
  program-size caps;
- a star whose body can complete an iteration without consuming a byte,
  which is the `(a?)*` capture-preference problem of section 4.3 — semantic,
  and no amount of lowering removes it;
- a `\R` the program emits, until `\R` compiles as an alternation, because
  it consumes a variable number of bytes. Emits, not mentions: a `\R` inside
  a `{0}` repetition compiles to nothing and carves nothing out.

All three say which matcher runs and nothing about the class. The two are
not the same question and do not coincide: `\R` routes to the backtracking
matcher and still classifies linear, because its certified bound is linear.
The linear guarantee is always stated per pattern by the classifier, never
as a blanket property of the wave and never read off the routing.

```
+--------+----------------------------------------------------------------+
| Wave   | Features                                                       |
+--------+----------------------------------------------------------------+
| 1      | literals, ., character classes [..] with ranges and negation,  |
|        | \d \D \w \W \s \S \h \v \R, POSIX classes [:alpha:] etc.,      |
|        | anchors ^ $ \A \z \Z \b \B, alternation, greedy and lazy       |
|        | quantifiers ? * + {m,n}, capturing groups, non-capturing       |
|        | groups, named groups (?<name>...), \Q...\E, escapes, inline    |
|        | option groups (?i) (?i:...), comment groups (?#...)            |
+--------+----------------------------------------------------------------+
| 2      | backreferences \1 \k<name>, lookahead (?= (?!, bounded         |
|        | lookbehind (?<= (?<!, atomic groups (?>...), possessive        |
|        | quantifiers ++ *+ ?+ {m,n}+, \G                                |
+--------+----------------------------------------------------------------+
| 3      | UTF-8 mode with case folding, Unicode properties \p{..} and    |
|        | UCP, conditionals (?(1)...), \K; subroutine calls (?1)         |
|        | (?&name) and recursion (?R) only if the section 12 question    |
|        | resolves favorably, with their depth limit threaded through    |
|        | the whole resource and proof contract first                    |
+--------+----------------------------------------------------------------+
```

Out of scope for now: callouts, backtracking control verbs ((*SKIP),
(*PRUNE), ...), \C, script runs, \X grapheme clusters, and the pcre2 JIT-only
behaviors. These are rarely used and several of them fight the whole point of
bounded execution. We can revisit once the rest is solid.

### 2.2 Options

Compile-time options in wave 1: CASELESS, MULTILINE, DOTALL, EXTENDED,
UNGREEDY, ANCHORED, ENDANCHORED, DOLLAR_ENDONLY, plus the newline convention
(NEWLINE_LF, NEWLINE_CR, NEWLINE_CRLF, NEWLINE_ANYCRLF, NEWLINE_ANY) and the
\R convention (BSR_UNICODE, BSR_ANYCRLF), because ^, $, ., and \R all depend
on them. Match-time options: NOTBOL, NOTEOL, NOTEMPTY, NOTEMPTY_ATSTART,
ANCHORED, plus a start offset. Any option we do not support is a compile
error, never silently ignored. UTF and UCP arrive with wave 3; until then
the engine works on bytes, which matches pcre2 running without PCRE2_UTF.

### 2.3 PCRE2 compatibility policy

"Correct PCRE" is not one behavior; it depends on how libpcre2 was built and
configured. We pin the reference exactly: one pcre2 release tag (recorded in
the repo along with the source tarball hash, the complete configure flags,
and the harness build recipe), the 8-bit library, default C locale character
tables, defaults NEWLINE_LF and BSR_UNICODE (both overridable through the
options above), no JIT. The oracle harness builds that exact pcre2 from
source so the ground truth is reproducible on any machine. Behavior of \w,
\s, \b, POSIX classes, and caseless matching in byte mode follows those
default tables. Any construct whose behavior depends on a build-time knob we
have not pinned is either added to the pin record or kept out of scope.
Moving to a newer pcre2 release is an explicit, documented compatibility
change, never a silent bump. When pcre2's documentation and its behavior
disagree, the behavior of the pinned build wins.

The correctness claim itself is scoped the same way: each release claims
pcre2-equivalent results for its documented, versioned supported subset,
the wave tables above narrowed by that release's proof inventory, and
nothing outside it; an unsupported construct is a distinct compile
error, never a silent approximation. That is how we read the objective's
"same results as the pcre library": exact agreement wherever support is
claimed, an honest refusal wherever it is not, with the supported set
growing wave by wave rather than the claim rounding up.

### 2.4 Generated API surface

Each backend must expose, in idiomatic form for its language:

- `compile(pattern, options) -> CompiledRegex | CompileError`. The pattern,
  like the subject, is canonically a byte sequence, and compile error
  offsets are byte offsets into it. In Go a string already is an arbitrary
  byte sequence, so `pattern string` is fine as is. In JavaScript the
  canonical form is Uint8Array; a string is accepted as a convenience only
  if every code unit is <= 0xFF (read as Latin-1 bytes), anything else is a
  compile error until UTF mode exists. Compilation has its own
  deterministic size policy: documented portable limits on pattern length,
  parse depth, AST nodes, bytecode size, and table sizes, all far below
  the IR array ceiling and all pre-checked, so an oversized but valid
  pattern fails with a distinct PatternTooLarge error identically in every
  language instead of hitting an allocation wall somewhere; the oracle
  compares only patterns inside both engines' documented limits. Compile
  errors carry pcre2-compatible error codes and byte offsets; those two
  fields are the tested contract, while the message text is our own. That compatibility
  applies to genuine syntax errors. A construct or option pcre2 accepts but
  we deliberately do not support fails with our own distinct
  UnsupportedFeature or UnsupportedOption code, never a repurposed pcre2
  code.
- On `CompiledRegex`:
  `match(subject, startOffset, matchOptions, limits, matchConfig)`
  returning found/not-found plus the ovector (byte offsets of the whole match
  and every capture group, named groups resolvable to indices), an iterator
  style `find all` built on repeated match calls under the exact advance
  rule pinned below, and group-name introspection. The `matchConfig`
  argument is one value used consistently across the whole API: the same
  configuration the analysis accessors price and context creation bakes
  in. Today it only chooses memoized backtracking or not, it defaults to
  the path compilation selected, and a value the pattern is not eligible
  for is BadInput (section 4.3). The start offset
  must lie within [0, subject length]; any other value yields the
  deterministic BadInput outcome in every language, part of the formal and
  oracle contracts alike. Ovector entries are i32 byte offsets; a group that did not participate in the match
  reports -1 for both ends, in every language, and the oracle harness maps
  pcre2's PCRE2_UNSET to -1 when comparing. Subjects are consequently
  capped at 2^31 - 1 bytes, which we accept as a documented limit. Subjects
  are byte arrays in every language; string conveniences arrive with UTF
  mode in wave 3.
- Analysis accessors, available right after compilation with no matching:
  `complexityClass()`, `worstCaseCost(subjectLen, matchConfig)`,
  `worstCaseStackEntries(subjectLen, matchConfig)`, and
  `worstCaseMemory(subjectLen, matchConfig)`, as defined in section 5.
  `complexityClass` alone takes no configuration, because the class is
  fixed at compilation: memoization is only legal on Pike-eligible
  patterns and changes the constants, never the class. Each returns a finite number, an
  explicit `ExceedsBudget` status, or BadInput for a matchConfig the
  pattern is not eligible for; a saturated counter is never presented
  as a finite bound, and `ExceedsBudget` also covers a bound no runtime
  limit could accept, a memory bound above the section 3 ceiling or a
  stack bound above its derived entry cap, so any number these
  accessors return is one the caller can actually pass as a limit. Stack is counted in entries of the engine's backtrack
  stack, memory in IR bytes summed over every per-call scratch array
  (backtrack stack, thread lists, capture slots, lookaround frames, the
  ovector and match-result storage, memo table when enabled) using the
  fixed IR scalar sizes; both are portable,
  engine-defined units. The accessors take the match configuration that
  affects resources (today, whether the memo table is enabled), so the
  reported bound always describes the configuration that will actually run,
  memo bitmap included exactly when it is on. Beyond that configuration
  argument, the bounds are conservative over everything else a caller can
  vary at match time: they hold for every combination of match-time
  options and for every start offset, with `subjectLen` always meaning
  the full subject length in bytes. It cannot mean bytes from the start
  offset onward: a pcre2 start offset does not shorten the subject,
  because lookbehinds and word-boundary tests may inspect bytes before
  it, so the only safe reading, and the one the accessors are specified
  and proved against, is the whole subject. A caller who wants a tighter
  number for a genuine sub-search passes the shorter subject itself.
  What a given host actually
  allocates per IR byte is documented per target but informational, since
  host object layout is not ours to guarantee. Applications use these to
  refuse or budget a pattern before ever running it.
- Hard runtime limits on every match call: cost limit, stack-entry limit,
  and scratch-memory limit, in the same units as the accessors, with a
  distinct `ResourceExceeded` result. For realtime callers each backend
  also offers a reusable match context: a workspace preallocated once from
  the compiled pattern's bounds, the caller's limits, and a declared
  maximum subject length, so that match calls made with it perform no
  allocation at all; a subject longer than the declared maximum is
  rejected as BadInput instead of triggering a resize. What "no
  allocation" means is stated per target, at the strongest each backend's
  representation admits, and each claim is proved by that backend's own
  instrumentation: in Go a context match performs literally zero heap
  allocations, success and failure paths alike, held to
  `testing.AllocsPerRun`; in JavaScript it constructs no backing store —
  no array, no typed array, no growth — held by counting constructors,
  while the printed value semantics may still create bounded short-lived
  records at call boundaries where Go copies stack values. Driving those
  records to zero as well is printer work, tracked as such rather than
  promised early. The match
  configuration is baked in the same way: a context is created for one
  configuration (memoization on or off) and one set of limits, and a
  call through it may lower the cost and stack limits but never raise
  them or switch configuration; asking for either is rejected as
  BadInput rather than answered with a resize, which is what keeps the
  no-allocation promise unconditional. Memory has no per-call role on a
  context at all: a context call allocates nothing, its resident
  scratch capacity is the creation reservation, a constant of the
  declared maximum rather than of the subject a given call matches, so
  the memory question is asked and answered once, at creation.
  Concretely, the context match entry point takes only cost and stack
  limits, so there is no memory field to silently ignore; in the formal
  model, `Exec` on a context configuration pins the memory component to
  the creation reservation and anything else is BadInput. The ovector and
  match result live in context-owned storage included in that sizing and
  stay valid until the next match call on the same context, with a
  documented copy-out helper for callers who need them longer; the
  helper runs outside any match call and costs exactly the copied size,
  so the match bounds owe it nothing. A context is deliberately not part
  of `matchConfig`: the per-match cost and stack bounds are functions of
  the subject length and matchConfig alone, and they hold for
  context-backed and plain calls alike, because preallocation changes
  where the memory comes from, not what work a match does, and
  per-match reset work stays charged to each match under the same
  certificate. The memory number is one function asked two different
  questions: `worstCaseMemory(n, matchConfig)` is the peak a plain call
  on an n-byte subject allocates, while a context call's resident
  memory is the constant `worstCaseMemory(declaredMax, matchConfig)`
  reserved at creation, whatever subject a given call matches. Creation has a
  derived bound rather than a certificate of its own: it reserves
  exactly `worstCaseMemory(declaredMax, matchConfig)` IR bytes against
  the memory limit and charges the zeroing of those bytes as cost units,
  so a caller can compute from the accessors it already has whether
  creation fits the engine's limits; actually obtaining the memory
  remains subject to the host-allocation caveat below. The Lean semantics accounts the same split, so
  context-backed calls have well-defined bounds and ResourceExceeded
  behavior rather than inherited ones. For context-backed calls, context creation is
  then the only point where host memory is requested, and a failure there
  surfaces through the target's normal error convention instead of inside
  a match. A plain call allocates its scratch at match start under the
  same pre-charge rule, so ResourceExceeded still precedes any
  over-budget attempt, but a within-budget request can also fail if the
  host itself is out of memory, and that surfaces however the host
  surfaces allocation failure, fatal in Go's runtime, an exception in
  JS, never a corrupted result. Genuine host memory exhaustion is the
  one failure mode that stays outside our deterministic model, the docs
  say so rather than pretend otherwise, and taking it off the table
  entirely is exactly what the preallocated context is for. A supplied cost limit must be a
  finite, non-negative integer no larger than the counter saturation point
  of 2^53 - 1; the scratch-memory limit is further capped by the portable
  allocation ceiling of 2^31 - 1 IR bytes that the IR semantics fixes
  for array sizes (section 3), and the stack-entry limit by that
  ceiling divided by the backtrack entry's IR size, since no target can
  honor more. Anything
  else (a fractional or NaN number in JavaScript, an out-of-range uint64 in
  Go) is rejected as BadInput rather than silently clamped, so enforcement
  is identical everywhere. Reservations are charged against the memory
  limit before any allocation happens, so `ResourceExceeded` always
  precedes an allocation attempt beyond budget rather than reporting one
  after the fact. Defaults are generous
  but finite, in the spirit of pcre2's match_limit and depth_limit. The
  `find all` iterator is sugar over repeated match calls under a pinned
  advance rule, the same loop the pcre2 documentation demonstrates,
  spelled out here because "the standard rule" hides real subtlety.
  After a non-empty match the next attempt starts at the match's end
  offset. After an empty match the engine retries at the same offset
  with NOTEMPTY_ATSTART and ANCHORED added as an iterator-owned overlay
  on top of the caller's base options, which stay untouched for every
  attempt; if that retry finds nothing, iteration ends when the offset
  already sits at the end of the subject, and otherwise the position
  advances by one character (one byte until UTF mode, a whole UTF-8
  sequence in it, and past a full CR LF pair when the newline
  convention treats CRLF as one newline) and scanning resumes with the
  overlay dropped, back to the base options alone; a base option the
  caller supplied is never cleared. When wave 3's \K makes a match end at or before
  the previous attempt's start, the same one-character advance applies
  from that start, so the iterator always makes progress. Every attempt,
  the empty-match retry included, is its own separately budgeted call
  under these same limits; there is no hidden aggregate work inside one
  call, and a caller who wants a total budget over a whole scan enforces
  it by counting attempts, which the per-call bounds make computable. An
  attempt that returns ResourceExceeded surfaces through the iterator,
  which stops without advancing and keeps the pending attempt's phase
  and temporary options in its state, so resumption re-runs exactly the
  attempt that failed, empty-match retry included, never a fresh
  unrestricted attempt that could emit the same empty match twice. The
  caller can thus resume deterministically from the same position with
  raised limits when the iterator runs on plain match calls; through a
  context, limits cannot rise, so recovery there means a fresh context
  created with higher cost or stack limits (the declared maximum, and
  with it the memory reservation, only needs to grow if the subject
  outgrew it), or abandoning the scan. That handoff is defined, not
  implied: the iterator's scan state is a small plain value, the next
  offset plus the attempt phase and its overlay, exposed by the
  iterator and accepted by the find-all constructor, so a caller
  rebinds a new iterator on the new context to exactly the pending
  attempt instead of restarting the scan. The constructor validates
  what it is handed rather than trusting it: the state also carries the
  compiled pattern's identity, the base match options, the matchConfig,
  and the subject length, and any mismatch with the new iterator's
  arguments, or an offset, phase, or overlay the advance rule could
  never have produced, is BadInput. The subject bytes themselves are
  the caller's to keep identical; handing equal-length different bytes
  yields a well-defined scan over those bytes, never memory-unsafe
  behavior, since every access is checked anyway.
  The rule is exercised by the conformance corpus and the oracle
  comparison, not just described here.

Substitution/replace is a thin wave-3 wrapper; it does not affect the core.

## 3. The intermediate representation (TIR)

TIR ("trusted IR") is the load-bearing design decision, so it gets the most
detail. It is a small first-order imperative language with structured control
flow, serialized as JSON. It is designed to be boring: every construct must
have an obvious translation to Go, an obvious translation to JavaScript, an
obvious denotational reading in Lean, and nothing else.

### 3.1 Design rules

- No recursion. The call graph must be acyclic; the validator rejects
  anything else. Everything that is naturally recursive (regex parsing, tree
  walks, backtracking) uses an explicit stack held in an array. This is what
  makes "max stack usage" a theorem instead of a hope: host-language stack
  consumption of any generated function is a static constant, and the only
  growing stacks are engine-managed arrays with checked capacity.
- No exceptions, no panics in TIR programs themselves: functions that can
  fail return a result value. The only indexed reads and writes go through
  checked accessors, and their semantics is total: a failed bounds check
  is a defined trap that stops the engine call, never undefined behavior.
  On the proved surface the Lean proofs discharge every check, so the
  trap is provably unreachable there; on code the proofs do not yet cover
  (a milestone still in flight, or features behind allowUnproved) it is
  only tested unreachable, and we say so. The backends must realize the
  trap explicitly rather than assume it away: in Go the native
  bounds-check panic is the trap, documented as the engine-bug channel;
  in JavaScript, where an out-of-range typed array read silently yields
  undefined instead of failing, the printer emits the check itself and
  throws. The no-panic promise is therefore scoped honestly:
  theorem-backed where the proofs cover, fail-fast on engine bugs
  elsewhere, silent corruption nowhere.
- First-order data only: fixed-size integers, bools, byte arrays, growable
  arrays (`vec<T>`), structs, and C-like enums used as tags. No closures, no
  interfaces, no generics in the IR itself (the DSL can be generic; it
  monomorphizes when emitting).
- Integer types are `u8`, `i32`, `u32`, and one special `counter` type.
  We deliberately avoid 64-bit integers because JavaScript numbers cannot
  represent them exactly and BigInt is too slow for a hot loop. `counter` is
  an unsigned saturating integer with saturation point 2^53 - 1, mapped to
  `uint64` with an explicit saturation check in Go and to a plain number in
  JS. Every counter operation the IR offers (addition, multiplication, and
  whatever else closed-form bound evaluation needs) is pre-checked: the
  operands are tested against the saturation point before the arithmetic
  runs, identically in TIR, Lean, Go, and JS. The pre-check is what keeps
  JS honest, since an unchecked double product would round above 2^53
  before any after-the-fact comparison could notice. All step and cost
  accounting and all bound evaluation use `counter`, so every language
  computes identical values. Arithmetic on i32/u32 is wrapping two's
  complement, which Go gives natively and JS gives through `| 0` and
  `>>> 0` (with `Math.imul` for products, see section 7).
- Control flow is `if`/`else`, `while`, `switch` on enum tags, `break`,
  `continue`, and early `return`. Every `while` loop carries a declared
  variant (a `counter` expression that strictly decreases, or a fuel bound);
  the Lean side uses it for termination, the backends ignore it.
- Mutation is allowed on locals, struct fields, and array elements.
  Parameters are passed by value, except explicit `inout` parameters,
  which must be pairwise disjoint places at every call site: not merely
  distinct names but non-overlapping access paths, so a struct and one of
  its own fields can never travel as two `inout` arguments, and an
  `inout` place cannot overlap any other argument either. The validator
  checks the root variable and projection path of every argument pair.
  Disjointness alone is still not enough to kill aliasing,
  because copying a struct that contains a vec would silently share the
  backing storage in Go and the object in JS; so heap-backed values (vec,
  bytes, and any struct containing them) are linear in TIR: they cannot be
  copied by assignment or passed by value at all, only moved, passed
  `inout`, or duplicated through an explicit deep-copy intrinsic, and the
  validator enforces it. The discipline covers every access path, not just
  whole variables: a heap-backed struct field or vec element is read and
  written in place through its projection, never extracted by value, and
  moving one out of its container goes through an explicit take-or-swap
  intrinsic that leaves an empty value behind. With that rule each
  heap-backed value has exactly
  one live name, there is genuinely no aliasing to reason about in Lean,
  and the backends can use their native reference types without the model
  lying. The one escape from linearity is deliberate and one-way: a
  `freeze` intrinsic turns a heap-backed value permanently immutable,
  after which it may be passed and shared freely as a read-only `in`
  parameter, because aliasing an object nobody can write to is invisible
  to the semantics. Compiled patterns are frozen at the end of
  compilation, which is what lets one compiled regex serve any number of
  simultaneous match calls (section 7) while every mutable scratch value
  stays linear; the validator rejects any write through a frozen path.
  Go receives `inout` as pointers; JS wraps scalars in a one-field
  cell and passes objects directly.

### 3.2 Type and expression inventory

```
+-----------+-------------------+---------------------+--------------------+
| TIR       | Go                | JavaScript          | Lean               |
+-----------+-------------------+---------------------+--------------------+
| bool      | bool              | boolean             | Bool               |
| u8        | byte              | number (0..255)     | UInt8              |
| i32 / u32 | int32 / uint32    | number with |0 >>>0 | Int32 / UInt32     |
| counter   | uint64, saturated | number, saturated   | Nat, saturated     |
| bytes     | []byte            | Uint8Array          | ByteArray          |
| vec<T>    | []T               | Array / typed array | Array T            |
| struct    | struct            | class or object     | structure          |
| enum tag  | typed int consts  | int consts          | inductive          |
+-----------+-------------------+---------------------+--------------------+
```

Expressions come from a closed operator inventory, never "the usual"
ones, because Go and JavaScript disagree exactly in the corners a casual
list leaves open: integer division, remainder, shift counts, operand
evaluation order, short-circuiting. The normative TIR specification
written in M2 pins every operator's result on every input: wrapping add,
subtract, and multiply on i32/u32; division and remainder only in
checked forms that return a result for a zero divisor and truncate
toward zero; shifts only with a validator-enforced in-range count;
explicit casts between the integer types with defined truncation, plus
the counter pre-checks above; strict left-to-right evaluation
everywhere; boolean and/or defined as conditionals so short-circuiting
is explicit; and the failure ordering of checked operations. Beyond
operators there is array length, checked indexing, struct field access,
and calls. Nothing higher order. `vec` supports push, pop, truncate, and reserve; capacity
growth is amortized and bounded by a declared maximum so memory is
predictable too. Array lengths and capacities are u32 values under one inclusive
portable ceiling of 2^31 - 1 IR bytes, fixed by the IR semantics
because it is what every target can represent and address; each
`vec<T>` derives its maximum element capacity as that ceiling divided
by the element's IR size, rounded down, and growth respects the
ceiling for old and new buffer together, since section 5 counts both
during a resize. The resource limits of section 2.4 inherit the same
ceiling.

### 3.3 Serialization and identity

The artifact is one JSON file, `engine.tir.json`, containing type
declarations, constants (including generated tables), and functions. It is
emitted deterministically: stable ordering, no floats, no timestamps. Its
SHA-256 is the identity that ties everything together: the Lean build records
the hash of the artifact it decoded, generated Go/JS files embed it in a
header comment and a constant, and CI refuses to ship artifacts whose hashes
disagree. That is the answer to the
objective's requirement that "the code in the intermediate representation
verifies the proof": the proof is checked against this exact file.

To be precise about what that buys, because precision is the point of the
exercise: the theorems cover the IR artifact under the TIR semantics. The
translation from TIR to Go and JS is a separate link in the chain, unproved
in the first releases, kept deliberately small, and covered by bit-for-bit
cross-implementation testing (section 8). We never describe the generated
libraries as formally verified; we describe them as generated from a
formally verified artifact by a printer that is tested, and section 10 lists
verified-backend work as future hardening.

### 3.4 The authoring DSL

Writing JSON by hand would be miserable, so the engine is written in Python
against a builder API (`Fn`, `Struct`, `While`, `If`, expression operators
overloaded on typed handles). The DSL only builds and validates IR; it has no
execution semantics of its own. The validator enforces typing, acyclic calls,
`inout` distinctness, loop variants, and the vec capacity discipline, and
then the reference interpreter can run the engine directly for tests. The
DSL is untrusted: if it has a bug, either the validator, the Lean proofs, or
differential testing catches the damage downstream.

## 4. The engine, as written in TIR

### 4.1 Pattern parser

A single left-to-right pass with an explicit stack of open groups, producing
an AST stored in a flat arena (arrays of nodes indexed by u32, no pointers).
Nesting depth is limited (default 250, like pcre2's parse depth) so the
parser's stack is bounded by configuration, not by input. Error reporting
carries pcre2-compatible error codes and byte offsets, checked by the
differential tests from the start; only the message wording is ours.
The extended (/x) whitespace rules, \Q...\E, and inline options are handled
here, so the AST is already normalized: options are resolved per node, case
folding decisions are made explicit, and {m,n} bounds are validated.

### 4.2 Bytecode compiler

The AST is compiled to a bytecode program, one instruction array plus side
tables (class bitmaps for bytes, range tables, group name table). The
instruction set is deliberately close to the classic Pike/Thompson VM with
PCRE extensions:

```
+----------------+---------------------------------------------------------+
| Instruction    | Meaning                                                 |
+----------------+---------------------------------------------------------+
| Char b         | match one byte                                          |
| Class idx      | match one byte against class table entry                |
| AnyNoNL / Any  | dot, with and without DOTALL                            |
| Split a, b     | try a first, then b (order encodes greediness)          |
| Jump a         | unconditional                                           |
| Save slot      | record current position in ovector slot                 |
| AssertBOL/EOL, | anchors and word boundaries, multiline-aware            |
| AssertWB, ...  |                                                         |
| RepZero r      | zero repetition r's counter                             |
| RepLoop r      | read the counter, decide whether to go round again      |
| RepEnter r     | remember where this iteration began                     |
| RepNext r      | count, then jump back to the head or fall out           |
| BackRef k      | wave 2: match text of group k again                     |
| LookStart/End  | wave 2: lookaround sub-match with direction and sign    |
| AtomicStart/   | wave 2: cut backtracking on exit                        |
| AtomicEnd      |                                                         |
| Accept / Fail  | end states                                              |
+----------------+---------------------------------------------------------+
```

Compilation of quantifiers, alternation, and groups follows the standard
constructions; possessive quantifiers desugar to atomic groups; UNGREEDY
just swaps Split arms. A counted repetition is lowered to star form first,
under the caps section 4.3 describes; what survives the lowering is the
four Rep opcodes of a pure star, and the fallback keeps the counter. The
compiler also runs the analyses of section 5 and stores their results in
the compiled object.

### 4.3 Two matchers

The engine embeds two matchers over the same bytecode. Compilation fixes,
per pattern, the default execution path (Pike VM when eligible, the
backtracking VM otherwise) and the set of legal match configurations; the
only runtime choice a caller has is the memoized-backtracking option below,
legal exactly on Pike-eligible patterns, and the analysis accessors take
that same configuration argument, so the bound a caller reads always
matches the path that will run.

The Pike VM is the linear engine: lockstep breadth-first simulation with
explicit priority mechanics, which we spell out because the exact-semantics
claim lives or dies here. Threads are kept in a priority-ordered list; the
epsilon closure at each position is expanded depth-first in split order, so
list order is exactly PCRE's backtracking preference order; the per-position
visited set is keyed by pc, and when two threads reach the same pc the
first (higher-priority) one wins and keeps its capture slots; when a thread
reaches Accept, it records its captures and kills every lower-priority
thread, while higher-priority threads keep running and may overwrite it.
Capture slots use a pooled copy-on-write scheme that stays inside TIR's
linear ownership rules: the match state owns one flat slot pool (a single
array of slot entries plus a refcount array and a free list), and each
thread holds only an integer handle into it, so "sharing" a capture set
across a fork is a scalar handle copy plus a refcount bump, never an
aliased heap value. A Save through a handle with refcount above one first
takes a fresh block from the free list and copies the slots, charged per
slot copied under the section 5 cost model. Slot count and live-thread
count are compile-time constants of the pattern, which bounds the pool
size for context preallocation, folds the copying into the linear
coefficient, and puts the pool squarely inside the section 5 memory
accounting; the representation is part of what the Layer R and I proofs
cover rather than an implementation liberty.
Keying the visited set by pc alone is only sound if pc determines the
thread's future behavior, so programs routed to the Pike VM must be
state-free. There is one bytecode and both matchers read it. What makes a
program state-free is that every repetition left in it is a pure star —
minimum zero, no maximum — because then the four Rep opcodes never consult
their counter to decide anything, and the Pike VM may read them as the
epsilon forks their control flow amounts to: RepZero and RepEnter as plain
epsilons, RepLoop and RepNext as a fork between one more iteration and the
exit, ordered by greediness.

A counted repetition that is not already an optional, a singleton or a pure
star is therefore *lowered* to star form at compilation:

    x+       ->  x x*
    x{m,}    ->  x .. x x*             (m copies)
    x{m,n}   ->  x .. x (x (..)?)?     (m copies, then n-m nested optionals)

Every copy of a body saves into the original group's slots, so a group
repeated three times is still one group reported once. The optionals nest
so that the k-th copy's presence is decided before the (k+1)-th's, which is
what makes the count preference pcre2's. The lowering is recursive and
all-or-nothing: one retained counter is enough to make a program ineligible,
so a pattern is lowered whole or not at all.

Two things keep it from applying everywhere. A star whose body can complete
an iteration without consuming a byte stays ineligible however it is
spelled — that is the `(a?)*` capture-preference problem, and lowering
`(?:a?)+` to `(?:a?)(?:a?)*` leaves the same nullable body behind — and `\R`
consumes a variable number of bytes, so a pattern that emits one is left in
counter form until `\R` compiles as an alternation. The pre-check reads both
off the tree the way the emitter will walk it, which is why a `{0}` body is
skipped for either: nothing under it is compiled, so nothing under it can
route the pattern anywhere. Those are the two
semantic carve-outs of section 2.1, decided by a pre-check on the AST before
anything is emitted; the third is size. The lowered form is measured against
the compiler's storage caps by a dry run that computes closed-form counts
rather than expanding anything, and a candidate that does not fit leaves the
whole pattern in counter form on the backtracking matcher. Oversize is a
documented carve-out, never a compile error: a pattern whose ordinary
counter form compiles today still compiles.

Eligibility itself is decided by one predicate over the emitted program, and
the lowering never gets a vote in it: the pre-check chooses whether to lower,
and `pike_ok` alone says whether the result may run in lockstep.

That discipline gives leftmost, priority-ordered,
greedy-by-split-order results with O(program_size * subject_len) cost and
O(program_size) threads. The claim that this reproduces PCRE backtracking
exactly on the wave 1 subset is a proof obligation (the section 6
refinement theorem for the Pike configuration) and a standing test
obligation (section 8), not an
assumption. The accurate statement of the wave 1 guarantee, carve-outs
included: a wave 1 pattern that emits no `\R`, has no star whose body can
finish emptily, and whose lowered form is inside the caps runs on the Pike VM,
which in practice is nearly all of them. Which matcher runs is not the class,
though, and section 5 is where the class comes from: it is read off the
shape of the certified cost bound, whatever the path, so `a{2}` and `\R`
classify linear on the backtracking matcher because their certified bounds
are linear. The carve-outs are a documented part of the contract, not
hidden constants.

The backtracking VM is the complete engine: depth-first exploration with an
explicit heap-allocated stack of (pc, position, plus undo entries for
captures and counters), never host recursion. It handles backreferences,
lookaround, and atomic groups. Work is metered with the cost model of
section 5 (one unit per instruction visit, plus one per byte compared by a
backreference) against the caller's cost limit, and every push checks the
stack limit, so the worst case is a clean `ResourceExceeded`, never a blown
host stack. The backtracking VM also has a memoized mode (a visited bitmap
over pc * position, as in Rust's bounded backtracker) whose honest purpose
is performance, not features: pruning on (pc, position) is only sound when
that pair determines the rest of the search, which is exactly the
state-free property Pike-eligible programs already have, so memoized
backtracking applies to the same patterns Pike handles and must return the
same results (a proof obligation). Its value is better constants than the
Pike VM on short subjects, at a memory cost the section 5 accounting
includes; it is selected through the API's matchConfig argument, rejected as
BadInput on patterns that are not Pike-eligible. Eligibility is the
condition there, and it is not the linear class: a pattern can classify
linear and still be refused the memoized path, `\R` being the standing
example.

Both matchers implement the empty-match rule (a quantifier iteration that
consumes nothing does not loop) and the section 2.4 find-all advance
rule.
On Pike-eligible patterns, which is wave 1 less the three carve-outs of
section 2.1, the two
matchers must agree exactly whenever both run under sufficient budgets
(section 6 states this precisely). The public API never routes such a
pattern to the plain backtracking matcher; that side of the comparison
runs through an internal testing entry point kept out of the public
surface, so ordinary backtracking on a Pike-eligible pattern is a test
and proof configuration, not a requestable one. The redundancy is a
test asset (section 8) and a proof asset (section 6).

### 4.4 Unicode

Until wave 3 the engine is byte-oriented, exactly like pcre2 without
PCRE2_UTF: subjects are bytes, offsets are byte offsets, case folding is
ASCII. Wave 3 adds UTF-8 validation, decoding in the matchers, simple case
folding from a generated table, and \p classes from generated range tables.
The Python tool generates those tables into IR constants from a pinned
Unicode Character Database version, chosen to match the one the pinned
pcre2 build ships with and recorded alongside the pcre2 pin, so backends
and proofs see plain data and a Unicode upgrade is the same kind of
explicit compatibility change as a pcre2 upgrade. UTF mode validates the
pattern too: an ill-formed UTF-8 pattern is a compile error with a byte
offset and pcre2-compatible code, and it extends the BadInput outcome of
section 6 to invalid UTF-8 subjects and to start offsets that land inside
a character, compared in the oracle against pcre2's UTF error family. The
JS string overloads reject ill-formed strings (unpaired surrogates) before
encoding rather than letting TextEncoder silently substitute U+FFFD, so Go
and JS can never end up compiling or matching different bytes for what a
caller believed was the same input. Until then, Uint8Array is the
canonical subject type in JavaScript, same as []byte in Go, because a JS
string cannot carry arbitrary bytes. With wave 3's UTF mode the JS wrapper
gains string overloads (UTF-8 encoded with TextEncoder, byte offsets
translatable back to string indices on demand); the core stays byte-based so
all languages report identical offsets.

## 5. Resource analysis

This is a first-class feature, not an afterthought, because the objective is
realtime use. All results are computed at compile time from the bytecode and
exposed on the compiled pattern.

The cost model comes first, because one model must be shared by the
analyzer, both matchers, and the Lean fuel accounting, or the numbers mean
nothing. One cost unit is charged per instruction visit; a backreference
additionally charges one unit per byte compared; wave 3 UTF-8 decoding
charges per byte examined; and scratch management is charged too, one unit
per IR byte initialized, zeroed, or copied when arrays are reserved or
grown, memo bitmap included, because setup work is real work and a
realtime bound that excluded it would be a bound on the wrong thing. The
memory bound of this section makes those management charges finite and
lets the analyzer fold them into `worstCaseCost`. Class lookups are O(1)
table reads. Enforcement is pre-charge: every charge is compared against
the remaining budget (charge > limit - consumed fails) before the
saturating addition, through the same generated helpers in every target
and the same definition in Lean, so a run can never idle at the saturation
cap doing uncounted work. With that model, "steps" below always means cost
units, and a proved fuel bound in Lean is a bound proportional to the
total work of the match call in the generated code.

Stack bound. The analyzer does not assert one clever formula; it computes a
per-pattern closed form by per-opcode accounting: each opcode has a proved
rule for the maximum stack entries it can push per visit and for what makes
those entries poppable, and the analyzer composes those rules over the
program structure. That structure is not rediscovered from the flat
bytecode, whose control-flow graph is cyclic and unhelpful: the compiler
has the AST in hand when it flattens, so it also emits a region table
mapping each source construct (quantifier body, alternation arm,
lookaround, group) to its instruction range and its place in the nesting
tree, stored in the compiled pattern. The compiled pattern owns that table, and the analyzer walks it; its
result is not a bare number but a bound certificate: one price per
region, in the same order, so that the tree exists once and nothing
carries a second copy of it to disagree with. There is one certificate per
internal configuration of the pattern (section 6's Config domain modulo
context parameters), covering the public matchConfig values and the
test-only backtracking path alike, so the memoized path's memo-table
memory and setup cost are priced by its own certificate. Internally,
every bound function in this section takes that internal configuration;
the public accessors are the projection of the same lookup onto the
legal matchConfig values, and the test harness reads the internal ones
directly. A deliberately small checker
validates certificates, defined once and existing twice, in TIR where
compilation runs it before trusting any bound, and in Lean where Layer A
proves it sound, so any accepted certificate really bounds the run.
Proving a checker is far less work than proving the analyzer's search,
and it is what keeps the M5 analyzer mechanically connectable to the
M6/M7 proofs instead of drifting into a plausibility argument. The rules
the checker applies — every opcode's charge, every region kind's
composition, and what a whole call pays on top of the tree — are written
down in BOUNDS.md, which is normative for them the way TIR-SPEC.md is for
the IR: an analyzer may only claim what that document lets a checker
verify. For plain
quantified patterns the empty-match rule makes
re-entries consume input and the composed bound comes out linear in the
subject length n; bounded lookbehinds contribute factors proportional to
their width at each attempted position; counted repetitions contribute their
declared bounds. The result is a polynomial in n with pattern-derived
coefficients (width of lookarounds, {m,n} bounds, program size), evaluated
by `worstCaseStackEntries(n, matchConfig)` in counter arithmetic. Soundness of every
per-opcode rule, and of the composition, is a Layer A proof obligation; no
bound shape is claimed that the accounting cannot derive.

Memory bound. The same accounting yields the total scratch bound: every
per-call array (backtrack stack, thread lists, capture slots, lookaround
frames, the ovector and match-result storage, the memo table when
enabled) has an entry size fixed by the IR
layout and a per-pattern entry-count bound, and
`worstCaseMemory(n, matchConfig)` is their sum in IR bytes. Memory here means peak allocated capacity, not live
entries: growing a vector momentarily holds the old and the new buffer, so
growth charges both against the budget before allocating, and both
backends follow the same deterministic growth schedule so the peak is the
same everywhere. Since the subject length is known when a match starts,
the engine sizes its arrays from the computed bounds up front whenever
they fit the caller's limit, which makes growth the exception rather than
the rule. For context-backed calls memory is a creation-time affair, as
section 2.4 spells out: resident capacity equals the reservation for
the declared maximum whatever a given call's subject length, which is
exactly the number a realtime caller wants pinned once. This is the number a realtime application sizes its memory
budget with, and the matchers enforce the corresponding limit across all
of those arrays together, not just the backtrack stack.

Cost bound and classification. The class is a property of the certificate,
not of matcher selection. BOUNDS.md section 6 is the normative rule and it
reads the shape of the certified cost bound for the path compilation
selected: base one and no power above the first is `linear`, everything
else is `notProvenLinear`. For patterns routed to the Pike VM that bound is
`cost <= c * (n + 1)` with c derived from program size, so those patterns
classify linear as a matter of course. They are not the only ones, and it
would be wrong to define the class that way: `a{2}` and `\R` run on the
backtracking matcher and classify linear too, because the bound their
certificate carries is linear. The linear claim is the one applications
gate on, and it is the one we make soundness theorems about.
For patterns needing the backtracking VM, the analyzer always
produces a conservative closed-form cost bound by structural analysis
(choice points, quantifier nesting, backreference lengths), and additionally
runs a ReDoS-style ambiguity analysis to label the pattern
polynomial-looking or exponential-looking. Those labels are advisory:
captures, ordered alternation, assertions, and backreferences make exact
degree computation on full PCRE a research problem, so the honest contract
is `linear` (proved) versus `notProvenLinear(bound)` (conservative closed
form, possibly exponential in form). The bound may overestimate, never
underestimate. `worstCaseCost(n, matchConfig)` evaluates the closed form
and returns
either a finite counter value or `ExceedsBudget` when the arithmetic would
saturate; a saturated value is never reported as a finite maximum, because
"at least 2^53" is not a budget anyone can plan with. The stack and
memory projections apply the same rule at their own caps: a bound above
the section 3 byte ceiling, or above the derived stack-entry cap, comes
back as `ExceedsBudget` rather than as a number no valid limit could
match.

These numbers plus the hard runtime limits give applications the full
contract: check the bounds after compile, decide with concrete numbers,
pick limits, and every match call finishes within them or returns
`ResourceExceeded` deterministically, with the single host-memory
exception of section 2.4: a within-budget scratch request on a plain
call can still hit host exhaustion, and only a context-backed call
removes that. An application that wants pcre2's
exact answer for a pattern the analyzer cannot prove linear can either
accept the conservative bound and budget for it, or refuse the pattern.

One wording rule we hold ourselves to wherever the word realtime
appears: what the engine guarantees is deterministically bounded work
per call, every instruction charged and every scratch byte accounted,
and allocation-free matching when a context is used. It does not turn Go or a browser into a hard-realtime system;
garbage collection pauses, JIT warmup, and scheduling belong to the host
runtime and sit outside our model. The documentation therefore says
"bounded and allocation-free" and leaves latency budgets to the
application's judgment of its own runtime.

## 6. The Lean proofs

Lean 4 with lake; dependency on batteries only (mathlib avoided to keep CI
fast, revisit if order theory for the analysis proofs demands it). Prior art
we will lean on for design, not code: Warblre's mechanized ECMAScript regex
semantics (Coq) for how to specify backtracking-priority matching, and the
verified-derivatives literature for the linear engine.

The Lean project has four layers, and this layering is also the proof
staging plan:

Layer S, the specification, in two parts, because one function cannot
honestly describe both what PCRE means and when our matchers give up.
The first part is the pattern semantics: PCRE pattern AST as inductive
types and
`Matches : Pattern -> Subject -> StartPos -> MatchOptions -> MatchAnswer`,
a priority-ordered big-step search whose answer is Found with captures,
NotFound, or BadInput (out-of-range start offsets and subjects beyond
the section 2.4 size cap from wave 1 on, extending to invalid UTF-8
subjects and mid-character offsets in wave 3)
and nothing else, because what a pattern means does not depend on which
of our matchers runs it. Match-time options are an explicit argument,
never ambient state: NOTEMPTY or ANCHORED change the answer itself, so
they belong to the semantics, and every theorem below quantifies over
them. Totality is earned, not assumed: `Matches` is
defined through a fuel parameter with a proved stability theorem, that
beyond a computable sufficient fuel the answer no longer changes, and
`Matches` is that stable answer. The second part is the execution
semantics: one operational function
`Exec : Config -> Pattern -> Subject -> StartPos -> MatchOptions -> Limits
-> MatchOutcome`
where `Config` is the internal configuration domain, deliberately wider
than what the public API exposes: Pike, backtracking, memoized
backtracking, each with or without a preallocated context and its
declared sizes. Wider in two ways. It contains configurations a pattern
is not eligible for, which `Exec` maps to a deterministic BadInput
after validating the request against the eligibility fixed at
compilation, so the public API's rejection is stated and proved rather
than assumed. And it contains ordinary backtracking on Pike-eligible
patterns, which the public wrapper never requests (compilation picks
the path, and the only public choice is memoization) but which the
agreement corollary and the section 8 cross-matcher tests quantify
over, reached through the internal testing entry point of section 4.3. `Limits` carries the
cost, stack-entry, and scratch-memory budgets in the section 5 model,
and `MatchOutcome` adds ResourceExceeded to the answers above. `Exec`
returns BadInput exactly when `Matches` does, plus the cases that only
exist at execution: limits that break the section 2.4 validity rules
and, on a context configuration, a subject longer than the declared
maximum or a call asking to raise limits or switch configuration, all
decided deterministically before any engine work and all inside the
refinement and oracle claims. Resource
behavior is defined per configuration because the matchers meter work
differently and no single limit story is true of all of them.
Configurations with a preallocated context do not appear from nowhere
either: the semantics includes a `CreateCtx` step, taking the compiled
pattern's bounds, the requested match configuration, the caller's
limits, and the declared maximum subject length, whose one-time
reservation and zeroing charges are checked against those limits and
which returns a valid `Config`, BadInput for parameters that fail the
section 2.4 validity rules, or ResourceExceeded; Layer R implements it and Layer I refines it, so
context creation has the same proved limit behavior as matching, while
genuine host allocation failure stays the one outcome outside the
model, as section 2.4 states. Between them, `Exec` and `CreateCtx`
account for every observable ResourceExceeded condition of the public
API. Three theorem families tie the parts together,
each stated per configuration: refinement (whenever `Exec cfg` returns
Found or NotFound, that answer equals `Matches`), monotonicity (raising
limits never changes a Found or NotFound outcome, it can only turn
ResourceExceeded into one of them), and sufficiency (with every limit at
or above the analyzer's bound for that configuration, ResourceExceeded
cannot occur). For context configurations, monotonicity and sufficiency
range only over the valid calls the context admits, cost and stack
limits at or below the creation limits, memory having no per-call role
there per section 2.4, and sufficiency gains a creation-side companion,
conditional on creation succeeding: once `CreateCtx` has accepted the
one-time reservation and zeroing charges within the creation limits, a
context whose limits sit at or above the analyzer's per-match bounds
for its configuration and declared maximum subject length never returns
ResourceExceeded on a call whose per-call limits also stay at or above
those bounds; a caller who deliberately lowers a limit below the bound
opts back into ResourceExceeded. Creation work is priced separately
from match work, and headroom is bought at creation, not per call. Cross-matcher agreement stops being a separate
obligation: for a Pike-eligible pattern, the Pike configuration and the
internal plain-backtracking configuration each refine `Matches` under
sufficient budgets, hence agree with each other, and the same argument
covers the memoized configuration. This layer is the trusted
definition of what "correct PCRE" means, so it stays small and readable,
written for auditability with the pcre2 man pages as the informal reference
and the pinned build as arbiter. Options are parameters of the semantics.
One caveat is inherent and worth stating wherever we state coverage: no
theorem can relate `Matches` to the pinned C library itself, so the
spec-to-pcre2 correspondence rests on the spec's auditability and on
differential testing of everything downstream of it, feature by feature.
That is the standard trusted-spec caveat of any verification effort, and
release notes carry it verbatim.

Layer R, the reference engine. Executable Lean functions covering the whole
post-parse path, structured like the real engine: `R.compile` from spec AST
to bytecode, and `R.run` executing that bytecode under a configuration
(same VM loops, same cost accounting, same context split). The central
theorem quantifies over spec ASTs and configurations:
`R.run cfg (R.compile p) s pos opts lim = Exec cfg p s pos opts lim`
(soundness and
completeness in one equation, per wave), which composed with Layer S's
refinement theorem says the reference engine, whenever it completes,
returns exactly `Matches`. On top come the stack and memory bound
theorems, and cross-matcher agreement on Pike-eligible patterns as the
corollary noted above, inherently a sufficient-budget statement: the
Pike and backtracking configurations agree whenever each runs with
limits at or above its own analyzer bounds, where sufficiency rules
ResourceExceeded out; at equal limits they may legitimately differ on
ResourceExceeded. Note what the
quantifier means: until the parser proof lands (M10), every theorem is
about ASTs, and the pattern-text-to-AST step is a tested link, stated as
such wherever we describe coverage.

Layer I, the IR embedding. TIR syntax as inductive types plus a definitional
interpreter (environment, store, fuel). The engine term is not transcribed
into Lean by the Python tool at all: the Lean project contains its own TIR
JSON decoder, written in Lean, and the build decodes the canonical
`engine.tir.json` bytes into the deep embedding directly, then re-serializes
through a Lean-side canonical printer and byte-compares against the input
as a self-check. That keeps any Python-side exporter out of the trusted
base, but we state exactly what it buys, because round-tripping is
weaker than it looks: a decoder that misread Split as Jump while its
printer wrote it back as Split would round-trip byte for byte and prove
theorems about the wrong program. The honest formulation is that Lean
proved its interpretation of these exact bytes, and that the decoder, as
a mapping from the JSON schema to the deep embedding, is a trusted-base
item next to the Layer S spec. We keep it trustworthy the same way: a
transparent constructor-per-constructor mapping written for auditability
against the normative TIR schema of the M2 spec document, the same
schema the backends implement, while the cross-implementation runs of
section 8 (Lean reference evaluation against the Python interpreter and
both backends on one corpus) test that every consumer reads the artifact
the same way. The round-trip self-check still earns its keep, pinning
the decoding as lossless, it just is not the semantic argument.
The theorems for this layer are refinements of both
runtime stages the public API depends on: running the TIR interpreter on the
exported engine's compile function agrees with `R.compile`, and on its match
functions with `R.match`, so the composed runtime path is covered for every
AST. Because the TIR engine and Layer R are written to be structurally
parallel, this decomposes into per-function simulation lemmas, which is
tedious but mechanical; automation (simp sets per IR construct, and
`decide`/`native_decide` for table lookups) keeps it moving.

Layer A, the analysis proofs, in the checker form of section 5: the
certificate checker is proved sound, so whenever a certificate is
accepted, the VM run stays within the certified cost, stack, and memory
bounds. The analyzer that searches for the certificate needs no proof at
all, which is the point of the split. Classification soundness (linear
really is linear) is proved; classification precision is only tested.

What we explicitly do not prove at first: the pattern parser (proved last,
in the M10 milestone; before that it is validated by differential testing
and fuzzing against pcre2's parser including error cases) and the backends
(see section 7). The M10 parser theorem has a definite shape so it is a
plan, not a wish: Layer S gains a spec-level parsing function
`ParseSpec : bytes -> Options -> CompileResult` over a grammar written for
auditability, and the theorem states that the shipped TIR parser, run
under the Layer I interpreter, returns exactly `ParseSpec`'s output,
errors and offsets included; composed with the existing chain this closes
the loop from pattern text to match outcome. Every unproved link
is compensated by testing and kept small, and the design doc for each release
states exactly which theorems exist. Engine features are held to a harder
rule than links: a feature whose proof chain is incomplete is not silently
"supported" — compiling a pattern that needs it fails with UnsupportedFeature
unless the caller passes an explicit allowUnproved compile option, so the
default surface of every release is exactly the proved surface, which is
what the objective's "correctly implement PCRE, with a proof" demands.
No overclaiming.

CI wiring: `make verify` re-emits the IR, recomputes its hash, and runs
`lake build`, whose decoder reads that exact artifact. A hash mismatch, a
failed round-trip self-check, or a broken proof fails the pipeline. The exact resulting guarantee, which release notes must
repeat verbatim rather than round up: the IR artifact the backends consume
is the one the theorems were checked against, read through the audited
Lean decoder that the trusted base includes; the decoder's schema
mapping and the backend translation are the two tested links, the first
trusted-base and audited, the second unproved and cross-checked.

## 7. Backends

Backends are deliberately the dumbest part of the system: syntax-directed
printers from TIR to source text, roughly 1500 lines each, with no
optimization passes (we rely on Go's compiler and JS JITs). Their smallness
is a trust argument: they are reviewable by eye, and their output is
cross-checked (section 8). A verified or translation-validated backend is a
possible future hardening, noted in section 10.

Go backend. Emits one package: types as structs, enums as typed constants,
`vec<T>` as slices manipulated only through generated push/reserve/truncate
helpers that check the declared capacity limit before any allocation happens
(a raw `append` could reallocate first and check later, which would break
the memory-budget story, so raw append never appears in generated code),
`inout` as pointers, checked indexing as normal Go indexing whose native
bounds-check panic realizes the section 3.1 trap, `counter` as uint64
with a saturating add helper.
Every scratch vector a match call can touch is registered against the
scratch-memory limit of section 5, not just the backtrack stack. Public API
is a thin hand-written wrapper
(committed, not generated) exposing the section 2.4 surface with Go
conventions: `Compile(pattern string, opts Options) (*Regexp, error)`,
`(*Regexp).Match(subject []byte, ...)`, etc. No goroutines; a compiled
Regexp is frozen in the section 3.1 sense, hence immutable and safe for
concurrent use, scratch state lives in the
per-call or per-context workspace of section 2.4, and a match run against a
preallocated context performs no allocation at all.

JavaScript backend. Emits one ESM module plus a hand-written wrapper and a
`.d.ts` file. The storage mapping is fixed per IR storage class, not left to
the printer's mood: `bytes` is Uint8Array; `vec` of u8/i32/u32 is a typed
array plus an explicit length field, grown by allocating a new buffer and
copying, with the same capacity-check-before-allocation discipline as Go;
`vec` of structs is an ordinary Array of class instances whose classes have
all fields initialized in the constructor (monomorphic shapes for the JITs);
structs are those same classes; checked indexing emits an explicit bounds
test that throws on failure, realizing the section 3.1 trap, because an
out-of-range typed array read would otherwise silently produce undefined;
integer ops get `| 0` / `>>> 0` coercions,
except multiplication, which must go through `Math.imul` (then `>>> 0` for
u32) because a plain double product can lose low bits above 2^53 before
any coercion runs — the one place where naive JS lowering is silently
wrong rather than slow, so the conformance suite hammers it; `counter` is
a plain number with a saturation constant of 2^53 - 1. These
layout rules live in the TIR spec document next to the determinism rules,
and the conformance suite includes cases aimed squarely at growth, overflow,
and coercion behavior. The wrapper takes Uint8Array subjects; string
overloads arrive with UTF mode in wave 3. Runs on Node and browsers; no
dependencies.

Cross-language determinism rules live in one place (the TIR spec document):
integer widths and wrapping, saturation point, iteration order (always
index-based), and growth policy. Both backends implement that spec, and the
conformance suite enforces it bit for bit.

Rust and C later: the IR was shaped for Go-like targets, and both Rust and C
accept the same shapes (explicit stacks, no recursion, tagged unions by
struct+tag). Nothing in the plan blocks them; they are out of scope until
after M10.

## 8. Testing strategy

Testing exists to cover exactly the links the proofs do not, and to keep the
proofs honest against the real pcre2.

- Oracle differential testing. A small C harness links libpcre2-8 and speaks
  a line protocol (pattern, options, subject in, ovector or error out). The
  Python side drives it with: hand-written cases per feature, the imported
  pcre2 testdata files (testinput1/2 subsets that fall in our supported
  scope, with a tracked skip list), and generated cases. Every result is
  compared field by field: match/no-match, all ovector entries, and compile
  errors including offsets. Runs where our engine reports ResourceExceeded
  are excluded from result comparison, per the oracle policy of section 1.
- Differential fuzzing. A grammar-based pattern generator (weighted toward
  nasty constructs: nested quantifiers, empty-matching groups, boundary
  anchors) plus random and structure-aware subjects. Each case runs against
  pcre2, the Python IR interpreter, the generated Go, and the generated JS —
  including the cases pcre2 has no opinion about, since a construct outside
  the claimed subset still has to be refused with the same code at the same
  offset by every implementation of this engine, and only the comparison with
  pcre2 is skipped. Any disagreement is a bug, minimized automatically and
  added to a corpus: to the semantic one when what disagreed is an answer,
  and to the sweep's own kept cases when it is an invariant — a bound, a
  limit edge, a context, the two matchers — since a corpus of expected
  answers never asks those and a regression filed there would guard nothing.
  Our cost limit does the budgeting, pcre2
  gets a generous match_limit purely as an external safety net, and results
  are compared only when our engine completes within its budget.
  The generator is `pcrevera.sweep`, and a case is a function of the numbers
  its manifest was generated from and its own index, which is what lets a
  manifest be rebuilt rather than kept and a failure be named by a manifest
  hash and an index rather than carried around as a pattern. The generator
  those numbers name belongs to the repository rather than to the host's
  standard library, so a manifest hash means the same thing on every
  interpreter. One population, one
  generator: the smoke test that runs on every commit and the campaign that
  runs for an hour differ in scale and in nothing else. What runs in ordinary
  CI is a committed shard — `conformance/sweep.json`, one deterministic slice
  of that population with every answer recorded, replayed by all three engines
  and by pcre2 — plus a small generated campaign against the oracle. The
  sustained side of this, meaning rotating seeds, scheduled long runs, deeper
  minimization and the week-long campaign, is M9's infrastructure and is
  called out there; M5 owns the harness, the shard and the campaign that
  closes the milestone. Both are stated here because "runs continuously" and
  "M9 builds the continuous runner" are easy to read as the same sentence.
- Cross-matcher agreement. On Pike-eligible patterns, Pike VM and
  backtracking VM results are compared on every fuzz case through the
  internal testing entry point, each matcher running with limits
  at or above its own analyzer bounds, mirroring the sufficient-budget
  premise of the section 6 agreement corollary. Where the backtracking
  analyzer has no finite certificate for such a pattern there are no
  sufficient bounds to run it under, and the pair is counted apart rather
  than folded in with the agreements: an answer is still compared, since a
  disagreement is a bug whatever the budget was, but a run that hits a capped
  budget says nothing and is never reported as agreement.
- Resource bound tests. For each fuzz case, run with instrumentation and
  assert that actual cost, stack depth, and scratch memory never exceed
  the analyzer's bounds, memory measured the way section 5 defines it:
  peak allocated IR bytes across every scratch array, growth overlap
  included, context reset work and every allocation attempt counted. The
  limits are tested at the edge too: for each of the three on plain
  calls, and for cost and stack on context-backed calls, a run with the
  limit set to the observed actual must succeed (host allocation
  permitting, which the harness makes a non-factor by running with
  ample free memory) and one below it must return ResourceExceeded,
  the deterministic budget boundary host conditions cannot move, on
  both matchers; the one-below assertion applies when the observed
  actual is positive, while zero usage is asserted as success at a
  zero limit and BadInput for a negative one; the memory edge on
  contexts is tested at creation instead, `CreateCtx` succeeding at the
  reservation and failing one IR byte below it. This tests Layer A and the enforcement paths empirically on
  inputs the proofs quantify over anyway, and catches analyzer
  regressions instantly. Re-running is what the edges cost, so they are run
  once per distinct observed usage of a case and no more than a stated number
  of times per case; both limits are deterministic, so a replay edges exactly
  the same trials, and the count of edge checks is part of the coverage report
  rather than something a reader has to infer.
- Conformance suite. A language-neutral JSON corpus of (pattern, options,
  subject, expected result, expected bounds) checked into the repo; each
  backend has a tiny runner. Backends must agree bit for bit with each other
  and with the Python interpreter.
- Proof CI as described in section 6.

Performance benchmarks (section 9, M9) compare against pcre2 and Go's regexp
on standard corpora; the target is "same order of magnitude as pcre2
interpreted", not beating JITs.

## 9. Step-by-step build plan

Each milestone has a definition of done. Order matters: the oracle harness
comes absurdly early because every later step leans on it, and Lean layers
S and R start before the engine is feature-complete so spec problems surface
while the engine is still cheap to change.

M0, scaffolding (small). uv-managed Python project, lake project skeleton,
Go module and JS package placeholders, CI running pytest + lake build,
`tmp/` for scratch. Done when: CI is green on a hello-world of each part.

M1, oracle harness. The C pcre2 shim, the line protocol, pytest integration,
first hand-written differential cases. Done when: `pytest -k oracle` runs
pcre2 and compares results for a seed corpus.

M2, TIR core. The normative TIR specification document comes first:
every operator and checked operation with its exact result on every
input, evaluation order, trap behavior, storage sizes and layouts, and
the linearity and inout-disjointness rules — the text that sections 3
and 7 defer to and that the Lean decoder and both backends implement.
Then the IR schema and JSON serializer, validator (types, acyclicity,
inout place disjointness, variants, capacities), Python reference
interpreter, the authoring DSL, golden tests. Done when: the spec
document covers every construct the schema admits, a toy program (say,
bounded Fibonacci with an explicit stack) round-trips DSL -> JSON ->
interpreter, and all validator rules have negative tests.

M3, engine wave 1 in TIR. Parser, bytecode compiler, backtracking VM with
limits (the Pike VM waits for M5 so M3 stays small). Done when: differential
tests pass against pcre2 on the wave 1 corpus via the Python interpreter,
including compile errors.

M4, Go and JS backends. Printers, hand-written wrappers, conformance
runners. The section 2.4 analysis accessors do not exist yet (the analyzer
is M5), so at this stage the generated API is explicitly provisional:
compile and match only, every pattern running on the backtracking VM
because Pike selection does not exist until M5, and the wrappers say
so; the section 4.3 routing discipline, including the test-only status
of plain backtracking on Pike-eligible patterns, takes effect when M5
lands. Done when: the conformance
corpus passes bit for bit in Python interpreter, Go, and JS; generated code
passes `go vet` and eslint; a README-level usage example works in both
languages.

M5, Pike VM and analyzer v1. Linear matcher, matcher selection, linearity
classification, cost, stack, and scratch-memory bounds computed as the
section 5 certificates with their TIR-side checker and runtime
enforcement, the preallocated match context in both
backends, bound assertions wired into fuzzing, and the analysis accessors
added to both backends, which together complete the section 2.4 API
contract in shape; the memoized matchConfig value stays rejected as
BadInput, accessors included, until M9 activates it, and the API docs
state that explicitly. Done when: wave 1 fuzzing shows zero disagreement between the
matchers on Pike-eligible patterns and none between our engine, pcre2,
and both backends anywhere, no bound violation, and a
context-backed match performs zero heap allocations under Go's allocation
counter and constructs zero backing stores under JavaScript constructor
instrumentation, per the section 2.4 per-target statement of the
no-allocation promise.

M6, Lean layers S and R for wave 1. Spec semantics, reference engine,
equivalence and termination and bound theorems. At the start of this
milestone we freeze and tag a wave 1 IR artifact; M6's reference proofs and
M7's refinement both target that frozen artifact, otherwise the proofs
chase a moving target while M8 lands features. Done when: `lake build`
proves the theorems, and the Lean reference engine (via #eval or
extraction) agrees with pcre2 on the conformance corpus.

M7, Lean layer I foundation. TIR embedding with its definitional
interpreter, the Lean-side artifact decoder with its round-trip self-check,
hash pinning in CI, and the proof automation the refinement will spend.
Engine changes after the freeze re-open proofs deliberately and visibly,
as far as there are proofs to re-open: a moved hash fails the build and
every existing proof is rebuilt against the new bytes. The stronger rule —
the pinned hash moves only together with the proof increment that covers
the change — needs a lemma per function before it can withhold anything,
so it arrives with M7R. Done when: `make verify` fails on a generated file
drifting from its generator, on a hash drifting from the freeze record, on the
coverage ledger drifting from the call graph, on the artifact failing to
decode inside Lean or to print back to its own bytes, and on any proof that
no longer builds. Binding the artifact's *meaning* to layer R is not part of
that gate and is M7R's; until then a changed engine is caught as drift and
by rebuilding what is already proved, which is a narrower promise and the
one the target actually keeps.

M7R, the artifact refinement. The per-function simulation campaign and the
composed theorem PLAN-M7.md section 1 states, scheduled after M8. This is
where the milestone's risk went and it is why it was split off: PLAN-M7.md
section 10 prices the campaign at roughly 110,000 lines of Lean *after* the
automation built to avoid exactly that, and records the two samples the
number comes from. Done when: the composed refinement of PLAN-M7.md section
1 is proved and `make verify` checks it. Until then the fallback below is
the one in force, and THEOREMS.md section 5 states layer I's coverage in
those terms. See section 10.

M8, engine wave 2. Backrefs, lookaround, atomic groups, possessive
quantifiers in engine + analyzer (bounds updated) + tests; extend spec and
proofs (S, R first, I incrementally per feature). Each wave 2 change
produces a new versioned artifact, and from here the repo tracks two pinned
manifests, each bundling an artifact JSON, the Lean sources proving it, and
its theorem inventory: one for the newest fully proved artifact, one for
the shipped artifact, whose possibly-smaller inventory the release notes
state explicitly. `make verify` builds each pinned manifest independently,
so a proof gap is always a visible, named thing rather than a silently
moved hash. Wave 2 features whose
proof chain is still incomplete sit behind the allowUnproved compile option
of section 6 rather than in the default surface. Done when: wave 2
differential fuzzing is clean and the proofs cover at least atomic groups
and lookahead, with the remaining gaps listed explicitly and gated.

M9, hardening and performance. Continuous fuzzing infrastructure, pcre2
testdata import completed, benchmarks, memoized backtracker option, API
polish, complexity API documentation with worked examples. Done when: a
week of fuzzing finds nothing, and benchmarks are published in the repo.

M10, wave 3 and parser proof. UTF-8 and case folding with generated tables,
\p classes, conditionals; recursion only under the conditions of section 12,
with its depth limit threaded through Limits, the accessors, the analyzer,
and the S/R/I theorems before any recursive pattern compiles without
allowUnproved; parser correctness proof; release documentation stating the
exact theorem coverage. Done when: every feature reachable without allowUnproved has its
full S/R/I chain proved, and 1.0 is tagged with that correctness statement.

Rough effort ranking, largest first: M7R, M7, M6, M8, M3, M5, the rest. If
M7R stalls, the fallback that keeps releases honest is documented in
section 10.
One consequence of the section 6 gating rule is worth spelling out: a
milestone can ship working, tested, fuzzed features early, they just sit
behind allowUnproved until their proofs land, so proof pace throttles the
default surface, never the engineering.

## 10. Risks and fallbacks

The refinement proof (M7R) is the schedule risk, and splitting it out of M7
is what section 9 does about it. Deeply embedded imperative proofs are
workable but slow. Mitigations: TIR is intentionally tiny, the
engine and Layer R are written in lockstep to make simulation lemmas
mechanical, and we build proof automation as we go. Fallback if it stalls:
keep releasing as 0.x with layers S and R proved and layer I covered by
exhaustive interpreter-vs-Lean-engine testing on the conformance corpus,
stated as such; the 1.0 label and the objective's full proof claim wait for
the refinement, and the architecture does not change either way.

PCRE semantic surprises. PCRE has decades of edge cases (empty-match rules,
\b at buffer edges, ovector conventions for unset groups). Mitigation: the
oracle harness from M1 onward, pcre2's own testdata, and treating pcre2's
behavior, not its documentation, as ground truth when they disagree.

Backends are unproved. Mitigation: kept tiny and dumb, bit-for-bit
conformance testing across three implementations, and Go/JS ecosystems'
own type checking. Future hardening: translation validation per release
(prove the printed Go parses back to equivalent IR) or a verified printer
for one target.

JS numeric semantics. All 64-bit needs were designed out (counter saturates
at 2^53 - 1); the conformance suite runs arithmetic edge tests specifically
targeting the coercion patterns.

Analyzer over-conservatism could scare users off legitimate patterns.
Mitigation: report both the class and the concrete bound so applications
can decide with numbers; document typical values; offer the memoized
matcher as a middle path.

## 11. Repository layout

```
pcre-vera/
  objective.md, DESIGN.md, BOUNDS.md, LOG.md, api-faq.md
  pyproject.toml            uv project: the generator and all tooling
  src/pcrevera/
    tir/                    schema, validator, serializer, interpreter
    dsl/                    IR builder API
    engine/                 the PCRE engine, authored with the DSL, and the
                            bounds and classification of section 5, which are
                            part of the same TIR program rather than a package
                            of their own
    backends/go/, js/       printers
    leanexport/             canonical artifact emission and hash tooling
    oracle/                 pcre2 harness driver, corpus tools
  lean/                     lake project: Spec/, Ref/, Tir/, Engine/, Proofs/
  oracle/pcre2shim/         the C shim
  conformance/              language-neutral corpus (JSON)
  gen/go/, gen/js/          generated artifacts + hand-written wrappers
  tmp/                      scratch, never committed
```

The generated Go and JS are committed (reviewable diffs, usable without
running the generator), with CI verifying they match a fresh generation.

## 12. Open questions

- Whether wave 3 recursion ((?R), (?1), (?&name)) can meet the
  bounded-resources promise in a satisfying way, or should stay permanently
  behind an opt-in flag. The current sketch encodes subroutine calls as
  engine-level call frames on the explicit backtracking stack (the TIR call
  graph stays acyclic), with a configured recursion depth limit surfaced
  through the API and folded into the stack bound. Admitting it means
  threading that depth through `Limits`, every analysis accessor, the
  analyzer formulas, and the S/R/I theorems first, which is exactly why it
  sits in wave 3 rather than being bolted on; what that costs in the
  analysis and the proofs is the open part.
- Whether the Lean spec should also be cross-validated against Warblre's
  published semantics on the feature intersection, as an extra audit.
- How much of pcre2's error-message text to reproduce verbatim versus only
  matching error codes and offsets.
