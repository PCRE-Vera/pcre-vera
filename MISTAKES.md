# Mistakes caught during design review

A record of what the first draft of DESIGN.md got wrong, caught over the
swival review rounds. Kept as a checklist of traps for the implementation
phase.

## Overclaiming

- Described the generated Go/JS as covered by the proofs, when the theorems
  stop at the TIR artifact and the backends are a tested link.
- Promised "same results as pcre2" unconditionally, ignoring that resource
  limits make ResourceExceeded an observable outcome pcre2 does not share.
- Presented the ReDoS classifier as if exact polynomial degrees were
  computable for full PCRE; only "linear (proved)" vs "notProvenLinear
  (conservative bound)" is defensible.
- Let a saturated counter value pass for a finite worst-case bound.
- Allowed shipping unproved features as "supported"; they must sit behind an
  explicit allowUnproved option to honor the objective's proof requirement.
- Presented the JSON round-trip self-check as proof that Lean and the
  backends assign the artifact the same meaning; a consistently wrong
  decoder round-trips perfectly, so the decoder belongs to the trusted
  base and is kept auditable instead.
- Claimed one formal Matches function could define resource outcomes for
  every matcher configuration; the matchers meter work differently, so
  the spec had to split into pattern semantics plus per-configuration
  execution semantics.
- Called the engine "realtime" without saying that GC pauses, JIT warmup,
  and scheduling belong to the host; the honest claim is bounded,
  allocation-free engine work.
- Promised deterministic ResourceExceeded and allocation-free matching
  for plain calls too; only a preallocated context removes host
  allocation failure from the picture.
- Stated context-creation sufficiency without the creation-only charges
  and without conditioning on per-call limits staying at or above the
  bounds.

## Unsound resource math

- Asserted a universal a + b*n backtracking stack bound; lookbehinds and
  counted repetitions break the linear shape. Per-opcode accounting is the
  sound approach.
- Charged one step per BackRef instruction; the real cost is per compared
  byte.
- Ignored the cost of scratch initialization, zeroing, and copy-on-growth in
  the cost model.
- Counted live entries instead of peak allocated capacity (growth briefly
  holds old + new buffers).
- Post-hoc saturating addition lets a run idle at the cap doing uncounted
  work; enforcement must pre-check charges against the remaining budget.
- Counter multiplication needs the same pre-checked saturation; in JS the
  double product rounds before any after-the-fact check.
- Claimed the analyzer composes per-opcode rules "over the program
  structure" after compilation had flattened that structure away; the
  compiler now emits a region table and the analyzer a bound certificate
  that a proved checker validates.
- Let worstCaseMemory answer two different questions silently: plain-call
  peak at the subject length versus a context's constant resident
  reservation at the declared maximum.
- Let accessors report finite bounds larger than any acceptable runtime
  limit; a bound above the portable caps is ExceedsBudget.
- Mixed an element-count ceiling with a byte ceiling that multi-byte
  vectors cannot both satisfy; the ceiling is bytes, per-vector
  capacities are derived from element size, and the stack-entry cap
  divides by the entry size.

## Semantic traps

- Pike VM thread dedup by pc alone is wrong once counter registers exist;
  counted repetitions must be unrolled (state-free) for Pike routing.
- Copy-on-write capture arrays shared across threads contradicted TIR's own
  no-aliasing rule; a pooled handle-plus-refcount scheme resolves it.
- The memo-table option as first drafted had an empty eligible set (its
  restrictions coincided with Pike eligibility); it is a performance mode,
  not a feature extension.
- Cross-matcher "agreement at equal limits" is unsound; the matchers meter
  resources differently, so agreement holds under sufficient budgets.
- `| 0` / `>>> 0` lowering of 32-bit multiplication in JS loses low bits;
  Math.imul is required.
- Struct/vec copies reintroduce aliasing through Go slices; heap-backed TIR
  values must be linear (move-only), including field and element paths.
- Read subjectLen as "the length actually searched"; lookbehind and word
  boundaries inspect bytes before the start offset, so only the full
  subject length is a safe bound parameter.
- Waved at "the standard find-all advance rule"; the real rule needs the
  empty-match retry overlay that never touches caller options, CRLF and
  UTF-8 advancement, the \K progress case, end-of-subject termination,
  and resumable attempt state with validated rebinding.
- Promised "no panics" while lowering checked indexing to plain Go
  indexing, and forgot that JS typed arrays return undefined out of
  range instead of failing; the trap semantics is now explicit and
  realized per backend.
- Gave TIR linearity no way to share a compiled pattern across
  concurrent matches; a one-way freeze intrinsic fixes it soundly.
- Checked inout distinctness by variable name, which admits a struct and
  its own field as two arguments; disjointness must be over access
  paths.

## Underspecification

- No pinned pcre2 build (version, flags, tables, newline, BSR) — "correct
  PCRE" is meaningless without one. Same later for the Unicode database.
- Missing NEWLINE/BSR options that ^ $ . \R depend on.
- No byte-level pattern type story for JS, no unset-capture representation,
  no start-offset validation, no limit-validity rules, no compile-time size
  policy, no find-all budgeting statement.
- "Stack usage in bytes" as a portable contract; only engine-defined units
  (entries, IR bytes) are portable.
- Match contexts needed a declared max subject length and context-owned
  result storage to honestly claim allocation-free matching.
- The trusted JSON-to-Lean exporter was avoidable: a Lean-side decoder with
  a round-trip self-check removes it from the trusted base.
- "The usual arithmetic operators" left division, remainder, shifts,
  casts, and evaluation order open exactly where Go and JavaScript
  disagree; the M2 TIR spec is normative on every operator.
- Claimed wave 1 is entirely linear while the unroll cap routes some
  counted repetitions to backtracking; the classifier speaks per
  pattern, the wave does not.
- Left the configuration story half-said: matchConfig missing from the
  match signature and the section 5 bound functions, contexts conflated
  with it, the test-only backtracking path unnamed, ineligible requests
  unrepresentable in the formal Exec.
- Left BadInput underdefined: invalid limits, over-cap subjects, context
  violations, and context creation itself were outside the formal
  contract.
- Omitted ovector and result storage from the memory bound, omitted
  memory from the resource tests entirely, and wrote limit edge tests
  that break at zero usage.
- Let an off-by-one slip between the 2^31 - 1 subject cap and a "below
  2^31 - 1" array ceiling.

## Process notes

- Milestone ordering promised API completeness before the analyzer existed,
  and let proofs chase a moving engine; freezing artifacts and gating the
  API contract fixed both.
- M4 exposed the backtracking matcher publicly on Pike-eligible patterns
  before Pike existed, and M5 claimed to complete an API whose memoized
  value only arrives in M9; both milestones now say what is provisional.

## Caught during M0/M1 implementation

- Parsed pcre2's `pcre2_chartables.c.dist` looking only for `0x..` tokens and
  got 576 bytes out of a 1088-byte table without noticing anything was wrong.
  The file writes the two case-mapping tables in decimal and the bit maps in
  hex. The length check against `PCRE2_CONFIG_TABLES_LENGTH` is what caught it,
  which is the lesson: a parser that cannot state how much it expected will
  happily return half an answer.
- Wrote four seed-corpus compile-error offsets from intuition. pcre2 reports
  the parse position at detection, which is one past the offending character in
  three of those cases and on it in the fourth. Guessing where a library points
  is not the same kind of claim as knowing what a construct means, and the
  corpus now separates the two.
- Trusted a cached build because its directory was named after a digest of the
  pin. The name records what was meant to be there, not what is there now. A
  cache is only as good as the checks it repeats on the way out.
- Let a validating loader coerce instead of check. `str(entry["pattern"])` turns
  the JSON number 61 into the two-byte pattern "61", and the case then passes
  while testing something else. Same shape as the pin that skipped a check for a
  field it did not find: silently doing nothing looks exactly like success.
- Guarded a blocking read with a watchdog and read the "did it fire" flag
  without a lock, so a response arriving as the clock ran out could have been
  discarded and a healthy oracle killed.
- Put a watchdog on the read half of a request and called it "every request has
  a timeout". The write half blocks just as well, once a large pattern fills a
  pipe nobody is draining.
- Accepted a response line that had no line terminator. A dying shim's partial
  output then reads as a shorter answer, which is precisely the kind of fiction
  a differential harness must never manufacture.
- Wrote a test named for reusing a valid cache that was actually reusing an
  incomplete one, so it asserted the opposite of its name and hid the missing
  source-tree check underneath it.
- Advertised a shared oracle cache and then built straight into the final
  directory. Two builds at once unpacked over each other and both failed. A
  cache that anything else may be using at the same time has to be written the
  way anything shared is: build aside, publish in one step.
- Closed and typed one section of the pin schema and left the other three open,
  which is the same "looks pinned, checks nothing" hole, three quarters of the
  way unfixed.
- Versioned a build recipe with a constant a human has to remember to bump. The
  recipe is code; hashing the code is the version.
- Fixed a shared-cache race in the branch I was looking at and left the other
  branch of the same function writing straight into the shared path. A race is a
  property of every path to a resource, not of the interesting one.
- Corrected an overclaim in the docstring and left the same sentence standing in
  the CLI output, a neighbouring docstring, and the README. Wording that is
  wrong is usually wrong in more than one place, because it was copied.
- Compared a schema number with `!=`. In Python `True == 1` and `1.0 == 1`, so
  two things that are not schema numbers passed for one.
- Derived a test marker from the fixtures a test requests, which is right for
  every test that uses a fixture and wrong for the one that called the machinery
  directly. A derived property is only as good as the thing it derives from.
- Fixed the `schema != 1` type trap in the pin loader and left the identical
  line in the corpus loader. Two loaders, one lesson, learned once.
- Validated a JSON document's fields without first checking it was a document.
- Closed and typed the schemas inside a corpus case while leaving the case
  itself open, so the field that says which case it is could go missing without
  a word worth reading. The outermost layer is the one an author gets wrong
  first.

## Caught during M2 implementation

- Gave a builder class an attribute named `ret` and a method named `ret`. The
  attribute won, so every `f.ret(expr)` built a literal and emitted no return
  statement, and the validator's "can reach its end without returning" was the
  only thing that noticed. In a class that is half data and half verbs, a name
  that reads as both is a name to avoid.
- Serialized declarations in canonical (sorted) order while keeping the
  author's order in memory, so a program did not equal what its own text
  decoded to. If an encoding normalizes something, the value has to normalize
  it too, or round-tripping tests a weaker property than it looks like.
- Propagated `frozen` through every field read out of a frozen struct. The rule
  is narrower: a field comes out frozen only when it would otherwise be linear,
  because a copyable field is copied out and writing to that copy must not
  reach back into the frozen value. A rule stated as "X propagates" is worth
  re-reading for the case where it should not.
- Wrote an interpreter that recovered operand widths from the runtime values,
  which works for everything except a bare integer — which is to say, for
  everything except the case that matters. It carries a small type environment
  now, built from the declarations it walks past.
- Let the validator index `INT_RANGE` with whatever type a literal claimed. The
  reader can only build literals of the five scalar types, but the DSL will
  happily write `bytes_(5)`, and a KeyError is not a rule violation. Every
  table lookup in a checker needs the check that the key is in the table.

## Caught reviewing M2

All of one shape, and worth stating as one lesson: **a checker that shares a
boundary with a parser will quietly rely on the parser.** Every hole below is
a check that existed in the reader and nowhere else, on a path a program built
in memory takes and a decoded one does not.

- Wrote operator dispatch as "if it is `not`, else treat it as `neg`/`bnot`",
  which reads as exhaustive and is not. `Unary("wat", x)` validated and
  computed bitwise-not. An else-branch over a closed set has to be spelled as
  the closed set, or the set is not closed.
- Compared a struct literal's field *names* as a set, after `dict()` had
  already collapsed a repeat. Building the dictionary is what discarded the
  evidence; the length is what says "exactly once".
- Range-checked payloads without type-checking them. `0 <= 1.0 <= 7` is true,
  and `x << 1.0` is a TypeError. A comparison is not a type check, and in
  Python it will not tell you so.
- Detected struct cycles by following only fields whose type is directly a
  struct. A cycle through `frozen<S>` has a finite storage size, so nothing
  looked wrong, and only the zero value — which is defined recursively —
  actually diverges. When two derived properties differ in what they recurse
  through, the check has to follow the one that recurses further.
- Assumed a name that parses is a name that prints. `var`, `class` and `len`
  are all fine identifiers here and unusable in Go or JavaScript verbatim.
- Made the reference interpreter raise a trap from a loop variant, when the
  document says no backend evaluates a variant at all. An interpreter that is
  the only implementation able to produce an answer is producing the wrong
  answer.
- Enforced argument disjointness at TIR call sites and left the host-facing
  entry point taking the same cell twice, which hands one heap-backed value two
  live names. A rule that holds inside the language and not at its edge does
  not hold.
- Wrote a normative rule — "a linear value is never read as an expression" —
  that nothing implemented and nothing could, since `len(v)` reads `v`. A
  specification sentence that no test can fail is a sentence nobody checked.
- Stopped an aliasing walk at frozen values, reasoning that sharing one is what
  freezing is for. True of two frozen views of a value; false of a frozen view
  of something still mutable elsewhere, which then watches it change. A rule
  that holds for the symmetric case is not thereby a rule.
- Then wrote the same check over `inout` arguments only, having just restated
  the rule it was mirroring — which says "every other argument, `in` ones
  included, since they read". Three review rounds went into one aliasing check.
  When a rule already exists in prose, the implementation should be read back
  against that sentence, clause by clause, rather than against the case that
  prompted the fix.
- Checked "every validator rule has a negative test" by looking for the rule's
  number in the test file. A comment satisfies that. The suite watches for the
  rules it actually provokes now, which is the difference between testing the
  property and testing that somebody typed its name.
- Compared types with `is` while relying on `==` everywhere else. `Prim` is a
  frozen dataclass, so a rebuilt `Prim("bytes")` is equal to the constant and
  is not the constant; `is_linear` asked the second question and answered "not
  linear" about the type linearity exists for. Two ways of asking the same
  question is one too many, and the one the data model already supports is the
  one to keep.
- Ended a projection-by-projection comparison at the first pair that matched.
  Two equal literal indices settle nothing on their own — `v[0].a` and `v[0].b`
  are disjoint — and a comparison that walks a list has to say what "equal so
  far" means as carefully as what "different" means.
- Detected struct cycles with a plain recursive walk: no memo, so a shared
  suffix was re-walked once per incoming edge and a chain of diamonds cost
  2^n, and no explicit stack, so a long chain raised `RecursionError`. A
  validator that answers `RecursionError` has not answered.
- Resolved every name through a dictionary lookup and never asked whether the
  name was a string. An object with a cooperative `__eq__` and `__hash__`
  resolves as `"u32"` through the whole validator and reaches a serializer that
  has nothing to write. Equality is what a lookup asks; it is not what the
  answer is used for afterwards.
- Wrote a mutation sweep that replaced leaves and dropped list elements, and
  called it a proof that the validator is the boundary. It never put a node of
  one kind where a node of another belongs, which is the one thing a program
  built in memory can do and a decoded one cannot — so it missed an `EnumDecl`
  among the structs, a variant list that was a `list`, and a bytes constant
  holding a `str`. A sweep proves what it varies.
- Promised that printers emit TIR names verbatim while letting two enums share
  a variant name. Go turns a variant into a package-level constant, so the two
  become one redeclared identifier. A "no mangling" contract is a claim about
  every target's scoping rules, and it has to be checked against them — the Go
  compiler had the answer in three lines.
- Answered "this walk raises RecursionError" by making that one walk iterative
  and writing a docstring that claimed the property for the module. Three other
  walks over the same program still recursed, and so would the Lean decoder and
  both printers. When a claim is about a boundary, either the boundary enforces
  it or the claim comes out of the document — a docstring is not a mechanism.

## The wave 1 engine (M3)

Every one of these was found by asking the pinned pcre2 rather than by
reasoning about it, which is the whole argument for building the oracle first.

- Applied the empty-iteration break to every quantifier. pcre2 only has one at
  a *repeating* ket; a bounded `{m,n}` is replicated instead, so all of its
  copies run and `(|a){1,3}` on `"a"` under NOTEMPTY reaches its third copy.
  A rule read off one construct was applied to a construct compiled another
  way entirely.
- Reported "nothing to repeat" at the end of the whole quantifier, lazy marker
  included. pcre2 reports it at the end of the quantifier proper, before the
  `?` that only says how it repeats. An error offset is part of the contract,
  so where it is taken is a decision, not a detail.
- Scanned a group name up to its terminator instead of over word characters.
  That collapsed four distinct pcre2 errors into one: a leading digit, an
  empty name, a name too long, and a run that stops somewhere other than the
  terminator each have their own code, and each is reported where the name
  stops rather than at the end of the pattern.
- Missed the bumpalong rule entirely: pcre2 declines to start a match between
  a CR and a LF when the convention makes them one newline and the pattern
  spells neither out. It is an observable refusal of a position where a match
  could have started, not an optimization.
- Then implemented that rule without noticing that pcre2's own start-code-unit
  filter can jump straight onto the position the rule would have skipped, so
  the rule only bites when the CR position was actually attempted. The fix is
  one bit of first-byte analysis over our own bytecode, deliberately
  conservative: an unknown answer is a yes, which is what pcre2 concludes when
  its filter is not built at all.
- Skipped whitespace inside `{m,n}` using the whole space class. The pinned
  build takes a space or a tab there and nothing else, so `a{\n2}` is a literal
  brace and not a quantifier.
- Read `(*VERB)` as a group whose first item is a star, which turned pcre2's
  "not recognized" into our "nothing to repeat".
- Left no node behind for a back reference, so a quantifier after one reported
  "nothing to repeat" instead of the reference's own error. A construct we
  refuse still has to occupy the place it occupies, or it changes what the
  rest of the parse sees.
- Picked round numbers for the AST, bytecode, class and repetition arenas, so
  a pattern inside the documented length limit could still be refused for
  running out of nodes. The four are derived from the pattern length now, which
  is what makes the length limit the one a caller can reason about.
- Reported the unknown-POSIX-class and unterminated-comment errors one byte
  short. Both are pinned by the corpus now rather than by arithmetic.

## The wave 1 engine, second pass

Found by a review of the finished code and by an exhaustive sweep over every
pattern of three bytes from a hostile alphabet — 178382 of them, which is the
kind of coverage a generator reaches and a hand-written corpus does not.

- Read one byte past the end of the pattern on a `(` that ends it. The guard
  was written as `land(pat[i] == '*', land(i + 1 < n, ...))`, with the bounds
  test in the second operand of the short circuit rather than the first. The
  interpreter's trap turned it into a visible failure rather than a wrong
  answer, which is the whole argument for having traps, but the exhaustive
  sweep is what put the case in front of it.
- Let a negative cost limit through into the interpreter's step budget, where
  it surfaced as `OutOfFuel` — an outcome only this execution path can give —
  instead of the BadInput DESIGN.md section 2.4 defines. The limits are
  checked now against the ceilings that section states, so an impossible limit
  is refused rather than clamped or acted on.
- Called the package "parser, bytecode compiler, and the two matchers" in its
  own docstring while building one matcher. The Pike VM is M5's and the
  docstring now says which parts of the section 2.4 surface are not here yet.
- Cleared the character class's "a `]` here is still a literal" flag on
  `\Q` and `\E`, which add no element. `[\E]` became an empty class where
  pcre2 sees a class that never closes.
- Reported "digits missing" for every malformed `\x{...}`, where pcre2
  distinguishes a brace with nothing in it from a byte that had no business
  being there, and put the offset in a different place for each. Spaces and
  tabs are allowed inside those braces too, the same as inside `{m,n}`.
- Reported a too-large quantifier bound at the closing brace rather than at
  the end of the number that overflowed, and only checked the lower bound
  after reading the upper one.
- Read `\8` and `\9` as literal digits outside a character class. pcre2 takes
  any digit escape starting with 8 or 9 as a back reference, whatever number
  it spells, so `\82` is a reference to group 82 and not the two bytes.
- Refused an unterminated `(?a` as an unsupported option before noticing the
  group never closed. The option letters we do not implement are read like any
  other now, and refused only once the group turns out to be well formed.
- Settled the possessive `+` before "is there anything here to repeat", so
  `*+` at the start of a pattern came back as an unsupported feature instead
  of pcre2's "nothing to repeat".
- Charged a growing scratch array for the elements copied out of the old buffer
  and not for the new one being zeroed, so the first block a run allocates cost
  nothing at all. DESIGN.md section 5 charges a unit per IR byte initialized,
  zeroed *or* copied, and a bound that leaves out the zeroing is a bound on
  the wrong thing.
- Applied the auto-possessification refusal only to greedy quantifiers. Over a
  genuinely disjoint pair a lazy repetition consumes exactly the run a
  possessive one would, so pcre2 rewrites `\R*?\s` the same way it rewrites
  `\R*\s`, and gets the same wrong answer.
- Read a quantifier's lazy marker at the next byte, where pcre2 reads it after
  the lexer has skipped what it makes invisible. `a*(?#x)?` is a lazy star.
- Accepted `(?^` anywhere among the option letters. It resets every option and
  only means that as the first thing after the `(?`, so `(?i^)` is one of
  pcre2's syntax errors and not an unsupported option.
- Refused a quantifier bound as too large before the braces had turned out to
  be a quantifier at all, so `{85125r` — which never closes, and which pcre2
  reads as the literal text it is — came back as an error.

## The wave 1 engine, third pass

A wider campaign — long and structured subjects, deep nesting, every start
offset, every convention crossed — plus a review aimed squarely at the parser.

- Recorded an explicitly written CR or LF for `[^\n]`. pcre2 compiles a negated
  class of exactly one character as "not this character" rather than as a
  class, so the code that records the flag never runs, and the bumpalong rule
  of section 4.3 then behaves differently. A range whose two ends are the same
  character counts as one character there too, because pcre2's parser rewrites
  it before the class is built.
- Treated `\Q` and `\E` inside a character class as things the class loop skips
  rather than as lexer markers, which is what they are. The hyphen test has to
  see through them on both sides: `[a\E-z]` is the range a to z, `[a-\E]` is
  the two characters a and -, and `[a-\Qz]` leaves the `]` quoted so the class
  never closes.
- Refused a POSIX name as a range endpoint with "range out of order" rather
  than "invalid range", by reading its `[` as an ordinary byte.
- Refused `\k` and `\g` inside a character class as unsupported. They name a
  group, which means nothing there, so pcre2 reads them as the letters they
  are — and refusing them also broke the ranges they bound.
- Refused a hyphen that follows another hyphen, or the `^` that clears every
  option, as an unrecognized character rather than as pcre2's invalid hyphen.
- Tested for the `^` that negates a class only at the byte right after the `[`,
  so `[\E^]` read the caret as a member instead of as the negation. The marker
  has to be looked for past `\Q` and `\E` too, and only when it is not itself
  quoted, which `[\Q^\E]` is.
- Refused lookaround, atomic and branch-reset groups the moment the opener was
  recognized. They are ordinary groups as far as the syntax goes, so the body
  is parsed and the refusal waits for the closing parenthesis; an unterminated
  one is then the missing parenthesis it is, with pcre2's code and offset.

## The wave 1 engine, fourth pass (review findings)

- Declared the backtrack stack and undo trail with a fixed 2^20 maximum,
  which quietly became a third resource limit nobody asked for: a run could
  fail below every budget the caller set. A declared maximum must be derived
  from the allocation ceiling, so the caller's limits stay the only ones.
- Passed a plain `in` argument as `inout` in the first draft of the
  read_ucp call; the validator's V-013 caught it before anything ran.
- Computed a braced group name's length after skipping the trailing blanks
  pcre2 allows, so `\k{ a }` compared "a " against the name table and
  reported a missing group. Lengths of a delimited token must be taken
  before the delimiter search moves the cursor.
- Wrote the first auto-possessification guard against the whole pattern's
  identity set on the theory that coarseness only over-refuses, and then
  documented it as the eight adjacent shapes; the README and the code have
  to describe the same predicate, and the predicate itself only needed
  parse-order suffix masks to be honest about "the next item".

## The Go and JavaScript printers (M4)

- Cloned every struct-typed read in the JavaScript printer, including linear
  ones. A linear struct never becomes a value at all — rule V-023 only lets it
  appear as a projection base — so `w` in `len(w.nodes)` has to reach the
  sequence itself, not a copy of it, and a copy method was never emitted for
  it in the first place. The fix was two rules rather than one: clone only what
  is copyable, and never clone something that is only going to be projected
  from. The second half is a real optimisation as well, since `re.ncap` was
  otherwise duplicating a whole compiled pattern to read one field.
- Wrote the JavaScript coercions as `a & b >>> 0` in the first draft, which is
  `a & (b >>> 0)`: a shift binds tighter than a bitwise and, so the coercion
  landed on the wrong operand. Caught by reading it rather than by a test,
  which is luck — the engine's own operands are small enough that the two
  spellings agree on almost everything. The rule is that the coerced expression
  is parenthesized, always, not when it looks like it needs it.
- Wrote a test asserting that the JavaScript wrapper refuses `"café"` as a
  pattern, on the theory that it is not Latin-1. Every code unit in it is at
  most 0xff, so the wrapper accepts it, correctly, and reads it as four bytes.
  The test passed only because it asserted the wrong thing; a character above
  the BMP boundary is what actually tests the rule. A test whose premise is
  wrong is worse than no test, because it also reads as documentation.
- Encoded the conformance corpus's group names as a list of `[name, number]`
  pairs, which is fine in Python and JavaScript and cannot be decoded into a
  Go map without a custom unmarshaller. A corpus that exists so three languages
  can read it should be written in the shapes all three already have; keying
  the object by the hex of the name costs nothing and needs no code anywhere.
- Nearly packed the probe's two-part answers with a multiplier of 2^32, which
  saturates the counter for any high half past 2^21 and would have turned every
  interesting case into the same CAP. A packing that loses information still
  compares equal in every language, so nothing would have failed; it would just
  have stopped testing anything.
- Left an `in` call argument to be evaluated inside the call while resolving a
  later `inout` place first, which reverses the trap order section 13 pins.
  The excuse at the time was that every trap at a call site is a T-01 and so
  the order is unobservable — but section 16 asks for exactly this ordering on
  an assignment, where both traps are also T-01, so the spec's own answer is
  that it is observable. Reaching for "this cannot be seen" is how a printer
  stops being a transcription of the semantics.
- Validated the start offset and all three limits in both wrappers and never
  the subject length, although DESIGN.md section 2.4 caps subjects at 2^31 - 1
  bytes for the same reason it caps everything else: the offsets have to fit
  in an i32. A limit that only exists in prose is not a limit.
- Wrote the JavaScript options as destructuring defaults, which fire on
  `undefined` and not on `null`, so `{limits: null}` reached a property read
  and threw a host TypeError instead of the deterministic BadInput the whole
  API promises. A default is not a validation.
- Classified a JavaScript string pattern carrying a code unit above 0xff as
  BadInput. It compiles once UTF mode exists, which makes it exactly the
  UnsupportedFeature case — a construct this release does not do yet — and
  the difference matters to a caller deciding whether to retry with a
  different release or to fix the call. Reaching for the generic outcome
  because the specific one took a moment's thought is how an error taxonomy
  stops meaning anything.
- Wrote the Go printer's constant-expression predicate as "built from literals
  alone" when the question Go asks is "will I fold this", and Go folds a named
  constant exactly as it folds a literal. The docstring described the narrower
  thing accurately, which is how it survived review: the name and the comment
  agreed with each other and both disagreed with Go. Two decisions that have to
  match — what gets emitted as a constant, and what counts as one — are now one
  function that both callers ask.
- Put a name-collision guard in each printer instead of in rule V-043, so a
  program could validate and then fail to print. The validator's own docstring
  for the neighbouring check spells out why that is wrong — "a program the DSL
  built would validate and then fail to re-read, which makes `validate` a
  weaker statement than it looks" — and the same sentence applies word for word
  to printing. Worse, the two guards then drifted: only one of them knew about
  the constant its own printer emits, and neither looked at parameters, so a
  parameter called `Math` printed a JavaScript module where `Math.imul` meant
  the parameter.
- Computed a bound term's `base^n` before looking at its coefficient, so a term
  with a coefficient of zero reported ExceedsBudget at any subject length where
  the base overflowed — a refusal about arithmetic that was never going to be
  part of the answer. The saturating multiply already short-circuits on a zero
  operand; it just never got the chance, because the operand it would have
  short-circuited on was evaluated last. Evaluation order decides which of two
  correct rules actually fires.
- Put the complexity class on the bound certificate and had the checker say
  nothing about it, so a certificate could call itself linear while naming an
  exponential cost bound. Two separate errors in one field: a claim nothing
  checks is decoration, and the class as DESIGN.md describes it is fixed per
  pattern while a certificate is per configuration, so the field also needed a
  meaning of its own before a rule about it could be written. The rule is cheap
  once the meaning is settled — linear is `c * (n + 1)`, so no growing base and
  no power above the first — which is the tell that the omission was not about
  difficulty.
- Wrote a docstring for the certificate marshalling saying it "refuses only
  what would not be a TIR value at all — a count no u32 holds, a table longer
  than its declared maximum", and then checked the integers and not the tables,
  nor the enum variants either. A docstring that describes a guard which is not
  there is worse than no docstring: the next reader stops looking, and the
  reviewer who does look has to work out which of the two is the truth. If the
  sentence is worth writing, the branch is worth writing first.
- Wrote down as a fact that the certificate checker could not be run from Go or
  JavaScript, having checked neither. JavaScript already exported every class
  and constant a test needed, and Go only wanted the test file to sit in the
  package it was testing. The tell was the shape of the sentence: it explained
  why something could not be done, in a commit that was not trying to do it.
  A limitation recorded without an attempt is a guess wearing a fact's clothes,
  and it is worse than silence because the next reader believes it.
- Ordered an enum so that its zero value was the claim rather than the absence
  of one: `CcLinear` first meant a certificate nobody had filled in came out of
  Go and JavaScript asserting the pattern was linear. TIR-SPEC.md section 4.1
  says plainly that a zero value is the first variant, so variant order is a
  safety decision in any enum whose variants are not equally harmless, and the
  conservative one goes first.
- Let the checker and the arithmetic hold different opinions about what a term
  with a zero coefficient means: the arithmetic said "zero, whatever its shape"
  and the shape rules went on refusing its base and its degree. Either answer
  is defensible alone; having both is what made it a bug, and it would have let
  a certificate call itself linear while naming an exponential term that
  happened to be multiplied by zero.
