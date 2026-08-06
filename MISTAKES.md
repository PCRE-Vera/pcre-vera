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
- Put a conformance corpus in `backends/` because that is where the last one
  went, without noticing that the last one is there for a reason the new one
  does not share: `lowering.py` builds a TIR program to test the printers, while
  the certificate corpus imports nothing from `backends` at all. Copying a
  file's location is copying the shape of a decision without the decision. The
  tell was in the test that had to import the engine's specification from
  `pcrevera.backends` and then explain itself in a paragraph.
- Left `src/pcrevera/analysis/` in place as an empty package whose docstring
  said the checker would land there, and then landed the checker somewhere else
  in the same milestone. A placeholder is a promise, and this one had already
  been broken by the commit that read it. Deleting a signpost is not churn when
  the road it points down does not exist.
- Moved a corpus generator to the package its subject lives in and left its own
  provenance line naming the old path, which then travelled into the committed
  JSON as the file's account of where it came from. A generated file that says
  who made it is only useful while that stays true, and a string is exactly the
  kind of reference no rename touches. When a module moves, its own name is the
  first thing to grep for, not the last.
- Counted a loop's iterations where the VM counts passes through its header.
  `OpRepLoop` is where the counter is read, so the pass that finds the count
  spent is a pass of its own: it reads, decides, and leaves without entering the
  body. `a{2,5}` on five bytes reaches the header six times, and the rule said
  five, so every bounded repetition was priced one visit short. What found it
  was not a test — the slack elsewhere in the total hid it — but simulating one
  anchored run by hand against the observed cost, where 239 units came out
  exactly right for six passes and one short for five. A bound derived from
  reading the code has to be checked against the code executing.
- Wrote down that the cost model and the matcher disagree about replaying the
  undo trail, and left it written down. The replay was bounded, which is true
  and is not the claim: `CrOk` says the certificate bounds the work, and work
  nothing charges for is work the meter cannot report. A caveat in a
  specification is a bug with better manners.
- Decoded enum ordinals out of a corpus file and cast them straight into the
  generated engine, in Go and in JavaScript both, while the Python side had
  refused a variant name its enum did not declare since the first slice. A TIR
  enum value is one of the variants it declares; printed, it is an integer like
  any other, and a switch that covers every variant is lowered without a default
  because there is nothing left to cover. So a number that names no variant is
  not a value the checker has any answer for — it falls through every arm and
  the region it belongs to is priced at nothing. Three runners reading the same
  file should refuse the same things, and the two that could not say a variant's
  name were the two that had stopped checking.
- Appended to `LOG.md` and `MISTAKES.md` from a shell whose working directory a
  previous command had left inside `gen/js`, creating two files there and
  committing them. This is the third time the drift has bitten, and the earlier
  two failed loudly where this one silently wrote the right prose into the wrong
  repository corner. Every command that touches a path gets the absolute one.
- Left the ovector copy uncharged after fixing the undo replay for exactly the
  same reason. Both are work the matcher does outside the instruction loop, and
  having just written down that "bounded" and "charged" are different claims, I
  did not go looking for the other place the difference lived. When a defect
  turns out to be an instance of a class, the next move is to enumerate the
  class.
- Justified option-independence with a premise that is false. Match options do
  not only remove work: `NOTEMPTY` refuses a match the run had already found
  and the search carries on, so `a??` on one byte costs more with it than
  without. The bound was sound the whole time, for a different reason — every
  fork is priced for both arms whether or not a run takes the second — and a
  specification that reaches the right answer through a wrong premise is worse
  than one that says nothing, because it invites the reader to reuse the
  premise.
- Answered "an unknown enum ordinal falls through every switch arm" by
  validating the ordinals in the corpus runners, and left the checker itself as
  it was. The runners are one caller. The generated module exports the checker,
  the enum is an integer once printed, and a switch that covers its enum is
  lowered without a default, so any other caller could still hand it a number
  that matched no arm and get a region priced at nothing. The rule that forbade
  the default — a value of an enum is one of its variants — is a fact about the
  IR, not about the code the IR is printed as, and I took it for a reason not
  to check rather than for the thing that made the check necessary. A boolean
  set in every arm and tested after says the same thing and is allowed.
- Wrote in the normative document that a region covering no instruction is
  always refused, in the same slice that made the compiler emit exactly such a
  region for an empty alternation arm and made the checker accept it. Both are
  right — a branch is read off the branch list rather than off the code — but
  the sentence had no room for the exception, and a specification that
  contradicts the implementation it specifies is worse than one that is silent.
- Closed the unknown-ordinal hole for a region's kind and for a bound's kind,
  and left the certificate's complexity class open, in the same slice. All
  three are the same shape — an enum field that arrives from outside and is a
  plain integer once printed — and the third one reads as a comparison against
  one variant rather than as a switch, so it did not look like the others. A
  fix that names a class of defect has to be applied to the class.
- Wrote a reference pricer that promises "the smallest certificate the checker
  accepts" and let it do unbounded Python arithmetic. The checker refuses a
  requirement that saturates; the pricer happily returned one twice the size of
  a counter, so the promise held only for the patterns anybody had tried. Where
  two implementations of one rule differ in what they can represent, the
  smaller representation is the specification.
- Named three constants in `spec.py`, wrote in their docstring that the
  matcher, the checker and the corpus all read them, and changed two of the
  three readers. The corpus kept its copies of the numbers, so the sentence was
  false the moment it was written — the same defect as a docstring describing a
  guard that is not there, which is already on this list. Centralising a
  constant is not the edit; replacing every spelling of it is, and the way to
  know is to change the constant and watch what moves.
- Wrote an analyzer that indexes the bytecode from region ranges and checked
  none of them, on the reasoning that the tree comes from our own compiler. The
  checker validates the same tree and reads the same array, and it is safe
  because the nesting rules run first; the analyzer had nothing running first,
  so a range past the end of the program was a trap rather than a refusal. A
  component called untrusted has to be untrusted in both directions: it may not
  be believed, and it may not fall over on the way to being disbelieved.
- Left the one new failure mode invisible to the sweep that would have found
  it. The generated differential test skips every outcome our engine declines,
  which is the right oracle policy for a construct pcre2 has no opinion about —
  and an internal error wears the same type while meaning the opposite. So a
  disagreement between the analyzer and the checker on a random pattern would
  have passed as a skip. When a change adds an outcome, look at what already
  swallows outcomes.
- Wrote the certificate into the compiled pattern only on success, in a
  function whose result is the caller's to reuse. Every other field of `Re` is
  written unconditionally, so a caller compiling a second pattern into the same
  result would have got the second pattern's bytecode with the first pattern's
  bound — the exact pairing the availability flag was added to prevent, arrived
  at by leaving the flag alone rather than by setting it wrongly. A field that
  means "this is about the value beside it" has to be written on every path
  that writes the value.
- Wrote down that a skip had hidden the new failure mode, fixed the sweep I had
  just read, and left the same skip in three other places: two more differential
  sweeps, and the helper my own new "priced or refused" tests are built on,
  which drops every pattern that does not compile — an internal error included.
  So the test whose docstring says it exists to catch the analyzer and the
  checker disagreeing could not have caught it. Writing a mistake down is not
  the fix; finding every instance of it is, and the search is the same one
  either way.
- Ran the checker only where there was a certificate to check. The checker
  answers two different questions — does this tree describe this program, and
  does this certificate bound it — and only the second one needs a certificate.
  Gating both on the analyzer succeeding meant a compiler that emitted a bad
  tree went unreported for exactly the patterns the analyzer gives up on, which
  is the worst possible correlation: the shapes hardest to price are the ones
  most likely to be compiled wrongly. When one function answers two questions,
  look at what each of them actually depends on before deciding when to call it.
- Split the checker in two and moved the easy half. The topology rules were the
  ones that read as generic, so those went into `cert_shape` and the rules that
  say what a region kind means stayed behind in the pricing walk — where they
  were still gated on the analyzer having produced something. The fix looked
  like the fix and closed about a third of the hole. When extracting a concern,
  the test is not "does this code look like the concern" but "is anything left
  behind that has the same dependencies".
- Wrote the invariant as "either CrOk or the verdict", which a function that
  returned CrOk for everything satisfies. An invariant with an escape hatch for
  the failure mode is not an invariant; the corpus records which half answered
  each case, and the relation that decides it is checked where the file is
  written.
- Derived which half of the checker answered a case from the name of the
  verdict, when one of the names means two things: `CrShape` is a program the
  checker cannot read, and it is also a certificate field naming no variant of
  its enum. The derivation was right for every case that exists and would have
  been wrong for the first one that did not. A classification computed from a
  value is only as good as that value's injectivity, and an enum whose
  description contains the word "or" is where to look first.
- Renamed the project inside the LOG.md entry that records how the name was
  chosen, turning "fifty candidate names to replace pcre-truste" into a search
  to replace pcre-vera with itself. A journal entry about a change is one of the
  few places where the old name is the correct name, and a global sweep cannot
  tell the difference between a reference to a thing and a mention of what it
  used to be called. Before running a rename over prose, look for the sentences
  whose subject is the rename.

## The accessors and the Pike VM (M5)

- Typed Go's MatchConfig as uint32, the exact width the engine takes, so a
  caller's conversion of an out-of-range value wrapped it into the valid
  default instead of being refused — while Python and JavaScript rejected the
  same value as BadInput. The start offset had already solved this the right
  way, an `int` validated down to u32, and consistency with the sibling
  parameter should have been the first thing checked. A public type as narrow
  as the engine's parameter delegates range validation to the caller's cast,
  which is a silent clamp wearing type safety.
- Designed the first Pike closure around "an empty loop iteration dies at the
  visited set, and the exit was already forked with the captures in hand".
  Wrong: the preferred empty iteration re-executes body instructions — its
  Saves included — that the closure already marked, because the thread it
  grows from was suspended mid-body, so the marks kill the path pcre2
  prefers and a lower-priority capture wins. `(a?)*` on "a" says (0,1) where
  the backtracker says (1,1). A pc-keyed visited set is exact for match
  extents but not for captures unless the non-consuming transition graph is
  acyclic; the fix was to make that acyclicity the eligibility rule itself —
  no star whose body can complete emptily — rather than to keep patching the
  closure. The differential test found it on the fourth hand-written case,
  which is why the cross-matcher obligation exists; a design argued only on
  the whiteboard would have shipped it.
- Checked the Pike certificate's stack claim by domination, like the other
  two bounds, when section 9's rule for it is equality with zero: no
  backtrack stack exists on that path, so a certificate claiming entries the
  matcher can never push dominated the requirement trivially and was
  accepted, letting an accessor report a requirement nothing has. When a
  rule says "exactly", transcribing it with the comparison every neighboring
  rule uses is how "at least" sneaks in; the corpus case that would have
  caught it — a mutation upward, not downward — did not exist because every
  existing mutation case was about claiming too little.
- Pinned the independent Pike restatement to one exact case, a literal with
  no captures and no Saves, so two of the closed form's four counts were
  multiplied by zero in the only place the restatement was compared. An
  independent restatement earns its keep exactly on the inputs where every
  term bites.
- Transcribed the whole-call stack equation as a domination, like cost and
  memory beside it, so the checker accepted a certificate whose stack claim
  floated free of the memory requirement priced from the derived number —
  harmless while the claim was only ever compared against limits, and a
  sizing hazard the moment a context would allocate an array from it. A
  bound that something will be *sized* from is not a bound, it is a
  dimension, and dimensions are equalities. Caught in design review of the
  context plan, before any context existed to inherit it.
- Patched the global typed-array constructors to count what a context match
  constructs, and broke the wrapper's own `instanceof Uint8Array` check for
  every subject built before the patch went in: instanceof resolves the
  global at call time too, and an instance of the real class is not an
  instance of a subclass planted over it. Instrumentation that swaps a
  global has to keep the identity questions answering as before, which is
  what `Symbol.hasInstance` delegation is for.
- Left the delivered answer out of the memory bound while writing the
  context's physical-equality contract, then wrote the three physical tests
  against the same under-count, so they proved the reservation equaled a
  number that was itself a result store short of what DESIGN.md defines the
  sum over. A test derived from the implementation's own decomposition
  inherits the decomposition's omissions; the fix was to read the normative
  list of stores again and charge `deliver` to memory the way it was
  already charged to cost.
- Reserved into whatever context the creation destination already held,
  forgetting that reserve never shrinks, so recreating a small context over
  a large one kept the large one's capacities and quietly broke the
  resident-byte equality — invisible through the wrappers, which always
  hand in a fresh destination, and exactly the kind of state a generated
  entry point that accepts any well-typed inout has to reset itself.
- Computed the context reservation a second time instead of asking the
  accessor for it, and never noticed the two numbers part company: creation
  evaluated the certificate's stack and trail claims at the declared length
  and summed real capacities, while `worstCaseMemory` evaluated the memory
  polynomial, and a polynomial with growth carries its constant terms at the
  larger base. On `(a|b){2,}` at a declared maximum of four the accessor said
  77696 bytes and the context held 74456 — safe, since the arrays covered
  every byte a call could touch, but DESIGN.md section 2.4 promises the two
  are the same number and the whole point of that promise is that a caller
  can plan creation from the accessors. Two computations of one quantity
  agree only until an approximation is introduced into one of them; creation
  now calls `re_mem` and the ballast makes up the difference. The generated
  sweep found it on the first population it was pointed at, on a pattern
  nobody would have hand-written into the corpus, which is the argument for
  the sweep in one sentence.
- Ran the limit edges of DESIGN.md section 8 on the selected matcher only,
  on a page that says "on both matchers", and did not notice because the
  cross-matcher check beside it does run both — for semantics. Two checks
  over the same pair of matchers, one of which quietly covers half of what
  it says, is what a review is for; the fix was to make the runner take
  the matcher as an argument so the two askings cannot drift again.
- Recorded the backtracking bound as a "priced" boolean rather than as the
  numbers, so the cross-matcher record pinned only whether the bound was
  sufficient, not what it was. The public accessors answer for the
  selected path, so nothing else in the sweep would have caught a
  backtracking analyzer that drifted inside the limits both the old and
  the new bound allow. A recorded flag derived from a number is worth
  less than the number.
- Wrote that the population's first forty-five cases cross every option
  family with every convention when the product is sixty-six, and wrote
  the test over a population of five hundred, which passed without ever
  looking at the prefix the sentence was about. A test whose input is
  bigger than the claim does not test the claim.
- Let `make sweep` exit zero on a run whose completion gate was not
  cleared. An evidence gate that only prints is a gate nobody has to pass.
- Named a promoted corpus case after the seed and index alone, when a case
  can fail in more than one way and a failure document can hold two records
  for it. The corpus loader refuses a duplicate name, so the promotion
  would have reported success and left the file unloadable. The name now
  carries the disagreement class, and promotion refuses a name the corpus
  already has before writing anything rather than after.
- Promoted every class of sweep failure into the wave 1 corpus, which only
  asks what an answer is. A bound violation, a limit edge, a context or a
  cross-matcher disagreement filed there is a case that compiles and matches
  correctly and says nothing at all about the invariant it was found by —
  a regression test that guards nothing is worse than none, because it
  reports the bug as covered. Promotion dispatches by class now, and the
  invariant cases are replayed through the whole battery instead.
- Let the reducer keep a subject on a compile disagreement, because delta
  debugging stops at one element and nothing tried the empty list. The
  promoted case then became a match case for a compile bug. When a
  dimension's zero is meaningful, the shrink has to offer it explicitly.
- Dropped declined cases from the sweep record, reasoning that pcre2 has no
  opinion about them. It does not, and the other two implementations of our
  own engine still have to refuse the same pattern with the same code at the
  same offset — thirty-one cases of a campaign that never reached Go or
  JavaScript, in a harness whose whole claim is four implementations per
  case. "The oracle cannot answer this" is not "nobody can".
- Wrote that a case is a function of its seed and its index when the subject
  count and the structured-population size are part of it too — which the
  replay command had always carried, so the code was right and four
  documents were wrong.
- Drew the population from `random`, whose seeding is stable but whose
  shuffle and range algorithms are CPython's to change, and then wrote the
  resulting manifest hash into a freeze record. A number that names an
  artifact forever cannot be computed by something that only promises to
  behave the same today.
- Wrote a rejection rule for the owned generator that counted its tail over
  the largest value rather than over the sample space, making residue zero
  one draw in 2^64 more likely than the others while the docstring said
  unbiased. The bias is unobservable and the wrong claim is not: an
  off-by-one that only an equation can see needs a test that asks the
  equation, not a histogram.
- Made the sweep's regression section mandatory and non-empty in both
  generated runners, so a repository that had not yet found an invariant
  failure could not replay its own shard. A facility has to work on the day
  it is added, with nothing in it.
- Promoted an invariant regression on the strength of a compile-and-match
  comparison with pcre2, which is exactly the check a bound violation, a
  limit edge or a context reservation survives. A promotion has to run the
  battery the case was found by, not the one the corpus it lands in
  happens to use — and running it also lets a case whose right answer is a
  decline be promoted, since the oracle policy lives in the battery.
- Kept the sweep's budget out of the failure record, so a reducer shrank
  under the default limits whatever the run had used. A ResourceExceeded is
  a decline under one budget and a finding under another, so that is
  shrinking towards a different failure than the one that was found.
- Recorded the kept regressions under the default budget while inserting
  them into a result document whose runners apply that document's budget.
  Two numbers for the same run, and only one of them written down.
- Asserted that a context call reports the reservation as its memory, and
  that it answers what the plain call answered, without excluding the call
  the context refuses: a subject past the declared maximum never begins, so
  it reports nothing and owes a BadInput rather than an agreement. No
  generated case can have one — the declared maximum is the longest subject
  — which is why only a hand-written regression found it.
- Let the generated runners read the decline contract off the record: a
  declined case with no offset was replayed as a case that never had one,
  so deleting the offset of an unsupported-construct record passed. Which
  refusals carry an offset is a contract, and a runner that takes it from
  the file it is checking has stopped checking that part of the file.
- Stored a promoted regression without the budget and edge count its
  failure was found under, then reran it under whichever document it was
  riding in. A regression found only under a custom limit is a regression
  only under that limit; the conditions are part of the case, not of
  whoever replays it.
- Decoded the sweep's regression section into a Go slice, which cannot tell
  a key that was absent from a list that was empty, so deleting the section
  from a document made the runner replay nothing and say nothing. The
  contract was "present but possibly empty" and half of it was
  unrepresentable in the type chosen for it; a pointer says both.
- Called the cross-backend figure a count of recorded numbers in three
  places after making it count every leaf, which includes the name of a
  compile outcome and the flag that marks an edged trial. A count is
  described by what it counts.

## Assessing the email pattern's cost bound

Mistakes made while answering why WorstCaseCost reports 48.9 billion for
`(?<user>\w+)@(?<host>[\w.]+)` at length 1000, all in the assessment rather
than in code:

- Described the cost unit as instruction visits. The unit also charges byte
  comparisons and every IR byte initialized, zeroed or copied by scratch
  management, and it has no numeric relationship to pcre2's counters at all;
  the section 5 cost model is DESIGN.md's, not pcre2's.
- Reported the bound as "~48.9·(n+1)³" by dividing the evaluated value at one
  length by (n+1)³. The certificate is the exact polynomial
  3448 + 2898·(n+1) + 764·(n+1)² + 48·(n+1)³ — the leading coefficient is 48,
  and 48.9 billion is the whole polynomial evaluated at 1000. A ratio at one
  point is not a coefficient.
- Claimed M9 memoization would improve the constants of backtracking-only
  patterns. DESIGN.md restricts the memoized configuration to Pike-eligible
  patterns and rejects it as BadInput elsewhere, so it offers nothing to a
  pattern that stays on the backtracking path, and nothing extra to one that
  becomes eligible — the default Pike path already fixes the asymptotics.
- Framed the missing quantifier desugaring as future work the roadmap would
  deliver. No milestone owns it: DESIGN.md 4.3 presents unrolling as how
  counted repetitions already compile, compiler.py says it does not do that,
  and README declares M5 done with the artifact frozen. That is a
  design/implementation discrepancy inside a milestone claimed complete, not
  a scheduled gap, and calling it "will be fixed later" understated it.
- Estimated the Pike-path cost for this pattern at "tens of thousands"; the
  eligible spelling measures 201,330 at length 1000 — low hundreds of
  thousands.
- Proposed sharpening the stack composition alone to fix the quadratic
  memory reservation. WorstCaseMemory is priced from the stack and the undo
  trail capacities together, so a live-versus-peak refinement would have to
  cover the trail as well or the reservation stays quadratic.

## RefineProto (S-8 prototype)

- Reached for `set` and `conv_lhs` out of Mathlib habit; this project is
  batteries-only and neither exists here. Recorded in api-faq.md.
- Wrote `altOut`'s patched jump target as `stM.code.size + 1` expecting it
  to be definitionally the size of the pushed array; `(a.push x).size`
  does not reduce on an abstract array, so the `rfl` characterization of
  `compileAlt`'s cons step failed until the statement spelled the push.
- First statement of the fragment lemma read "running the fragment with an
  empty stack yields the enumeration or nomatch", which is wrong for empty
  fragments (`cat []` falls through to the continuation, it does not
  fail); the fix — threading an ambient stack and treating the exit pc as
  the continuation — is the formulation that ended up load-bearing.
- The module overview initially said a completed `btStep` "equals" the
  mirror; it refines it (the metered side can stop early), and the review
  caught the overclaim.
## Monotone (S-9)

- Reached for `Option.noConfusion h` to kill constructor-clash equations in
  the S-9 proofs; its universe metavariables do not elaborate from an
  `Eq Prop` argument alone, and plain `cases h` was the right tool.
- Scripted the `circM`/`dollM` arms like the other assertions. Their test
  is itself an if-expression, so `split at h` decides the inner condition
  first and the one-split script bound the wrong hypothesis; both matchers
  needed a two-level case.
- Assumed `pikeRun`'s `let (st, mh, ended) :=` destructuring compiles to a
  tuple match. Single-constructor structures destructure into projections,
  so the split lands on `match (...).2.snd` and the loop lemma had to be
  restated over the whole answer triple (`pikeLoop_mono_end`).
- Added `rw [hcc] at hs ⊢` after `rcases hcc : ctxCreate ... with ⟨cst, octx⟩`;
  rcases had already generalized the scrutinee in the goal (though not in
  `hs`), so the rewrite found nothing there.
- Assumed `split` on a match introduces only the per-arm equation. It also
  generalizes the scrutinee into a fresh inaccessible variable, so the
  `rename_i` slots in the `pikeAdd_go_congr` closers were off by one per
  nested match until the traced context showed the extra `POut PikeSt`
  binders.
- Expected `rw [getElem!_neg ...]` to close `default.op = Op.chr` by its
  trailing rfl. The rewrite's rfl check does not unfold the derived
  `Inhabited` instance; an explicit `rfl` afterwards does.

## Lean, S-8 backtracking round

- Assumed `repCount (.cat []) = 0` was `rfl`. Definitions that use
  `List.attach` for termination compile by well-founded recursion, so
  nothing unfolds definitionally; `rw [repCount]` works, and on the
  catch-all arm it leaves one "no earlier pattern matches" goal per
  skipped pattern, which `simp` discharges.
- Spelled the compiled high bound as an inline `match hi with | some h => h
  | none => none32` in the `FragAt` constructor and again in a `have`. The
  two elaborate to different matchers — the second generalizes every
  context hypothesis that mentions `hi` — so the constructor's field no
  longer typechecked against it. Naming the function (`hiCode`) ended the
  problem.
- Expected `simp` to close `Resumes … ↔ Resumes …` once both sides
  normalized to the same printed term. What was left was the `Decidable`
  instance inside an `ite` whose condition simp had rewritten
  (`decide (pos < s.size) = true` against `pos < s.size`), and instances do
  not print. Reading the enumeration's answer through a defeq type
  ascription before the case split avoids the mismatch entirely.
- Ran `split at h` on an `if` sitting inside `match some st2 with …`. The
  branches mention the match-bound variable, so the rewrite cannot abstract
  them and the pattern is reported as not found; `simp only [] at h`
  iota-reduces the match first, and then the `if` is rewritable.
- Fed `omega` a hypothesis about `(mctx re s mo).s.size` while the goal
  spoke of `s.size`. They are definitionally equal and omega treats each as
  its own atom; a one-line `have` at the wanted type is the fix.
- Reached for `getBang_set_eq` on a goal spelled with `Array.set!`. The
  helpers are stated over `Array.setIfInBounds`, so
  `rw [Array.set!_eq_setIfInBounds]` has to come first.

## The Lean model's out-of-range read (M6)

While proving the per-attempt bound, the backtracking-bounds work found that
`cert_shape` never asks whether a program contains an `Accept`. A straight-line
region of tests with none walks off the end of its own code, and the two sides
of that walk differ: TIR's checked indexing traps (TIR-SPEC.md T-01), while the
Lean reference reads `getElem!`'s default instruction and charges for it. The
per-attempt bound is false for such a program in the model.

No pattern can produce one — `generate` always emits the trailing `Accept`, so
every compiled program has one — and the bound theorems carry the existence of
an `Accept` as an explicit hypothesis rather than assume it away. What the
episode is worth recording for is the shape of the mistake it nearly caused: a
total-by-default read is not the same failure as a trap, and a model that
answers where the engine stops will happily prove something about a program
neither of them can run.

## Reading the Pike eligibility flags back (M6)

Four things went wrong on the first pass at `PikeRefine.lean`, all of them
about *where* a fact lives rather than whether it is true.

- Wrote `PikeShape` so that a `{0,0}` repetition constrained its body. The
  compiler emits nothing at all for that form, so the fragment relation has
  no body derivation to induct on and the clause is unprovable — and it is
  also unwanted, since the specification never looks at that body either.
  The predicate now says nothing about it.
- Asked `pikeOk_rep` for a bounded high and then tried to conclude
  `hi = none` by `omega` on `RepInfo.hi ⟨…⟩ = none32`. `rw [hinfo]` leaves
  a projection applied to a literal record, which `omega` treats as an
  opaque atom; restating it at the wanted type with a `have` fixes it.
- Split `pikeHollow.go`'s opcode match with `split` and then expected
  `rfl` to close each branch. The left-hand side reduces, the right-hand
  side is still a match on the same scrutinee, so the branch equation has
  to be rewritten in before anything is definitional.
- Rewrote the run hypothesis guard by guard and then had to undo the
  rewrites to apply the step lemma. Two small step lemmas — one for a fresh
  pc, one for a pc already marked — say the whole iteration in one rewrite
  and the invariant proof reads straight through.

## Lean, PikeBounds round 3

- Assumed the backtracking side's `chargeGrow_doubles` argument would carry
  to the Pike arrays. It does not: it says the declared maximum is out of
  reach because no memory limit could pay for an array that large, and
  `maxThreads * thSize` is 525600 against a ceiling of 2^31 - 1. The Pike
  no-clamp fact has to come from the arrays' own entry bounds instead.
- Read `Owned.size_le` as a bound on the pool. It is not one on its own —
  `rc.size ≤ free.size + live.length` is nearly an identity, since the free
  list is itself only bounded by the table. The bound is about where the
  table grows, so the fact belongs on `pikeTake` and not on the invariant.
- Wrote a record update as `{ st with m := mm, poolCap := cap,` and put the
  remaining field on the next line at the indentation of `st`. Structure
  instance fields are parsed at the column of the first one, so the parser
  stopped at the comma and asked for a `}`. Breaking the line right after
  `with` is the habit that always works.
- Wrote `(Charged.idle …).mono (by omega)`. The receiver of a projection is
  elaborated without the expected type, so the `rfl` proving
  `st'.reserved = st.reserved` unified `st'` with `st` instead of with the
  goal's state. `refine Charged.mono (Charged.idle ?_ rfl rfl h) (by omega)`
  fixes it, and the same reordering fixes a hypothesis order that pins an
  implicit state from the wrong argument.
- Used `subst hxh` on `hxh : x = h` where `h` was the theorem's parameter
  and `x` the freshly introduced index. `subst` eliminated `h`, so every
  later mention of it was an unknown identifier. `rw [hxh]` keeps both.
- Gave every growth wrapper the headroom hypotheses of all the arrays it
  might touch. A park into `nlist` then needed room in the untouched
  `clist`, and a take off the free list needed the room only the fresh path
  wants — so the lemma is unusable exactly when the other array is at its
  bound. Each hypothesis belongs behind the branch test that reaches the
  growth: `if intoNext then nlist else clist`, `free.size = 0 → …`.
- Wrote `pikeDrop_owned` so that the handle is in the live list, and forgot
  that `stepThreads` drops the match sentinel before it has a match. The
  wrapper's hypothesis makes `none32` impossible, so the one call the VM
  really makes was the one it could not cover; the sentinel needs a no-op
  lemma of its own.

## Reading the closure loop against its own step relation (M6)

- Guarded the 24 opcode branches of `pike_add` with
  `exact absurd hok (by simp)` inside a `first` chain. The nested `by`
  logs its failure instead of failing the alternative, so every ok-branch
  reported an unsolved goal. A named lemma applied as a plain term is what
  makes a `first` chain behave.
- Stated `epsTargets` for `repLoop`/`repNext` as `[body, after]`
  regardless of greediness. Harmless for reachability, wrong for the
  preference order the same list has to carry later; fixed before anything
  depended on it.
- Wrote the empty-iteration path out of a `repNext` as a step to the
  repetition's *body* rather than to its *exit*. The path being built is
  the one that leaves the loop, not the one that goes round again.

## Reading the capture pool (M6)

- Stated the copy-loop lemma without a room hypothesis on the destination
  block. A write past the end of an array is a no-op here and reads back
  as the default, so the clause was simply false; the fold needs to know
  the pool has room for the block it is filling.
- Bundled the copy loop's size clause with its content clauses. The
  content clauses need the room hypothesis, the room hypothesis is stated
  in terms of the size, and the knot only comes undone if the size is its
  own lemma.
- Fed `omega` a bound stated over `st.pool.size` while the goal spoke of
  the same field of a record that differed from `st` only in the meter.
  They are definitionally equal and omega atomizes each separately; a
  restating `have` at the wanted type is the fix, and this is the second
  time the same shape has cost a debugging round.
- Reached for `pikeAdd_go_build` as the template for a second walk over the
  closure's dispatch. `pikeAdd_go_congr` is the better one: a `repeat'
  split` with one alternative per arm *shape* rather than a case per opcode,
  and its out-of-range argument — a pc the program does not have reads as
  the default `chr`, which parks and pushes nothing — means the walk needs
  no pc-range hypothesis at all, so `BuildOk` never has to be re-derived.
- Discriminated the refusal arms of that dispatch with `exact absurd h (by
  simp)` at the head of a `first`. A `by` block inside a term is elaborated
  after the alternative has already been accepted, so `first` never backs
  out and every real arm was reported as an unsolved `¬ … = .ok …`. The
  refusal arm belongs last, where `cases h` fires only once the shape-matched
  alternatives have each failed on `h`'s type.
- Read `Owned.size_le` as the pool's bound a second time, in the shape of a
  measure. It only ever says `rc.size ≤ free.size + live.length`; what the
  bound needs is that the table grows solely when the free list is empty,
  which is why the `max` clause sits on `pikeTake` and is threaded from
  there.
- Cut a block out of a file with `s[s.index(start):s.index(end)]` where the
  end marker was a docstring opening that also occurs earlier in the file.
  The slice came back empty and every replacement inside it silently found
  nothing. Searching for the end marker *from* the start index is the fix,
  and asserting the expected occurrence count is what caught it.

## Rebuilding what a neighbour had already built (M6)

Started a pool-size invariant and its closure-loop induction in
`PikeRefine.lean` while `PikeBounds.lean` was growing the same clause into
`Owned`. The neighbouring file was mid-edit and red at the time, which is
exactly when it is tempting to work around it rather than read it. Reading
it first would have saved the round: the answer was one field on a
structure that already travels through every helper.

## The fork account (BtBounds round seven)

- Put the docstring above `set_option maxHeartbeats … in` rather than below
  it, twice in the same session. Lean wants the attribute first and the
  docstring immediately before the declaration; the parse error names the
  `set_option` token and reads as if the previous declaration were
  unfinished.
- Scripted a docstring pass that keyed on an existing doc comment, so the
  new one landed above the old one and left two in a row. Keying on the
  declaration line is the only safe anchor.
- Assumed `split at h` takes the outermost `if` and named the resulting
  hypotheses positionally with a chain of `rename_i`. On `shape_alt`'s
  nested chain it took an inner one first, so every name in the chain was
  about the wrong condition and the failure surfaced several tactics later
  as a `decide` complaining about free variables. Driving the unfolding with
  `by_cases` and `rw [if_pos …] / rw [if_neg …]` is deterministic, and
  pulling it out as `shapeAltGo_step` turned out to be worth having on its
  own — the code layout a shape walk settled is a fact worth stating once.
- Reached for `Array` push/pop reasoning by hand before looking:
  `Array.eq_push_pop_back!_of_size_ne_zero` is already there and is all the
  `owed` bookkeeping needs.
- Unfolded `addMeasure` in a goal with `simp only [addMeasure, …]` while the
  hypothesis bounding it kept `addMeasure` folded. omega then had two
  unrelated atoms and no way between them. Proving `addMeasure … = addMeasure
  …` as a `have` and rewriting keeps one atom throughout, and reads better.
- Wrote `rw [h₁, h₂] at hyp ⊢` where one of the rewrites only applies to the
  goal. `rw … at` fails outright when a pattern is missing from *any* of its
  targets, so the two have to be separate.

## Alternation and the optional item (BtBounds round eight)

- Put the docstring above `set_option … in` for the third session running,
  and had to write the same scripted swap twice more. It is now in
  api-faq.md with the error message it produces, which is what I should
  have looked for the first time.
- Trusted `split at h` to take the outermost `if` again, this time on
  `shape_alt`'s nested chain and on `cert_shape`'s dispatch. It does not,
  and the failure surfaces several tactics later as a `decide` complaining
  about free variables. Both places are now driven by `by_cases` and
  `rw [if_pos …] / rw [if_neg …]`, or by `cases hk : …` on the scrutinee.
- Wrote `cases hk : (re.regions[i]!).kind` and then `rw [hk] at h ⊢`. The
  `cases` has already substituted in the goal; only the hypothesis needs
  rewriting, and the goal's rewrite fails with "did not find an occurrence".
- Specialised `certCheckRegions_step` to an incoming flag of `false` and
  left the old closing tactic `rw [← hv, ← hover]` in place. With the flag a
  literal rather than a variable, `← hover` rewrote the *incoming* `false`
  instead of the outgoing one. A tiny `triple_eq` lemma — a triple read back
  off its own components — closes it without depending on rewrite order.
- Reached for `by_contra`, which this toolchain does not have. `rcases
  Nat.lt_or_ge …` or deriving the positivity from a hypothesis already in
  scope is the local idiom.

## The Pike counter invariant (PikeRefine, dedup round)

- Took the previous round's own note at its word — that the guard for the
  counter should be the one `EntryFresh` uses, "this row's `repNext` is still
  reachable without consuming" — and started building the invariant around
  it. It is vacuous exactly where the counter is read: from a deciding head
  the only non-consuming way back to that row's `repNext` runs through the
  body, and eligibility is precisely the fact that it does not. The guard has
  to be structural containment, `head ≤ pc < after`, which is what turned the
  reachability question into an address one and produced `FragAt.noMidEntry`.
- Wrote the invariant as "the count is not the unset sentinel" before
  noticing that `repNext` bumps it, so a count one below the sentinel would
  walk into it. Only a bound relating the count to the position survives the
  bump, and getting the bump strict is what pulls `EntryPast` and
  `EntryFresh` into a lemma that looks like it should only need the count.
- Assumed a fragment's edges were the whole story and would also settle where
  the repetition cells stand. They are two different inductions over the same
  relation — `FragAt.targets` reads what a construct defers to,
  `FragAt.cells` reads what it pins — and only the second discharges
  `CellsOk`.
- Left `hlt` in `count_stay`'s signature out of symmetry with its neighbour;
  the containment conclusion never uses it, and the unused-variable linter
  said so.

## The per-position account (PikeBounds round eight)

- Planned to price every mark as if it could force a copy-on-write, which
  would have bounded a position's copies by `C`. The certificate says `S`,
  the `Save` count, so the measure has to be weighted by the opcode at the
  pc being marked. Reading the price back off BOUNDS.md before writing the
  measure would have caught it; reading it off the Lean statement did not,
  because `(S + 2) * B` looks the same as `(C + 2) * B` until you ask which
  is which.
- Assumed `Charged … st out` survives replacing `st` by a state that differs
  only in a field the reading never looks at. It does not: `Charged` is a
  structure, so the two are different types and unification compares the
  states field by field. `Charged.ofState` transports it across a state with
  the same meter and the same capacities, and is needed exactly once, where
  the closure pops its worklist before dropping a handle.
- Gave an arm helper a hypothesis list beginning with `stA.stk.size ≤
  st.stk.size`, which is provable with `stA := st`. The elaborator obligingly
  picked `st` and every later argument then failed to typecheck. Putting the
  `Charged … st stA` hypothesis first pins the state before anything else is
  read.
- Wrote a structure instance as `{ st with stk := …, seen := …, m := … }`
  with the continuation lines indented less than the first field. Structure
  instance fields are column sensitive: the parser stops at the first token
  left of the first field and reports `unexpected identifier; expected '}'`
  at the end of the previous line, which reads as if the field value were at
  fault. Putting `{ st with` on its own line and the fields under it is the
  form that always works.
- Used `simp only [hop]` where the only work being done was reducing a match
  whose scrutinee `cases hop :` had already replaced by a constructor. The
  lemma was doing nothing, the unused-simp-arg linter said so, and `dsimp
  only` is the tactic that means what was meant.
- Wrote `.mono (by omega)` on a term whose target bound was still a
  metavariable when the `by` block ran. `refine … ?_` puts the side goal
  after unification, where the bound is known.
- Expected `rw` to close `1 + x ≤ 1 + x`. It tries `rfl` for `Eq` and `Iff`
  only; an order goal needs `omega` or `Nat.le_refl` after it.

## The closure's ordering (PikeRefine, correspondence round)

- Called `epsReach_antisymm` "no closure walk comes back where it started" in
  three places. Antisymmetry is not that: `EpsReach` is reflexive, so a
  non-empty walk from a pc back to itself pairs with `refl` and the theorem
  concludes only `a = a`. The fact the priority argument actually needs is
  `epsReach_no_cycle` — one step out and no way back — and the ingredients
  were already there, so the claim was ahead of the proof by one lemma.
  Caught in review, which is where a statement written as prose first and
  proved second usually gets caught.
- Planned the thread-list correspondence around decoding a pool block into
  the mirror's register file before noticing the two are not the same width:
  `pike_add` keeps no repetition counters, so a block is `novec` slots where
  the mirror's file is `novec + 2 * reps.size`. Read as a mirror file a block
  would answer zero for every counter, and at position zero a `repNext` would
  take the empty-match exit the closure never takes. The correspondence is
  `Agree novec`, and `Fit` belongs on the mirror's side.

## A check that was never reached (M6)

The corpus replay cross-checks a bridge skip against the record — the engine
refused this pattern, the record says so too, and the codes agree — so that a
bridge which skipped every case cannot replay nothing and report success. The
check was written inside the per-case runner, and the driver only called that
runner for cases the bridge had *not* skipped. It was dead from the moment it
was written, and a tampered bridge passed.

What caught it was running the tamper rather than reading the code. The lesson
is the ordinary one about guards: a check belongs on the path the thing it
guards against actually takes, and the way to find out which path that is, is
to take it.

## S-10 and R-9(b) for a forking program (BtBounds round nine)

- Passed `_` for the state a step lemma is about and let unification pick
  the enclosing `st` rather than the record the goal was really about. The
  failure reads as an application type mismatch several arguments later.
  Where the goal names a record, name it in the call too.
- Composed two `Steady`s as `Steady.trans ⟨rfl, rfl, rfl, rfl⟩ h`. The
  anonymous constructor pinned the middle state to `st` before `h` was
  looked at, so the composition had the wrong middle. Naming the middle
  state in a `have` first is the fix, and the same trap applies to any
  transitivity lemma whose middle is implicit.
- Dropped a `have hpopT := owed_pop T hne` while transcribing the pop
  bookkeeping from one induction to the next. Nothing complained until an
  `omega` several arguments away came back with a counterexample about
  `owed T`; the missing fact is always the one whose atom appears in the
  counterexample with no relation to anything.
- Wrote `simp only [regSize] at hcost ⊢` and forgot that the branch
  hypothesis `split` had just introduced still carried `regSize`
  unexpanded, so omega saw `(a - b) * regSize` and `4 * (…)` as unrelated
  atoms. Name the branch hypothesis with `rename_i` and simp it too.
- Kept copy-pasting `dsimp only;` from the `Within` proof into the budget
  and steady proofs, where the state was already a variable and there was
  nothing to reduce. "dsimp made no progress" is an error, not a warning.

## Closing the per-position account (PikeBounds round nine)

- Wrote the arms of `stepThreads_spent` before the `simp only [stepThreads]`
  and the split on its charge test, so the dispatch below was working on the
  unreduced call and every `split` failed with "could not split". The error
  points at the split, not at the missing unfold, and the goal it prints is
  the one from before the `have` block — which is the tell.
- Assumed `cases hop : e <;> simp only [hop]` was doing the rewriting. It is
  mostly doing iota reduction, and which of the two is needed differs per
  opcode: `first | dsimp only | simp only [hop] | skip` covers both and
  leaves the unused-simp-arg linter quiet.
- Passed `_` for a universally quantified state and let the elaborator pick
  it from the first hypothesis that mentioned it, twice more. When the
  hypothesis is `stA.stk.size ≤ st.stk.size` the wrong state satisfies it.
- Let two hypotheses about the same state disagree on whether a structure
  instance had been zeta-reduced: `Charged … (let __src := {}; {…}) …` and
  `Charged … {…} …` are the same proposition and different omega atoms. The
  fix that always works is to quantify the state, prove the step about the
  bound variable, and let `refine` unify it with whatever the goal holds.
- Reached for `simp only [Nat.max_le]` on `x ≤ max a b`. That lemma is about
  `max a b ≤ c`; omega handles `max` on either side without help.
- Unfolded `addMeasure` in one hypothesis and left it folded in the other,
  again, this time inside a `have` that only needed the folded form. The
  entry from round seven of BtBounds says exactly this.

## The attempt reading (PikeBounds round ten)

- Estimated the round as "mostly mechanical" and sized only the new
  mathematics. The mathematics was one lemma; the threading is four large
  inductions and was the whole cost. The honest reading of "mechanical" is
  "no new ideas", not "small".
- Wrote a structure instance across lines with commas for the third time in
  two rounds. The entry from the previous round says exactly this. Putting
  `{ st with` on its own line is not a style preference, it is the only
  layout that parses when the fields wrap.
- Passed `hrooms.stk` to `chargeGrow_refused` out of habit, having just
  written the lemma without that hypothesis — the capacity bound follows from
  `oldcap ≤ len < claim` alone. The error surfaces as `rcases failed: not an
  inductive datatype` two lines later, because the misplaced argument shifts
  everything after it.

## The closure invariant (PikeRefine, block-stability round)

- Wrote down "a marked pc stands for a segment of the parked prefix" as the
  closure invariant twice, in two rounds of prose, before working out that it
  is not inductive. Marking pushes the expansion onto the worklist; it
  reaches the parked list only as the stack above a later duplicate drains.
  The invariant has to be about the stack's shape — a complete segment above
  every marked entry — and that is where the acyclicity is actually spent.
  Prose that names an invariant is cheap; checking that it survives the step
  that establishes it is the part worth doing first.

## The threading (PikeBounds round eleven)

- Picked the shape of the loop's refusal conjunct before doing the run-level
  arithmetic it has to survive. A plain `Blown` at the price of the positions
  covered is provable everywhere and is short by one `closureLeftFull` at the
  cash-out whenever the scan starts at offset zero, which is the ordinary
  case. The tight form needs to know that the last position's step marks
  nothing, and that cost a whole extra reading (`BlownFlat`) and a second
  induction (`stepThreads_last`). Deriving the final inequality first would
  have found it in ten minutes rather than in the middle of the fourth
  induction.
- Assumed the fuel premise the previous round identified was the only one.
  `pike_loop`'s step count is a variant too, and its base case answers
  `exceeded` outright, so the refusal conjunct is false there without
  `s.size + 1 - pos < steps`. The tell is that the base case of the first
  reading was provable and the base case of the second one was not.
- Reached for `Rooms.zero rfl rfl rfl rfl rfl rfl` to get `Rooms re st` for a
  state that had inherited its capacities from another. `Rooms.zero` wants
  every capacity to be zero; the anonymous constructor over the six
  projections of the state's own `Rooms` is what carries them across.
- Wrote `exact by decide` for `⟨Outcome.noMatch, …⟩.outcome ≠
  .resourceExceeded`. It works while the record is closed and fails the
  moment the record mentions a local — see api-faq.md.

## The closure correspondence (PikeRefine, induction round)

- Typed a Cyrillic `e` into an identifier and spent two builds on "expected
  token" pointing at a column in the middle of what reads as an ordinary name.
  The message is right and the eye is wrong: "expected token" inside a plain
  identifier is what a homoglyph looks like.
- Wrote a structure field `∀ q, st.seen[q]! = true → …` without annotating
  `q : Nat`. The index type stays a metavariable, `GetElem?` gets stuck, the
  whole structure fails to elaborate, and every later use then reports
  "unknown identifier" for it. The real error is the first one in the list,
  not the twenty that follow.
- Ran a search-and-replace of `th.pc` across a proof to follow a `subst`, and
  it also hit the line *before* the `subst`, which still needed `th`. Renaming
  across a `subst` boundary is not mechanical.
- Called a lemma whose implicit `start` and `attempt` occur only in its
  conclusion from inside an `obtain`, where there is no expected type to pin
  them. The failure is two stray `⊢ Nat` goals reported at the enclosing
  bullet, nowhere near the call. Name them.
- Assumed `<;> [tac₁; tac₂]` was available for taking a `split`'s two branches
  apart. It is not in this toolchain; write the bullets out, even at the price
  of a repeated block.

## `ReWf` from the compiler (ReWfCompile)

- Reached for `emit` from a new file because `Refine.lean` names it freely.
  It is private to `Compile.lean`, and every use of it elsewhere goes
  through the `open private` line at the top of the file doing the using. A
  three-line probe answered the question in one build, which is cheaper
  than the assumption would have been.
- Wrote a four-field structure literal across three lines with the
  continuations lined up under the term rather than under the first field.
  The parser stops at the first comma and reports `unexpected identifier;
  expected '}'` a line later, and every branch of the enclosing `cases`
  then reports as missing. The trap is already written down in api-faq.md;
  hit it anyway.
- Closed a `Op.repNext = Op.repNext ∧ …` goal with `⟨rfl, h⟩` after the
  `simp only` that produced it had already normalised the equation to
  `True`. The anonymous constructor then wants `trivial`, and the failure
  reads as an application type mismatch between `?a = ?a` and `True`, which
  looks like the wrong lemma rather than like a normalised conjunct.
- Reached for `tauto` to close two dozen small disjunction goals produced
  by one `<;>`. It is not in this toolchain — see api-faq.md.
- Assumed a lemma stated over `re.code` and `re.reps` with `re` implicit
  could not be applied to a `FragAt (compile p).code …` hypothesis, and
  made `re` explicit to avoid the problem. The unifier solves
  `?re.code =?= (compile p).code` by itself; the workaround was free but
  the belief behind it was wrong, and a probe would have said so.

## The merge (PikeRefine, dedup-across-attempts round)

- Applied `eff_accept_give` with every implicit free and a `by omega` for
  its one hypothesis, which constrains nothing. The elaborator guessed
  `attempt := a₂` and `pos := a₁`, and the failure surfaced two lines later
  as a `rw` that could not find its pattern — with the arguments visibly
  permuted in the message, which is the tell.
- Reached for `rw [resumes_cons]` on a goal carrying two copies of it, one
  at `r` and one at `.nomatch`. `rw` instantiates the metavariables from the
  first match and rewrites only that term; `simp only` is what takes both.
- Wrote `List.map_append _ _ _`. It takes no explicit arguments here.

## Re-indexing onto the merge (PikeRefine, currency round)

- Let a bulk edit script abort halfway through its list of replacements. It
  had already mutated the string in memory but had not written the file, so
  the tree was untouched and the build error output was stale — which read
  for a moment like the edits had been applied and done nothing. Collect the
  misses and write once, rather than asserting per replacement.
- Wrote `simp [untag, tagAtt]` for `List.map (Prod.snd ∘ fun e => (a, e)) L =
  L` and left it unsolved: simp composes the two maps and then has no lemma
  for the composition. `Function.comp_def` is the argument that makes it go.

## Section 4.4's fork account (BtBounds, counter-indexed pricing round)

- Followed the previous round's note into a ghost weight list carried beside
  the backtrack stack, and only afterwards noticed that the fold it was there
  to replace does the job by itself if it is written as a recursion that
  replays as it walks down the stack. Each of the three moves — push, record,
  pop — is then one unfolding of the definition, with no auxiliary state and
  no invariant tying it to anything. The note had called that shape "worse";
  it is the cheap one, and reading the VM rather than the note would have said
  so sooner.
- Aimed `rw [replayTrail_id (by omega)]` at a goal with the same function
  nested inside itself. The `by omega` pins no implicit argument, so the
  rewrite hit the outer call — see api-faq.md.
- Wrote `writeReg_owedAt (fun h => Held_mark hheld h) hw`, and the elaborator
  read the state off `hheld` rather than off `hw`, so the two disagreed by one
  `BtSt.tick`. The message blames `hw` and prints the expected type with
  metavariables in it, which is the tell that the implicit was pinned by an
  earlier argument. `(st := BtSt.tick st)` is the fix, four times over.
- Left the `1 ≤ W pc` fact out of the branch where a loose instruction hands
  its failure to the stack. Every other branch gets it from the clause it is
  using; that one uses no clause, so the universally quantified one has to be
  instantiated at the current position on purpose.
- Ran a bulk replacement over two textually identical proof blocks and patched
  the first when the second was meant. Anchoring on the last occurrence, or on
  more context, is the difference between a green build and a puzzling
  "unknown identifier".

## The list step and the seed (PikeRefine, lockstep round)

- Wrote `have htp : tp = pos := hat.2.1` and then `subst htp`, expecting `tp`
  to go. `subst` eliminates the right-hand side when it can, so it ate `pos`
  — a variable bound in the theorem's own signature — and every later mention
  of `pos` became an unknown identifier several hundred lines away. Reversing
  the equation is the whole fix, but the error points at the use, not at the
  `subst`.
- Renamed a variable inside a proof with a bulk textual replacement and hit
  the `obtain ⟨a, pcx, t⟩` binder along with the uses, producing a binder
  literally named `th.pc`. That elaborates — it is a legal hierarchical name —
  and shadows the projection, so the failure is a type mismatch on
  `hat.left : … = th.pc` rather than a syntax error. Rename by hand, or
  exclude binder lines.
- Modelled "two moves that differ only in the file they carry" as an
  `inductive` indexed by two `Eff`s and then tried to `cases` a hypothesis
  whose indices were both `eff …` applications. Dependent elimination cannot
  abstract those. A plain `def` by match on the pair, read off with four small
  lemmas that each `revert` and `cases` the concrete side, is what goes
  through.
- Attached the accept arm's ownership reasoning to `st` when the machine had
  already charged the meter, so the write was really on `{ st with m := … }`.
  The neighbouring `stepThreads_owned` had already solved this: quantify the
  arm over its own intermediate state and take the field equations as `rfl` at
  the call site. Reading the file next door before writing the same proof
  again would have saved a rewrite.
- Left `rw [fst_of_tagAtt hy]` closing a goal that became `a ≤ a`. `rw`'s
  trailing `rfl` only fires on `Eq` and `Iff`, so an order goal is left open
  and the message is a bare "unsolved goals" with nothing obviously wrong in
  it. `Nat.le_of_eq` on the equation is the honest form.

## Section 4.4's measure (BtBounds, nesting-order round)

- Reported that region index order is not a containment order, with a
  breadth-first numbering as the counterexample: root, then two children A and
  B, then A's child C, so C outranks B while sitting inside A which precedes
  B. The counterexample is real and irrelevant — B and C are *disjoint*, and
  the measure needs an order only between a region and the regions inside it.
  Containment among regions is ancestry, because `cert_shape` nests the ranges
  and forbids siblings from overlapping, and every parent has a smaller index
  than its child. I had compared code order against containment and concluded
  something about index order.
- Chased the `RepZero` case of the measure for a while before noticing that
  the flag it needs is `pc ≤ r.lo` rather than `pc < r.lo`. With the strict
  form the flag has already fallen by the time the `RepZero` runs, so the
  counter reset is unpaid for; with the non-strict one the flag falls *at* the
  reset, which is what makes entering a repetition payable exactly once.
- Wrote `intro -` and `rw [Nat.mul_add] at h` — see api-faq.md for both.

## Two checker rules that are not there (M6)

Proving the resource bounds turned up two rules `cert_shape` could enforce and
does not. A program with no `Accept` walks off the end of its own code, and a
`Save` naming a counter register moves that counter with nothing to account for
it. Neither is reachable from the parser — `generate` emits the trailing
`Accept`, and a `Save` is emitted only for a numbered group — so both live in
the proofs as standing hypotheses, and both are written down in THEOREMS.md
rather than added to the checker, since adding them would move the artifact the
milestone froze.

What they are worth recording for is the pattern. A checker written to refuse
what an analyzer might get wrong will not, on its own, refuse what a *program*
might be; the two are different questions, and it is the proof that asks the
second one.

## Reading `scan_repeat` (BtBounds, flow-bridge round)

- Reached for `simp only [scanRepeat] at h` to expose the checker's counted
  arm, and for `dsimp only at h` followed by `split at h` when that timed out.
  Both fail for reasons the messages do not name — see api-faq.md. The shape
  that works on functions like this is already in the file twice, in
  `chargeCall_dom` and `chargeGrow_unfold`, and reading them first would have
  saved the two attempts.
- Set out to prove the whole of `scan_repeat`'s reading in one theorem and had
  to stop at the flag chain. The half that is arithmetic — that the checker's
  flow covers `S` — is separable from the half that is plumbing, and splitting
  them at the start would have landed the same result without the detour.

## The position loop (PikeRefine, closing round)

- Fell into `subst`'s direction twice more in the same proof, once on
  `att = pos` and once on `tp = pos`. Both ate the theorem's own `pos` and
  the error surfaced hundreds of lines later as an unknown identifier. The
  rule that would have saved all three: never `subst` an equation whose
  right-hand side is a variable the statement quantifies over — rewrite the
  other one away instead.
- Wrote `intro -` for a binder to discard. `-` is an `rcases` pattern, not an
  `intro` one, and the parse error lands on the next line rather than on the
  dash. `intro _` is the spelling.
- Reached for `by_contra` and `set` out of habit. Neither is in core or in
  Batteries, and this repo takes no mathlib; the failure is a bare "unknown
  tactic" with no hint that a dependency is missing. `rcases Nat.lt_or_ge`,
  `cases h : e` and an `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩` cover
  everything they were wanted for.
- Put `by` blocks inside an `exact` inside a `first`. A failing `by` block is
  postponed rather than raised, so `first` does not backtrack and reports the
  failure of the *first* alternative as an unsolved goal. Writing the
  impossible branches as `fun h => Outcome.noConfusion h` — no tactic block at
  all — is what makes the alternation work.
- Modelled the scan's unopened tail as a scan call indexed by an attempt, and
  had to abandon it: the loop must fix the tail before it knows what the
  current attempt answered, and the two possible tails differ by whether the
  scan stopped. Carrying the tail as a plain `Option MatchAnswer` value, with
  a separate invariant saying which scan it is, closes in one case split.

## Closing a hand-inlined equation lemma (BtBounds, `scan_repeat` round)

- Ended `scanRepeat_counted_unfold` with `rfl`, which is what an equation
  between two spellings of the same body asks for, and it timed out at `whnf`.
  `dsimp only` naming the two definitions the right-hand side introduced closes
  the same goal at once — see api-faq.md. The tell was there in the previous
  round's note: anything that reduces rather than rewrites walks into
  `scan_span`'s recursion.
- Wrote `rcases hspan : scan_span … with ⟨v, a, o⟩` and then `rw [hspan]`,
  which failed with "did not find an occurrence": the `rcases` had already
  generalized the goal. The same two lines in sequence *are* right when the
  target is a hypothesis, which is how `scanRepeat_opt` uses them, and I had
  copied the pattern without noticing which side it was aimed at.
- Planned the round as "the whole bounded case" and got one joint of it. The
  half that is reading the checker back is separable from the half that is
  building the pricing, and they meet at one abstract statement
  (`repRegion_dom`); saying that at the start would have made the stopping
  point a decision rather than a discovery.

## Claiming a side condition was free (M6)

The refinement theorems carry `suffFuel s.size p.root < none32`, and both the
docstrings and THEOREMS.md said it followed from the parser's own limits —
quantifiers stop at 65535, subjects at the cap, so the counter cannot wrap. A
review disproved it in one line: `suffFuel` is the *whole search's* fuel and
adds across sibling repetitions, so `a*b*` at the longest admitted subject
already exceeds the sentinel. The premise a counter needs is per repetition;
the premise the proof was handed is per search, and nobody checked that the
second implied the first before writing that it did.

The lesson is narrow and worth keeping: a hypothesis inherited from a proof is
not a claim about the world until someone evaluates it at the boundary. The
counterexample took a four-line arithmetic script to find.

Three smaller findings from the same review, all now fixed: `Exec`'s context
configurations had no refinement theorem at all, though the cores were already
stated over arbitrary scratch; the corpus replay compared `hascrlf` against the
very value it had been handed, which cannot fail, while omitting the option
fields that can; and the runner checked `Wf` but not the `PatFits` sizes the
lockstep bounds also read the program through.

## Proving the per-repetition counter bound (the counter-wrap round)

- Assumed the sharper premise would fall straight out of `Wf`, since the
  previous round's note said "the parser's own quantifier limit would give
  it". `Wf` did not give it: the rep clause capped the *high* and left the
  low free, so a `Wf` pattern could name `{2^40,}` and count there. The
  clause now restates MAX_QUANT on both sides, which is what the parser
  enforces — but the gap was in the file the whole time, and reading the
  clause before believing the sentence about it would have cost nothing.
- Reached for `rw [Spec.repCap]` inside the repetition case, the way the
  neighbouring `repCount` proofs do, and got "simp made no progress". The
  arm has a nested `match hi with` in it, so the equation lemma is split per
  `Option` shape and nothing fires until `hi` is destructed — see api-faq.md.
  A one-line `repCap_rep_body` lemma that does the `cases hi` once is what
  the three repetition cases actually wanted.
- Wrote the fold-max helper with `rw [List.foldl_cons]` and finished with
  `omega`, which failed on a goal whose atoms included
  `(fun a x => max a (f x)) acc x`. `rw` does not beta-reduce what it puts
  in place; `simp only` does.
- Wrote `repCap`'s unbounded arm as `lo + n` and documented it as "how high a
  repetition's count can climb". It is how high a round is *entered* with,
  which is what the proof happens to need, so nothing failed and nothing
  complained. The round the empty-match rule ends bumps the counter once more
  before leaving, so the register really goes to `lo + n + 1`. A review found
  it by evaluating the definition on `.rep 0 none _ .nul` at the empty
  subject; I had reasoned about the recursive branch and never about the
  terminal one. A definition whose docstring makes a claim the proof does not
  use is a claim nobody checks.

## Forwarding a premise and calling it discharged (M6)

The first attempt at S-12's sufficient-budget form took `hbtBudget` — the
backtracking run did not answer ResourceExceeded — and passed it straight
through, while the prose said both budgets were discharged from certificates.
The lockstep side really was discharged; the backtracking side was the same
assumption under a new name, one hop further from the reader.

It is now composed with `btRun_inBudget_forward`, so no hypothesis mentions how
a run ended. Doing that exposed something the first version hid: the two
matchers' class conditions intersect much more tightly than either alone —
eligibility wants every repetition to be a pure star, the composition wants
every repeat region to be an optional item, and the two only overlap where a
pattern's quantifiers are `?` and `??`. A forwarded premise had made the
statement look wider than it was.

## Describing a class by its examples (M6)

Having composed S-12's budgets properly, I described the resulting class as
"the patterns whose only quantifiers are `?` and `??`". That is wrong in both
directions, and a review caught it: `{0}`, `{1}` and `{0,1}` are in it too —
the compiler erases the first, compiles the second as its body, and gives the
third the same single split — while `\R?c` is out of it despite having only a
`?`, because eligibility forbids `\R` for reasons that have nothing to do with
quantifiers.

The theorem was never wrong; its hypotheses are explicit and were checked. What
was wrong was reading a class off the examples I had evaluated instead of off
the conditions.

The corrected wording was still wrong, and the second review said why: it read
the condition off the source tree, when the conditions are about the program
the compiler builds. A `{0}` is erased without its body ever being visited, so
`\R{0}c` spells a `\R` and is eligible anyway, and `(?:a*){0}b` holds an
unbounded repetition and claims no row anyway. The accurate statement walks
only what the compiler reaches, stopping at every `{0}` — which is a sentence
longer than the wrong one, and the length is the finding.

## Writing four hundred lines before compiling one (M6)

Two agents were editing the file mine imports, so building would have raced
with them, and rather than wait I wrote the whole next chunk of the counted
repetition pricing blind. It cost two bugs. One was `∀ q` over an index the
elaborator then could not type, which is already in `api-faq.md` under its own
heading — I had read that entry earlier the same day and still wrote the
pattern. The other was `rw [f, f]` on a goal whose two sides are an
inequality, where the closing `rfl` does not fire and two goals stand.

Neither is interesting on its own. What is interesting is that both were found
by somebody else's build rather than by mine, and that the file sat red for the
better part of an hour with nobody the wiser. Blind Lean is not progress
banked; it is progress claimed. Waiting for the lock would have been faster.

## Reading a theorem's shape off its name (M6)

I planned a generalization of `btRun_no_growth_forward` over a context's
reserved capacities, briefed an agent on it, and described the theorem as
being stated at `0 0` the way `btRun_inBudget_forward` is. It was already
quantified over both capacities. The two theorems sit fifty lines apart and I
had read one of them.

The cost was small — the agent checked and said so — but the habit is not: I
had inferred the statement from its neighbour and from what the gap in
THEOREMS.md implied, rather than from the statement.

## Designing the invariant before doing the arithmetic (section 4.4's account)

The brief for `RegFlow` over the counted pricing said the head needs its
counter bounded by `rep.lo + pos`, that the bound has to ride along in the
domain, and that closing it needs a code fact nobody had proved — that control
enters a repeat region only at its own `RepZero`. I took the plan as given and
spent a long while laying the invariant out: where it holds, which edges
preserve it, which of those need two regions' ranges to nest. Only then did I
work out what the head's arithmetic asks for. It asks for one thing, that the
counter the recurrence reads not wrap, and the head's own maximum test already
gives it: the recurrence is unfolded only on the arms where the count is below
the maximum, and unbounded the maximum it reads is `none32`, which is the
largest value a counter can hold. No invariant, no domain clause, no entry
fact. What the arithmetic did want was something the plan had not mentioned —
a register file long enough for the `RepEnter` to write in — and that fell out
of the same computation, at the line where the walk reads back the position it
had just remembered.

The lesson is the ordering. The invariant was a plausible answer to a question
I had not asked yet, and half an hour with the closed form would have retired
it before the first line of it was written.

- Lost a debugging round to `omega` reporting a counterexample for a goal one
  rewrite away from a hypothesis in scope. The hypothesis had come out of a
  `match`-shaped unfolding lemma through `simp only … at`, which leaves it
  printing as plain arithmetic and unreadable to `omega` — see api-faq.md. The
  tell was in the counterexample all along: the atom it listed was the whole
  right-hand side rather than the term the equation was about.

## Assuming the arena's index order was the tree's (the quantifier lowering)

The compiler's dry run prices a node from its children, so it needs an order
where every child comes first. I read `alloc_node` — it appends — and read
`apply_quant` — it allocates the copied body after the slot it rewrites — and
concluded that a child always has a higher index than its parent, so a reverse
scan of the arena would do. I wrote the pass that way.

It is not true, and the counterexample is every alternation. An `NdAlt` node
is allocated when the first `|` is read, which is after its own first branch
has been parsed: the parser then re-parents that branch under the new node.
So an alternation's first child sits *below* it and its later branches above,
and a reverse scan reaches the alternation before the branch it needs.

What made this cheap to find rather than expensive is that I checked the
claim on `(a|b)` before trusting it, node by node. What made it possible to
get wrong is reading two allocation sites and generalising from them; the
third site was the one that mattered, and it does not allocate at all — it
rewrites a link.

The fix is a list of the reachable nodes built parents-before-children —
push the root, then walk it appending each node's children — and read
backwards. It costs one array and no assumption about how the parser
happened to allocate.

## Pricing the replay before deciding, and then still finding it too big

PLAN-POST-M6.md asks for the M6 obligations to be classified by semantic
dependence on the compiler *before* the implementation starts, priced as an
input to the go decision. I did that, wrote the inventory, and concluded the
dependent set was four items of which two were definitional — on the strength
of a design where `R.compile` becomes `compileNode ∘ lower` and every
structural proof underneath it is untouched.

The inventory was right about the shape and wrong about the size, and the
thing it missed was not a theorem at all. `ReWfCompile.lean` bounds the
emitted program at four instructions per arena node. The lowering breaks that
invariant by design — that is the *whole* point of the dry run on the Python
side — and I had noted the same break in `spec.py` an hour earlier without
carrying it across to the Lean. So the replay does not want one new theorem
plus some plumbing; it wants a second counting theorem the size of the one it
replaces, and that only shows up when the build does.

Two things follow. A pricing exercise should walk the *invariants* the proofs
rest on, not only the theorem statements — the statements moved hardly at all
and the invariant is what broke. And a change already known to break a sizing
argument in one language should be checked against the same argument in every
language that states it, at the moment it is first noticed rather than at the
moment a compiler complains.

## Choosing a witness the arbiter cannot answer for (the quantifier lowering)

The lowering's caps want witnesses on both sides, and I wrote three
over-the-cap cells into the sweep's quantifier matrix by reading our own
limits: one past MAX_REPS, one past MAX_CODE through a one-instruction body,
and one past MAX_CODE through a two-instruction body. The third was
`(?:ab){9000}c`, and the campaign that found it produced thirty-three
disagreements in a row — every trial of that case, all saying the same thing.

pcre2 replicates a bounded quantifier and refuses at its own compiled size.
`(?:ab){9000}` is "regular expression is too large" there and an ordinary
counter here, so the cell had no answer to be compared against: our engine and
the arbiter disagree about whether the pattern exists, before anything about
the lowering is reached.

Two things are worth keeping. A witness for one of *our* limits is still a
differential case, and a limit of ours that sits above one of pcre2's is
exactly where a generated population walks off the end of the oracle — so a
cap witness wants checking against the arbiter before it is written down, not
after. And the failure was loud in a useful way: thirty-three findings on one
case is the shape of a case that should not exist rather than of an engine
that is wrong, and reading the count that way saved chasing an ovector.

## Refusing to compile the one case the assertion was built for

The compiler's dry run predicts what the emitter will produce, and after
emission the emitter asserts the two vectors match. The assertion is the whole
point of the design — two calculations of one number drift exactly at the cap
boundary, which is where the fallback decision lives — and it only ever runs
on a program that was emitted.

So the one place it had to be exercised was the fitting side of a boundary,
and that is the one place I did not go. Laying out thirty thousand copies is
past the reference interpreter's default step budget, so the boundary test
asked the dry run about both sides and compiled only the declining one. The
budget is a harness safety net rather than a limit of the engine, and raising
it for one test costs thirteen seconds; I wrote a paragraph explaining why the
fitting side was out of reach instead.

There was a bug there, and it was in the emitter rather than in the dry run.
The walk's fuel counter is decremented at the top of each turn and the
exhaustion test read `fuel == 0`, so a walk that needed *exactly* WALK_FUEL
turns finished on its last one, left the counter at zero, and was refused as
if it had run out — an internal error for a program the generator had just
laid out correctly. The dry run, which allows the cap itself, was right; the
test that would have shown it was the one I had argued myself out of.

The lesson is not about fuel. An assertion that only runs on the expensive
path is an assertion nobody has run, and "this case is too slow to test" is
the sentence to distrust: thirteen seconds was the actual price.

## An entry-by-entry assertion with an entry missing

The dry run prices seven things, refuses the lowering when any one of them is
over its cap, and the emitter is then held to the prediction entry by entry.
That is how the design is written down in three documents. It priced seven and
compared six.

The missing one was the registers, and it is the only entry with no array of
its own: captures and repetition counters are turned into a register count
after the walk, by a formula that lived in `program.py` while the dry run's
copy of it lived in `compiler.py`. Two spellings of one formula, one of them
inside the gate and one outside it. Nothing was wrong today — repetition
counts are compared, captures do not move, so the two agreed — which is
exactly what makes it the kind of gap that survives a review: the number was
right, the claim about how it was checked was not.

The fix is smaller than the finding. One TIR function computes the count,
`check_fit` compares the dry run's prediction against what that function says
about the finished program, and the final allocation calls the same function.

What I would do differently is read the assertion against the *list* rather
than against the code around it. I had the list — it is in the plan, in
DESIGN.md and in the docstring — and I checked that every comparison was
right instead of checking that every entry had one.

## Numbers written down at the moment they were measured

Three documents carried a count of the cases the Lean corpus replay walks, and
they carried three different numbers: 248 in one paragraph, 315 in another and
in the LOG. The executable said 331. Each had been true when written, and the
corpus grew afterwards.

A count copied into prose is a fact with no owner. The hashes in the freeze
record have a test that reads the file; these had nothing, and there is no
sensible test for a sentence. The habit that would have caught it is cheaper
than a test: when a run's output is quoted anywhere, grep for the previous
quotation of the same output before writing the new one.

## Tests that compare two files and call it a compile

The census's non-regression half needed a before-state, so I recorded what the
old engine said and joined it to the migration report. The join was between
`oracle/corpus/pre-lowering.json` and `conformance/migration.json` — two
committed files — while the docstring said the rows were recomputed and three
documents repeated it. A separate test in the same module does hold the
committed report to the generator, so the chain is sound when the whole file
runs; but the test that made the claim did not make the check, and running it
alone proves nothing.

The fix is one line of structure: generate the report at import and let every
test read that, with one test holding the committed copy to it. The direction
matters — the file keeps up with the engine, never the other way round.

The habit to keep: when a test's name says "still answers", find where the
answer comes from before writing the docstring. A fixture on both sides of a
comparison is a tautology with good manners.

## A digest of the program that left out half the program

Answering a review that the "same program" check compared only conclusions, I
hashed the compiled pattern: bytecode, region tree, repetition table, capture
and register counts. That reads like the whole thing and is not. An instruction
naming a character class carries an *index* into a table the hash never
touched, so `[a]` and `[b]` came out identical, and so did `^a` under LF and
under CRLF, since the newline convention is a scalar field I had not listed.

The mistake is the shape of the list, not any one entry. I wrote down the parts
of the program I had been thinking about all week — the parts the lowering
touches — and called that the program. The fix was to read `Re` field by field
and take everything a matcher reads.

Twice in one session now: an assertion missing an entry, then a digest missing
a field. Both times the reference was in front of me — the plan's list, the
struct definition — and both times I enumerated from memory instead. When the
claim is "all of X", the list has to come from wherever X is defined.

## Theorem statements quoted from their slogans (the M7 plan)

Two of PLAN-M7.md's central statements were written from my summary of what
a function is *for* instead of from its signature. The endpoint said the
decoded TIR compile function agrees with `R.compile` on every AST — but the
artifact's `compile` entry takes pattern bytes and parses internally, while
`R.compile` takes a `Pat`, so with the parser proof deferred the two cannot
be equated at all; the honest statement splits at a work-area relation and
leaves the exported entry as a corollary conditional on the parse. And L-2
was written `Matches (lower a) = Matches a` and glossed "same preference
order", but `Matches` exposes only the final `MatchAnswer`, `scan` having
already picked the first surviving thread; the order lives in `search`'s
thread lists, so the equality I wrote was the corollary and the theorem
was the stronger list equivalence I had not stated.

The mistake is the same in both: a plan is exactly the place where slogans
get frozen into obligations, so the statement has to be transcribed from
the definition it will be proved about, signature first, even when the
prose around it is right about the idea.

## A done-when the tag makes impossible (the M7 plan)

Gate 7 said `make verify` passes on the tagged state. The tag is
`wave1-frozen`, it stays on the freeze commit for all of M7, and `make
verify` is built by M7's last gate — so the tagged state can never contain
the gate, and the criterion was unsatisfiable as written. Same family as
gate 3, which nearly asked the freeze test to hold the tag to a Lean pin
file that postdates the tag. A completion criterion has to be checkable at
the commit where it is claimed, and anything pinned in the past can only
be *read from*, never asked to contain what came later.

## The destination is resolved first (gate 1's interpreter)

What I got wrong: I wrote the TIR interpreter's `assign`, `take`, `copy`,
`freeze` and `pop` so that the source was evaluated before the destination
place was resolved. TIR-SPEC.md section 13 pins the opposite order — the
destination place first, its index expressions left to right and each
bounds-checked as it is resolved, then the value, then the store — and
`tir/interp.py` follows it.

Why it matters: it is observable. When both sides would trap, the order
decides which trap the program answers with, and a `pop` from an empty
sequence into an out-of-bounds destination should answer T-01 and not T-02.
An interpreter that got this backwards would have made every gate 5
simulation lemma about a language slightly different from the one the
backends implement, and the corpus would not have caught it, because the
corpus does not drive the engine into two competing traps.

The lesson is narrower than "read the spec": I transcribed the *effects* of
each statement carefully and skipped the paragraph that says in which order
they happen, because effects look like the content and order looks like
detail. In a language whose observable outcomes include which check failed
first, order is content.

## `git checkout` on a file I had not committed

What I got wrong: while inducing failure modes for `make verify`, I edited
`THEOREMS.md` to fake a wrong hash and then restored it with `git checkout
THEOREMS.md`. The file also held twenty minutes of uncommitted documentation
work, which that command discarded along with the fake.

The habit that would have prevented it is not "check `git status` first" —
I had, and the file was listed as modified, which I read as "the fake is
there" rather than "the real edit is there too". It is: when a check needs a
file temporarily wrong, copy it aside and restore from the copy, or commit
first. `git checkout` restores from the index, and the index does not know
which of my changes I meant.
