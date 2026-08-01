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
