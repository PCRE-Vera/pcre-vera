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
