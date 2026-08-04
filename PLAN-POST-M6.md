# Rectifying the M5 quantifier gap, after M6

This plan exists because of one pattern. `(?<user>\w+)@(?<host>[\w.]+)` is an
ordinary wave 1 pattern, and DESIGN.md promises that essentially all of wave 1
runs on the Pike VM and classifies linear. Today it does not: the compiler
emits counter-based Rep opcodes for every quantifier, `pike_ok` admits pure
stars only, and the pattern lands on the backtracking path with a certified
cost bound of

    3448 + 2898*(n+1) + 764*(n+1)^2 + 48*(n+1)^3

which is 48.9 billion cost units at n = 1000, against a measured worst case of
9.13 million and a memory reservation of 354 MB against a measured peak of
36 KB. The certificate is sound — the arithmetic is exact and the engine stays
under it — but the number is unusable, and the linear classification is the
project's main selling point.

The root of it is a design/implementation discrepancy inside a milestone
declared complete. DESIGN.md section 4.3 says counted repetitions are compiled
by unrolling; compiler.py says, on purpose, that it does not do that; README
says M5 is done and the artifact frozen. No milestone owns the missing piece.
This plan is where it gets owned.

The email pattern is one instance of a category, not the whole defect.
`pike_ok` has three rejection conditions, and sorting ordinary wave 1
patterns by them says what the fix reaches and what it deliberately leaves:

    +------------------------------+--------------------------+--------------------------------+
    | category                     | examples                 | after the lowering             |
    +------------------------------+--------------------------+--------------------------------+
    | counter-based quantifiers    | a+  a+?  a{2}  a{1,}     | Pike-eligible when the lowered |
    |                              | [A-Z]{2,8}               | form fits the cap              |
    | nullable unbounded bodies    | (?:a?)*  (?:a|)*         | still backtracking             |
    |                              | (?:a*)*  (?:^)*          |                                |
    | \R anywhere                  | \R  a\Rb  (?:\R)*        | still backtracking, until \R   |
    |                              |                          | compiles as an alternation     |
    | lowered form over the cap    | a large enough {m,n}     | backtracking, by design        |
    +------------------------------+--------------------------+--------------------------------+

For scale: `a?`, `a??`, `a{0,1}`, `a{1}`, `a*` and `a{0,}` are eligible
today, alternations of unequal widths like `(?:a|bc)*` are fine, and
captures, inline options and anchors do not by themselves prevent Pike
routing — assertions only bite when they let a repeated body finish without
consuming. So the first row is the entire payoff of this plan, and it is the
common case: every unbounded repetition with a nonzero minimum, which today
carries a superlinear certificate (`a+` alone is 14.2 million cost units at
n = 1000, classified notProvenLinear), and the bounded `{m,n}` spellings,
which split today. A bounded repetition of a simple body — `a{2,8}`,
`(?:ab){3,5}` — classifies Linear already and merely pays counter-form
constants. A bounded repetition of an ambiguous body — `(?:a+){2}`,
`(?:a+b){2}`, `(?:a+|b){2}` — has no accepted certificate at all and
answers ExceedsBudget on every accessor, the class included. The lowering
rescues that last group twice over: `(?:a+){2}` lowers to `(?:aa*)(?:aa*)`,
which is Pike-eligible, so migrations arrive from ExceedsBudget as well as
from notProvenLinear.

The evidence that the fix is architectural-risk-free, and the limit of that
evidence: the hand-lowered spelling `(?<user>\w\w*)@(?<host>[\w.][\w.]*)`
flows through compilation, eligibility, certificate generation, checking, the
accessors and the context machinery today, and answers class Linear, cost
201,330, stack 0, memory 12,115 at n = 1000. So the intended lowered
representation has been exercised successfully through the entire downstream
pipeline, and no matcher or analyzer redesign is needed. That is not a proof
of the automatic lowering — capture identity reuse, cap-aware fallback, the
sizing invariants and priority order are all still open work, and they are
the substance of this plan.

## Sequencing

Everything here happens after M6 lands and before M7 begins. M6 and M7 both
target the frozen wave 1 artifact, so the order is: finish M6 against the
current freeze, apply this plan, refreeze, replay M6 against the new hash,
then start M7. Replaying M6 once is the cost of doing this now; doing it
after M7 would mean replaying both, and doing it never would mean proving
theorems about behavior we have already decided is wrong.

The replay is expected to be mechanical where the Layer S and R proofs speak
about the reference semantics, which the lowering does not change — but
"expected" is not a plan, an inventory is. Before the implementation
starts, list every M6 theorem and mark whether it mentions compilation
layout, bytecode shape, or artifact bytes; the unmarked ones replay
mechanically by construction, and the marked ones are the cost input to
the decision below, priced before the work rather than discovered after
it.

## Step 1: settle the rules before the code

The repo's method is that normative documents come first, and this change is
no exception. Before touching the compiler:

- Amend DESIGN.md section 4.3 to describe the mechanism actually built and
  kept: both matchers read one bytecode; the Pike VM treats the four Rep
  opcodes of a pure star as epsilon forks; and quantifiers that are not pure
  stars are lowered to star form at compilation when the lowered size fits
  the cap. The current text describes an unrolled second compilation that
  never existed.
- Amend section 2.1's carve-out sentence. There are three carve-outs, not
  one: a quantifier whose lowered form exceeds the cap, a star whose body
  can complete emptily (the `(a?)*` capture-preference problem — semantic,
  and no amount of unrolling removes it), and `\R` until it compiles as an
  alternation. All three route to the backtracking matcher, and the
  classifier remains the per-pattern statement of the guarantee.
- Fix section 4.3's claim that a non-Pike pattern "is then classified
  notProvenLinear, since the linear class is defined as Pike-eligible."
  That is not what is built, and what is built is better. BOUNDS.md
  section 6 classifies from the shape of the certified cost bound, whatever
  the matcher, and the implementation follows it: `a{2}` and `\R` classify
  Linear today on the backtracking path, because their certified bounds
  are linear. Keep BOUNDS.md normative and reword DESIGN.md — the class is
  a property of the certificate, not of matcher selection, and the two do
  not coincide even after this plan (`\R` stays Linear-and-backtracking).
  The memoization passage equating the two needs the same care: memoized
  backtracking is legal on Pike-eligible patterns, which after this fix is
  no longer the same set as the Linear-classified ones.
- Fix the section 4.2 instruction table: RepInit/RepChk is stale; the engine
  and BOUNDS.md have RepZero, RepLoop, RepEnter, RepNext.
- BOUNDS.md needs no rule changes. The counted-repetition rule of its
  section 4.4 stays, because the over-cap fallback still produces counter
  bytecode and still needs pricing.

## Step 2: the lowering

One rewrite, at compilation, from counted form to star form:

    x+       ->  x x*
    x{m,}    ->  x .. x x*          (m copies)
    x{m,n}   ->  x .. x (x (.. )?)?  (m copies, then n-m nested optionals)

Each generated optional is one Split whose arm order follows the
quantifier's greediness — body first when greedy, skip first when lazy — and
the optionals nest so the k-th copy's presence is decided before the
(k+1)-th's. That nesting direction is what makes the count preference match
pcre2; `a{1,3}?` followed by a literal that forces backtracking is the case
that tells a wrong nesting apart, and it belongs in the sweep. The star that
remains is still the four Rep opcodes, which is what `pike_ok` already
admits; the eligibility predicate is untouched — what changes is the
programs presented to it.

The constraints that make this more than a syntax rewrite:

- Capture identity. Every copy of a body emits its `Save`s against the
  original group's slot indices — a group repeated three times is one
  group, reported once — and the lowering allocates no new group, no new
  slot, and leaves source-order group numbering and names exactly as the
  parser assigned them. That is the requirement; the differential sweep is
  a check on it, not a substitute for stating it.
- Empty iterations. pcre2 replicates a bounded `{m,n}` so every copy runs,
  and `(|a){1,3}` on "a" under NOTEMPTY is the case that tells replication
  from a repeating-ket break. The counter implementation already had to
  emulate replication; the lowered form is replication, which should make
  agreement easier, not harder — but that is a thing to demonstrate, not
  assume.
- The cap and the fallback. A lowered form that does not fit routes the
  pattern to the backtracking VM in counter form. It must not become
  PatternTooLarge: oversize is a documented carve-out, not a compile error.
  So the compiler sizes the lowered program before emitting anything, and
  the decision is per pattern — either the whole program lowers and fits,
  or the whole program compiles in counter form as today. "Fits" has one
  meaning: a dry-run pass prices every arena the emitter draws from, with
  the same arithmetic the emitter then executes, and the pattern fits when
  all of them are within their caps. That is more than code and regions:
  a copied body that contains a repetition duplicates its Rep entry, so
  MAX_REPS is consumed by the lowering, and MAX_REGS with it, since the
  register file is sized as MAX_OVEC + 2 * MAX_REPS; and the walk's own
  state is bounded by MAX_JOBS and MAX_PATCHES, either of which can bind
  before MAX_CODE does depending on where the rewrite lives. Exactly at a
  cap is a fit; one past any of them is the fallback; and the sweep
  exercises both sides of that boundary. The dry run and the emitter are
  two calculations of one number, so their equality is a checked
  invariant rather than a shared intention: after emission the compiler
  asserts that the counts actually emitted equal the prediction, in every
  arena the dry run priced. Two independently maintained calculations
  drift exactly at the cap boundary, which is exactly where the fallback
  decision lives, and an assertion is cheaper than that bug.
- Lower only when it can pay. Lowering cannot make a nullable unbounded
  body eligible — `(?:a?)+` lowers to `(?:a?)(?:a?)*` and the trailing star
  still has a nullable body, which is the exact thing pc-keyed
  deduplication cannot honor — and it cannot help a pattern containing
  `\R`. An AST pre-check for either obstacle keeps such patterns in
  counter form, which is more compact and is what the section 4.4 pricing
  rule already handles. The rule stays simple: the pre-check decides
  whether to lower, and `pike_ok` alone decides eligibility afterward, so
  nothing about routing is ever inferred from the lowering's own logic.
  That safety comes at a price the census must collect on: the pre-check
  is a second implementation of "can finish without consuming", and each
  direction it can be wrong in costs something — a false negative leaves
  a rescuable pattern on the backtracking path, a false positive lowers a
  program `pike_ok` then refuses anyway. So the census provisionally
  lowers every pattern the pre-check declined and asks `pike_ok` whether
  it would have been admitted — a yes is a missed migration and fails the
  census — and the migration report asserts that the lowered-but-refused
  set is empty. The two checks hold the pre-check to `pike_hollow`'s
  answer on the whole corpus, which is the only place the duplicated
  judgment is allowed to live.
- The sizing invariants. MAX_CODE is 4 * MAX_NODES + 16 on the strength of
  "no AST node emits more than four instructions", and lowering breaks that
  invariant by design. MAX_REGIONS = MAX_NODES breaks with it, since every
  emitted copy carries its own regions. The pre-sizing pass replaces the
  per-node invariant: the fit check against the caps is what makes the
  arrays safe, and the invariant's comment should say so. Whether the caps
  themselves grow is a choice to make deliberately — growing them buys more
  patterns onto the Pike path at the price of larger worst-case programs
  everywhere the caps size an array.

Where the rewrite lives — in the parser's arena before the walk, or in the
compiler's walk emitting a child job several times — is left to whoever
implements it, with one requirement on the region table, and "right" has a
definition rather than a feeling: every copy of a body carries its own
region records, nested under the correct parents, ranged over the copy's
own instructions, in emission order, such that `cert_shape` accepts the
tree and the analyzer prices it and the checker accepts the price. The
shape rules of BOUNDS.md section 4 are the specification of correctness
here, on purpose — a lowering whose bytecode is right but whose region
tree is refused is a compiler bug, and compilation reports it as one
rather than quietly shipping the pattern without a certificate.

## Step 3: evidence

In order, each gating the next:

- The unit and conformance suites, regenerated. The certificate corpus
  changes shape: patterns like the email one move from CfgBacktrack cubic
  certificates to CfgPike closed forms. Regenerate
  conformance/certificates.json together with a machine-checked migration
  report — per pattern: the selected configuration before and after, the
  certificate status, the class, the cap decision, and two reason fields
  that are deliberately not one. The first is the lowering decision and
  every AST-level blocker the pre-check found, all of them rather than the
  first — a pattern can hold `\R` and a nullable star at once, and a
  report that names one blocker per pattern would flap when the walk order
  changes. The second is `pike_ok`'s verdict on the program as compiled.
  The two describe different programs and must not be compared as if they
  agreed: for `a+\R` the pre-check declines to lower because of `\R`, the
  bytecode therefore keeps its counter, and `pike_ok` — a short-circuiting
  boolean with no reason of its own — refuses that counter before it ever
  reaches the `\R`. The blocker list must not be the report's own
  invention, or the report becomes a rationalizer: a generator that
  reconstructs blockers from the AST after the fact can explain an
  incorrect compiler decision and pass its own assertions while doing so.
  Either the compiler's pre-check exports its decision and blockers and
  the report carries them verbatim, or the report derives them
  independently and asserts equality with what the compiler recorded — a
  decision the derivation cannot reproduce is a finding about the
  compiler, never a formatting difference to smooth over. With that
  anchored, the assertion is: every pattern that stays on the backtracking
  matcher names at least one ineligibility reason or the cap. Matcher selection is the thing being
  asserted here; classification has its own census below, because the two
  are different questions. Reading the diff by hand is encouraged and is
  not the gate.
- The differential sweep, extended with the quantifier matrix: nullable
  and non-nullable bodies, with and without captures, greedy and lazy, for
  each of `{m}`, `{m,}` and `{m,n}`, crossed with NOTEMPTY,
  NOTEMPTY_ATSTART and anchoring, each followed by a literal that forces
  backtracking into the copies — `(|a){1,3}` under NOTEMPTY and `a{1,3}?b`
  are the two seeds the matrix grows from. Add the cap boundary in both
  directions, so the lowered and fallback compilations of near-identical
  patterns are both exercised against pcre2, across matchers and across
  backends.
- The bound assertions in fuzzing, unchanged in kind: no run may exceed its
  certificate, on either path.
- A named regression for the motivating pattern: `(?<user>\w+)@(?<host>[\w.]+)`
  classifies Linear, and once the implementation is frozen the test pins
  the exact accessor answers at n = 1000, the way the certificate corpus
  pins every other bound. Until those numbers exist, the pre-registered
  sanity scale is the hand-lowered spelling's measurement — 201,330 cost
  units, 0 stack entries, 12,115 bytes — and an automatic lowering that
  lands an order of magnitude away from it owes an explanation before the
  numbers are pinned.
- A classification census. Over a corpus of representative wave 1 patterns,
  count the classifier's answers before and after. Every migration to
  Linear should be a first-row pattern from the table above. Every pattern
  still notProvenLinear should name one of three reasons: a nullable
  unbounded body, an over-cap quantifier, or a superlinear pattern kept on
  the backtracking path by `\R` — `a+\R` sits at 16.3 million cost units
  today while bare `\R` is Linear, and both facts must survive the fix.
  ExceedsBudget gets its own column, in both flavors: no accepted
  certificate at all (`(?:a*)*`) and a certified bound past counter
  arithmetic at the asked length (`(?:a?)+`, whose class answers
  notProvenLinear while every bound accessor refuses). And the gate for
  already-Linear patterns is no classification regression plus an explicit
  resource-tradeoff review, not Pareto improvement: migrating `a{2}` to
  Pike form moves 63,887 cost / 3 stack / 560 memory to 25,392 / 0 / 1,585
  — cost and stack fall, the conservative constant reservation rises — and
  bare `\R` does not change at all. Both movements are correct; the census
  records them rather than forbidding them.
- Regenerated Go and JavaScript backends, their suites green, and the
  no-allocation context promise still holding under both instrumentations.

## Step 4: refreeze and replay

Regenerate the artifact, record the new hash in THEOREMS.md, replay the M6
lake build against it, and update README's status paragraph to say what is
now true: the wave 1 guarantee holds with the three named carve-outs. If any
part of this plan is deliberately deferred instead, README says that instead
— the one unacceptable outcome is documents that describe a mechanism the
implementation does not have, which is the state this plan exists to end.

## Out of scope, on purpose

Three refinements are adjacent and not part of this gate:

- Live-versus-peak composition for the backtracking stack bound. Promising,
  but it only pays off if the undo trail gets the same treatment — the
  memory bound is priced from both capacities, and a stack-only refinement
  leaves the reservation quadratic through the trail term.
- First-byte disjointness in the alternation rule, and the anchored n + 1
  factor. Both are named in BOUNDS.md as the next sharpenings; they improve
  patterns that genuinely stay on the backtracking path, which after this
  plan is a much smaller set.
- A mechanism for nullable-body stars on the Pike VM, and `\R` as an
  alternation. Each would remove a carve-out; neither blocks the guarantee
  being stated honestly with the carve-outs in place.

None of these block the refreeze. All of them get cheaper to evaluate once
the population of backtracking-only patterns is down to the carve-outs.
