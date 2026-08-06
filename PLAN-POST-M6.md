# Rectifying the M5 quantifier gap, after M6

This plan exists because of one pattern. `(?<user>\w+)@(?<host>[\w.]+)` is an
ordinary wave 1 pattern, and DESIGN.md promises that essentially all of wave 1
runs on the Pike VM and classifies linear. Today it does not: the compiler
emits counter-based Rep opcodes for every counted repetition that is not an
optional, a singleton or a pure star, `pike_ok` admits pure stars only, and
the pattern lands on the backtracking path with a certified cost bound of

    3448 + 2898*(n+1) + 764*(n+1)^2 + 48*(n+1)^3

which is 48.9 billion cost units at n = 1000, against 9.13 million measured
on the most hostile subject the investigation found, and a memory reservation
of 354 MB against a 36 KB measured peak on that subject. The certificate is
sound — the polynomial is exact as stored, deliberately an upper bound in
what it claims, and every observed run stays under it — but the number is
unusable, and the linear classification is the project's main selling point.

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
    |                              | [A-Z]{2,8}               | form fits the caps             |
    | nullable unbounded bodies    | (?:a?)*  (?:a|)*         | still backtracking             |
    |                              | (?:a*)*  (?:^)*          |                                |
    | a \R the program emits       | \R  a\Rb  (?:\R)*        | still backtracking, until \R   |
    |                              |                          | compiles as an alternation     |
    | lowered form over a cap      | a large enough {m,n}     | backtracking, by design        |
    +------------------------------+--------------------------+--------------------------------+

These rows are routing categories and nothing else. Classification is a
different axis — bare `\R` routes to backtracking and still classifies
Linear, `(?:^)*` is certified superlinear while `(?:a?)*` has no accepted
certificate at all — and the census in step 3 keeps the two apart.

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
of the automatic lowering — capture identity, recursive lowering of nested
repetitions, cap-aware fallback, the sizing invariants and priority order
are all still open work, and they are the substance of this plan.

## Sequencing

Everything here happens after M6 lands and before M7 begins. M6 and M7 both
target the frozen wave 1 artifact, so the order is: finish M6 against the
current freeze, apply this plan, refreeze, replay M6 against the new hash,
then start M7. Replaying M6 once is the cost of doing this now; doing it
after M7 would mean replaying both, and doing it never would mean proving
theorems about behavior we have already decided is wrong.

How much of the replay is mechanical is a question the theorem inventory
answers, not one this plan prejudges. THEOREMS.md is an inventory of
obligations, and some of them depend on this change semantically rather
than textually: `R.compile` is a restatement of the real compiler, so the
lowering changes the theorem's subject directly; the compile/run
equivalence goes with it; and `S-12`, the cross-matcher agreement, is
quantified over Pike-eligible patterns, so every pattern this plan makes
eligible widens what that theorem covers — new proof coverage, not a
rehash. Before the implementation starts, classify every M6 obligation by
semantic dependence on compilation — not by whether its text mentions
bytecode bytes — and price the dependent ones as an input to this plan's
go decision rather than a discovery at the end.

## Step 1: settle the rules before the code

The repo's method is that normative documents come first, and this change is
no exception. Before touching the compiler:

- Amend DESIGN.md section 4.3 to describe the mechanism actually built and
  kept: both matchers read one bytecode; the Pike VM treats the four Rep
  opcodes of a pure star as epsilon forks; and counted repetitions that are
  not already optionals, singletons or pure stars are lowered to star form
  at compilation when the lowered size fits the caps. The current text
  describes an unrolled second compilation that never existed.
- Amend section 2.1's carve-out sentence. There are three carve-outs, not
  one: a quantifier whose lowered form exceeds a cap, a star whose body
  can complete emptily (the `(a?)*` capture-preference problem — semantic,
  and no amount of unrolling removes it), and `\R` until it compiles as an
  alternation. All three are routing statements — they say which matcher
  runs, and nothing about the class — and the classifier remains the
  per-pattern statement of the guarantee.
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
- Sweep the rest of the prose for the same stale equivalence, because it
  was written when Pike and Linear were meant to be one set: DESIGN.md
  section 5's classification passage describes the Pike bound as the only
  linear claim; layout.py carries comments that encode the older
  equivalence; README makes broad status statements beyond the paragraph
  step 4 updates; and any corpus or schema documentation that assumes one
  certificate form per routing split.
- BOUNDS.md needs no rule changes. The counted-repetition rule of its
  section 4.4 stays, because the fallback path still produces counter
  bytecode and still needs pricing.

## Step 2: the lowering

One rewrite, at compilation, from counted form to star form:

    x+       ->  x x*
    x{m,}    ->  x .. x x*           (m copies)
    x{m,n}   ->  x .. x (x (.. )?)?  (m copies, then n-m nested optionals)

The boundary spellings are enumerated rather than implied, lazy variants
included, and the compiler's existing special forms are kept, not
re-derived: `x{0,0}` emits nothing, `x{1,1}` is the body alone, `x{0,1}` is
the one-Split optional, and `x{0,}` normalizes to the native pure-star Rep
— no mandatory copy, no separate counter entry. `x{m,m}` is m copies with
no optional tail. Only what is left — a nonzero minimum or a finite bound
above one — is lowering's to do.

Lowering is recursive, bottom-up, and all-or-nothing. A copied body that
itself contains a counted repetition contains a counter, and `pike_ok`
refuses any retained counter, so lowering only the outer quantifier of
`(?:a{2})+` buys nothing. The candidate that matters is the fully
recursively lowered program, and fitting is necessary, never sufficient: a
pattern is a Pike candidate when the pre-check finds no semantic blocker
and the candidate constructs within every cap of the fit vector below, and
`pike_ok`'s verdict on the emitted program remains the authority even then
— a pattern can fit every cap and stay ineligible, which is what `\R`
does. If the candidate does not construct — any part of it — the whole
pattern compiles in counter form as today. All-or-nothing is not a semantic necessity, and the plan says so:
one retained counter already makes the program ineligible, which makes
partial lowering pointless for routing, and whole-program fallback keeps
the cap accounting one decision instead of a search. The witness test:
two independently lowerable repetitions whose combined lowered form
overshoots a cap must compile whole in counter form — not partially
lowered, and not PatternTooLarge.

Each generated optional is one Split whose arm order follows the
quantifier's greediness — body first when greedy, skip first when lazy — and
the optionals nest so the k-th copy's presence is decided before the
(k+1)-th's. That nesting direction is what makes the count preference match
pcre2, and `a{1,3}?` followed by a literal that forces backtracking is the
seed case that tells a wrong nesting apart — a seed, not the property. The
prose above is a preference order, not yet a construction, so the
implementation writes the lowering down as a recursive definition over the
AST (or an exact bytecode construction with its patch targets), and the
sweep generates its oracle over a defined body grammar — bodies with
groups, alternations, inner repetitions — rather than trusting any single
spelled-out case. The star that remains is still the four Rep opcodes,
which is what `pike_ok` already admits; the eligibility predicate is
untouched — what changes is the programs presented to it.

The constraints that make this more than a syntax rewrite:

- Capture identity, and capture lifetime. Every copy of a body emits its
  `Save`s against the original group's slot indices — a group repeated
  three times is one group, reported once — and the lowering allocates no
  new group, no new slot, and leaves source-order numbering and names
  exactly as the parser assigned them. Slot identity alone is not the
  whole contract, so the observable lifetime rules are part of the
  specification too: a later participating copy overwrites the group's
  previous capture; a skipped optional copy leaves the prior value
  intact; the unselected arms of a copied alternation stay unset;
  backtracking out of an abandoned copy restores what that copy wrote;
  and on the Pike side the copy-on-write blocks must deliver the
  preferred path's captures at every pc collision. The oracle cases that
  pin this are concrete — `(?:(a)|(b)){1,2}`, `(?:(a)?){1,2}`,
  `((a|aa)){1,3}b`, `(?<g>a?){1,3}b` — and the assertion is full ovector
  equality with pcre2, unset slots included.
- Empty iterations. pcre2 replicates a bounded `{m,n}` so every copy runs,
  and `(|a){1,3}` on "a" under NOTEMPTY is the case that tells replication
  from a repeating-ket break. The counter implementation already had to
  emulate replication; the lowered form is replication, which should make
  agreement easier, not harder — but that is a thing to demonstrate, not
  assume, and the sweep matrix in step 3 is where it is demonstrated.
- The fit vector, and a bounded dry run. A lowered form that does not fit
  routes the pattern to the backtracking VM in counter form, never to
  PatternTooLarge: oversize is a documented carve-out, not a compile
  error. The dry run that decides it prices three distinct kinds of
  limit, because they are not one kind:

      final storage:  code length (MAX_CODE), region count (MAX_REGIONS),
                      rep count (MAX_REPS), and the candidate's derived
                      register count — its novec plus twice its own rep
                      count — against MAX_REGS; the global ceiling
                      MAX_OVEC + 2 * MAX_REPS is the type's bound, not
                      the candidate's number
      transient:      peak job depth (MAX_JOBS), peak patch count
                      (MAX_PATCHES), and the walk's fuel — WALK_FUEL is
                      8 * MAX_NODES on the strength of a bounded-revisit
                      argument that job duplication breaks, so it is
                      re-derived from the pre-sizing or the placement is
                      chosen so revisits do not multiply; a candidate that
                      fits every array and then dies of fuel exhaustion
                      as an internal error is a bug of ours
      unchanged:      the parser's node, group, name and class limits,
                      which lowering happens after and never relaxes

  The dry run itself must be bounded: a quantifier can name up to
  MAX_QUANT = 65535, and a pre-sizing pass that expands or enqueues
  candidate copies to discover the overflow has already done the damage
  it exists to prevent. It computes with closed-form counts, detects an
  excess before allocating or enqueuing anything, and only a candidate
  that passed the whole vector is emitted at all. Exactly at a cap is a
  fit; one past any cap is the fallback; the sweep exercises both sides,
  and the boundary witnesses are generated from the dry run's own report
  rather than guessed. One more rule keeps the fallback honest: it is
  available only where today's counter compilation succeeds. A pattern
  whose ordinary counter form already exceeds a limit keeps its
  PatternTooLarge — lowering neither creates that outcome nor masks it.
- Dry run against emitter. The two passes share their checked counting
  primitives and their cap constants — one place for the arithmetic that
  can overflow — and traverse independently: the dry run counts virtual
  output and peak transient state, the emitter mutates real storage, and
  after emission the compiler asserts the emitted vector equals the
  predicted one, entry by entry. Shared primitives keep the numbers from
  drifting; independent traversal is what makes the assertion mean
  something. Two calculations of one number drift exactly at the cap
  boundary, which is exactly where the fallback decision lives, and an
  assertion is cheaper than that bug.
- Lower only when it can pay. Lowering cannot make a nullable unbounded
  body eligible — `(?:a?)+` lowers to `(?:a?)(?:a?)*` and the trailing star
  still has a nullable body, which is the exact thing pc-keyed
  deduplication cannot honor — and it cannot help a pattern that emits a
  `\R`. An AST pre-check for either obstacle keeps such patterns in
  counter form, which is more compact and is what the section 4.4 pricing
  rule already handles. Emits rather than contains, which this plan first
  said and the implementation sharpened: the pre-check reads the tree the
  way the emitter walks it, so a `{0}` body is skipped for both obstacles.
  Nothing under it is compiled, so nothing under it can route the pattern
  anywhere, and `(?:\R){0}a+` lowers. The `\R` half is otherwise deliberately
  coarse and says so: Pike refuses `\R` because it consumes a variable number of
  bytes, not because the opcode is inconvenient, and keeping the whole
  pattern in counter form means the `a+` inside `a+\R` is not lowered
  even though it could be — a whole-program routing policy, consistent
  with all-or-nothing above, not a semantic requirement. The rule stays
  simple: the pre-check decides whether to lower, and `pike_ok` alone
  decides eligibility afterward, so nothing about routing is ever
  inferred from the lowering's own logic. That safety comes at a price
  the census must collect on, because the pre-check is a second
  implementation of a judgment `pike_hollow` already makes — and makes at
  the bytecode level, conservatively on assertions, so the two are held
  together by an equivalence gate stated over the same object: for every
  corpus pattern whose fully lowered candidate constructs within the fit
  vector, the pre-check approves exactly when `pike_ok` approves that
  candidate bytecode. An approval the pre-check missed is a missed
  migration and fails the census; a lowering `pike_ok` then refused makes
  the lowered-but-refused set nonempty and fails it too; and candidates
  that do not construct within the caps are reported in their own
  bucket, counted as fallback rather than as either failure.
- The sizing invariants. MAX_CODE is 4 * MAX_NODES + 16 on the strength of
  "no AST node emits more than four instructions", and lowering breaks that
  invariant by design; MAX_REGIONS = MAX_NODES breaks with it. The
  pre-sizing pass replaces the per-node invariant: the fit check against
  the caps is what makes the arrays safe, and the invariant's comment
  should say so. Whether the caps themselves grow is a choice to make
  deliberately — growing them buys more patterns onto the Pike path at the
  price of larger worst-case programs everywhere the caps size an array.

Where the rewrite lives — in the parser's arena before the walk, or in the
compiler's walk emitting a child job several times — is left to whoever
implements it, with one requirement on the region table, and "right" is
defined per generated construct rather than by feeling. A copied leaf
emits code and opens no region; a copied group or alternation opens the
regions its original opened, nested under the correct parents and ranged
over the copy's own instructions; a generated optional opens the
one-Split region BOUNDS.md section 4.3 prices; the trailing star opens
its repeat region; and a nested lowered repetition nests all of the
above. The mechanical gate over the lowering corpus is: `cert_shape`
answers CrOk, the checker accepts the analyzer's price, and no pattern
compiles to an internal error. A lowering whose bytecode is right but
whose region tree is refused is a compiler bug, and compilation reports
it as one rather than quietly shipping the pattern without a certificate.

## Step 3: evidence

Every numerical gate in this step is bound to a fixture, the way the
certificate corpus already pins its bounds: pattern bytes, compile
options, newline and BSR convention, the matchConfig asked about, the
subject length, the artifact hash the numbers were produced against, and
the expected statuses and values. A number in this plan's prose is a
scale; a number in a fixture is a gate.

In order, each gating the next:

- The unit and conformance suites, regenerated. The certificate corpus
  changes shape: patterns like the email one move from CfgBacktrack cubic
  certificates to CfgPike closed forms. Regenerate
  conformance/certificates.json together with a machine-checked migration
  report whose columns are orthogonal on purpose — one answer per
  question, each naming the program and the analysis it describes, never
  recombined:

      original blockers        the pre-check's findings on the original
                               AST: nullable unbounded body | \R, all of
                               them
      lowering decision        lowered | not needed (already canonical:
                               a, a?, a*, ...) | declined (blockers) |
                               declined (cap)
      pike verdict             pike_ok on the emitted program, whichever
                               form was emitted
      backtracking analysis    accepted | ArAmbiguous | ArOverflow |
                               ArShape — the analyzer's answer, recorded
                               even when Pike is selected
      selected certificate     which configuration's certificate the
                               pattern carries, and its class
      accessors at n           cost, stack and memory separately, each
                               finite or refused — saturation and the
                               ceilings are separate refusal paths

  The backtracking-analysis column exists because the two analyses are
  genuinely independent and can disagree without either being wrong:
  `a*b*c*d*` is Pike-selected, carries an accepted Pike certificate and
  classifies Linear, while the backtracking analyzer answers ArOverflow
  for the same pattern — it is BOUNDS.md's own example of coefficients
  running out. A schema with one certificate column would record that
  pattern as a contradiction; two columns record it as what it is. The
  blocker column records every blocker the pre-check found, not the
  first — a pattern can hold `\R` and a nullable star at once, and a
  one-blocker report would flap when the walk order changes. It is also
  a statement about the original AST, deliberately: a lowerable `a+` has
  a non-pure Rep before lowering and none after, so a blocker column
  that read the emitted bytecode would say something different, and the
  schema names which program each column reads so no one has to guess. It also must
  not be the report's own invention, or the report becomes a
  rationalizer that can explain an incorrect compiler decision and pass
  its own assertions doing it: either the compiler exports its decision
  and blockers and the report carries them verbatim, or the report
  derives them independently and asserts equality with what the compiler
  recorded — a decision the derivation cannot reproduce is a finding
  about the compiler, never a formatting difference to smooth over. The
  blocker column and `pike_ok`'s verdict describe different programs —
  for `a+\R` the pre-check declines on the `\R`, the bytecode keeps its
  counter, and `pike_ok` refuses that counter before ever reaching the
  `\R` — so they are never compared to each other; the equivalence gate
  of step 2 compares like with like instead. The assertions over the
  report: every pattern on the backtracking matcher names at least one
  blocker or the cap; the lowered-but-refused set is empty; and the
  ArShape count is zero — ArShape is the two halves of BOUNDS.md
  disagreeing, which no pattern can legitimately cause, and compilation
  surfaces it as an internal error rather than an expected outcome.
  Reading the diff by hand is encouraged and is not the gate.
- The differential sweep, extended with the quantifier matrix, finitely
  and reproducibly: bodies drawn from a defined grammar — literals,
  classes, groups, alternations, optional and starred items, nullable and
  not, with and without captures — crossed with greedy and lazy `{m}`,
  `{m,}` and `{m,n}` for m and n in 0 through 3 plus the cap-adjacent
  values the dry run's report names, crossed with NOTEMPTY,
  NOTEMPTY_ATSTART, anchoring and nonzero start offsets, each followed by
  a literal that forces backtracking into the copies. `(|a){1,3}` under
  NOTEMPTY and `a{1,3}?b` are two cells of that matrix, not its extent.
  The oracle is full result equality with pcre2 — ovector included, unset
  slots included — and cross-matcher agreement wherever the pattern is
  eligible, on every backend, under a recorded seed and manifest so the
  run is the same run twice.
- The bound assertions in fuzzing, unchanged in kind: no run may exceed its
  certificate, on either path.
- A named regression for the motivating pattern: `(?<user>\w+)@(?<host>[\w.]+)`
  classifies Linear, and once the implementation is frozen the fixture
  pins the exact accessor answers at n = 1000. Until those numbers exist,
  the gate is an explicit interval derived from the hand-lowered
  measurement of 201,330 cost, 0 stack, 12,115 memory: cost below
  1,000,000, stack exactly 0, memory below 100,000. Inside the interval,
  proceed and pin; outside it, the lowering is wrong or the plan's
  understanding is, and either way the discrepancy is written down before
  the numbers move.
- A classification census, read off the migration report's columns. Every
  migration to Linear names `lowered` in its lowering column. Every
  remaining notProvenLinear or ExceedsBudget names its blockers or its
  cap decision — `a+\R` stays superlinear-certified at 16.3 million units
  while bare `\R` stays Linear, `(?:a*)*` stays certificateless, and all
  three facts must survive the fix. For patterns already Linear the gate
  is exactly one thing, mechanically: the class does not regress. The
  resource movements are recorded as an informational artifact of the
  report, not gated, because they legitimately go both ways: `aa` — the
  hand-lowered shape of `a{2}`, and the expected result of lowering it —
  measures 25,392 cost / 0 stack / 1,585 memory today against counter-form
  `a{2}` at 63,887 / 3 / 560, so cost and stack fall while the
  conservative constant reservation rises; and bare `\R` does not move at
  all. Both movements are correct; the report shows them; nothing
  forbids them.
- Regenerated Go and JavaScript backends, their suites green, and the
  no-allocation context promise re-verified on lowered patterns
  specifically — the email pattern among them — under the same two
  instrumentations the M5 statement names: Go's allocation counter and
  JavaScript constructor instrumentation.

## Step 4: refreeze and replay

Regenerate the artifact, record the new artifact and corpus hashes in
THEOREMS.md, replay the M6 proofs against them at whatever cost the
sequencing inventory priced, and update README's status paragraph to say
what is now true: the wave 1 guarantee holds with the three named
carve-outs. If any part of this plan is deliberately deferred instead,
README says that instead — the one unacceptable outcome is documents that
describe a mechanism the implementation does not have, which is the state
this plan exists to end.

## Out of scope, on purpose

Four refinements are adjacent and not part of this gate:

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
- Partial lowering. Lowering the `a+` inside `a+\R` buys no Pike
  eligibility while routing is whole-program — though it is not quite
  nothing: the backtracking certificate of `aa*\R` prices marginally
  under `a+\R`'s, 16,238,710 against 16,253,893 cost and 112,448 against
  112,560 memory at n = 1000. A fraction of a percent is not worth a
  second lowering mode; it becomes worth revisiting only if per-region
  routing ever exists.

None of these block the refreeze. All of them get cheaper to evaluate once
the population of backtracking-only patterns is down to the carve-outs.
