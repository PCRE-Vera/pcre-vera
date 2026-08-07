# M8: engine wave 2, compatibility without an unbounded bill

M8 is the first milestone after the frozen wave 1 proof foundation that moves
the engine again. It adds the PCRE constructs that make the library useful for
many existing patterns rather than only for regular ones: atomic groups,
possessive quantifiers, lookaround, `\G`, and backreferences. Those constructs
also put state back into matching. Captures can affect what a later instruction
means, an assertion can run a nested search without consuming, and an atomic
boundary can erase choices that would otherwise survive. Getting the answer
right while losing the resource contract would miss the point of the project.

This plan therefore has three equal objectives:

1. On the surface it admits, agree with the pinned libpcre2 10.47 build in
   compile results, match results, capture registers, preference order, error
   codes and byte offsets. “Supports backreferences” never means that one
   spelling happened to work.
2. Keep every run under the same deterministic cost, stack and scratch-memory
   limits as wave 1. Every new byte examined and every new scratch byte has a
   price, and a preallocated context still performs no match-time allocation.
3. Move the artifact without rewriting history. The completed M7 foundation
   remains independently buildable while the shipped artifact advances, and a
   wave 2 feature cannot enter the default surface before its complete proof
   chain exists.

The order is deliberate. Gates 0 and 1 install the versioning and admission
machinery before a wave 2 spelling can compile. Gates 2 through 7 then land one
vertical feature slice at a time. Nothing moves `wave1-frozen` or
`m7-foundation-20260807`.

## 1. The compatibility target

The reference is the build in `oracle/pcre2-pin.toml`: PCRE2 10.47, the 8-bit
library, non-UTF matching, the C-locale character tables recorded there,
newline and `\R` conventions supplied through the existing API, JIT disabled,
and variable lookbehind capped at 255. Compatibility in M8 means exact
compatibility with that build over:

* all wave 1 syntax and options;
* every spelling listed in section 2 for the wave 2 families;
* the eight compile options and five match options already public;
* the existing five newline conventions and two BSR conventions;
* every valid subject byte string, start offset and admitted option
  combination inside the project's documented portable limits.

For a compile this means the same success or the same PCRE2 error code and byte
offset. A successful compile must expose the same capture count and name table.
For a match it means the same match/no-match answer and every ovector entry,
including captures made inside positive assertions and captures restored by
failed branches. Our `ResourceExceeded`, `PatternTooLarge`, `BadInput`,
`UnsupportedFeature` and `UnsupportedOption` remain our outcomes; the oracle
policy compares PCRE2 only when our call completes inside its own limits and
the construct belongs to the admitted surface.

This is not a claim of compatibility with all of PCRE2. UTF, UCP, conditionals,
`\K`, branch-reset groups `(?|...)`, subroutine calls and recursion, non-atomic
assertions, scan-substring assertions, all four script-run spellings, callouts
and backtracking verbs remain outside M8. A well-formed one is refused as ours.
Its malformed spelling still receives PCRE2's syntax error whenever the parser
has enough of that grammar to know it, preserving the wave 1 rule. Options such
as `DUPNAMES` and `MATCH_UNSET_BACKREF` are not silently approximated: until a
later milestone admits them, the option is `UnsupportedOption`, duplicate
names follow PCRE2's default compile error, and a backreference to an unset
group fails. The public PCRE2 option words, compile-context extra options and
the project's option surface are separate universes; gate 1 records their
exact relationship rather than treating the shim's accepted names as PCRE2's
complete set.

The five newline conventions are a deliberate project subset. PCRE2 10.47
also has `PCRE2_NEWLINE_NUL`, and accepts both the compile-context setting and
the pattern start item `(*NUL)`. M8 implements neither entrance: the API value
is `UnsupportedOption`, the start item is `UnsupportedFeature`, and gated mode
does not change either answer. This explicit exclusion does not change the M7
theorem domain or imply a defect in the frozen engine.

Where the PCRE2 documentation and the pinned executable disagree, the
executable is the compatibility reference. The source files under the pinned
oracle build explain a result; the oracle protocol decides it. Every such
quirk gets a named corpus case so that a later PCRE2 pin can choose explicitly
whether to retain or remove it.

## 2. The exact wave 2 surface

The grammar and semantics below are the scope. The symbolic and alphabetic
forms are aliases and must compile to the same AST; accepting only the first
column would not close the feature.

| Family                   | Spellings admitted in M8                                    | Semantics that must be observable                                                                                                                                                                            |
| ------------------------ | ----------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Atomic group             | `(?>...)`, `(*atomic:...)`                                  | The first successful path through the body commits. Later failure may backtrack before the group, never into it. Captures from the committed path remain and are restored if an outer choice is later taken. |
| Possessive repetition    | `?+`, `*+`, `++`, `{n}+`, `{n,m}+`, `{n,}+`, `{,m}+`        | Equivalent in result and captures to an atomic group around the greedy repetition. `UNGREEDY` does not make a possessive quantifier lazy.                                                                    |
| Positive lookahead       | `(?=...)`, `(*pla:...)`, `(*positive_lookahead:...)`        | Runs atomically at the current position, consumes nothing, retains captures from its first successful path.                                                                                                  |
| Negative lookahead       | `(?!...)`, `(*nla:...)`, `(*negative_lookahead:...)`        | Succeeds only when every body path fails, consumes nothing, and retains no capture made while testing.                                                                                                       |
| Positive lookbehind      | `(?<=...)`, `(*plb:...)`, `(*positive_lookbehind:...)`      | Like positive lookahead, but every top-level branch is tried ending at the current position. Fixed branches may have distinct lengths; variable branches try maximum length first.                           |
| Negative lookbehind      | `(?<!...)`, `(*nlb:...)`, `(*negative_lookbehind:...)`      | Like negative lookahead over the permitted positions behind the current one, with all temporary captures restored.                                                                                           |
| Start-of-match assertion | `\G`                                                        | True exactly when the current matching position equals this call's `startoffset`, not the end of a previous wrapper-level match and not every later bumpalong attempt.                                       |
| Numeric backreference    | `\n`, `\gn`, `\g{n}`, `\g+n`, `\g-n`, `\g{+n}`, `\g{-n}`    | Matches the bytes most recently captured by the resolved group. The existing PCRE2 decimal/octal and forward-reference rules remain exact.                                                                   |
| Named backreference      | `\k<name>`, `\k'name'`, `\k{name}`, `\g{name}`, `(?P=name)` | Resolves to the same numbered group as PCRE2 under the default unique-name rule.                                                                                                                             |

Traditional lookaround is atomic. PCRE2's `(?*...)`, `(?<*...)`, `(*napla:)`
and `(*naplb:)` family is deliberately not smuggled into this table: it has a
different backtracking contract and stays unsupported. The long
`(*non_atomic_positive_lookahead:...)` and
`(*non_atomic_positive_lookbehind:...)` aliases are the same unsupported
family. `(*script_run:...)`, `(*sr:...)`, `(*atomic_script_run:...)` and
`(*asr:...)` are also explicit exclusions; their script restriction is not
observable on the admitted 8-bit non-UTF subject alphabet, so match-result
differentials cannot stand in for parser/admission fixtures.

The following interactions are part of the surface rather than follow-up
polish:

* nested atomic groups and assertions in every sign and direction;
* alternatives, empty branches, empty matches and quantified assertions;
* captures inside positive assertions and their later backreferences;
* capture rollback on failed positive paths and every successful negative
  assertion;
* a reference inside its own repeated group using the previous iteration's
  capture, and forward references permitted by PCRE2's grammar;
* zero-length and unset captures, ASCII caseless comparison as selected at the
  reference site, and backreferences under quantifiers;
* lookbehind before the call's `startoffset` but never before the subject;
* fixed-length lookbehind branches up to PCRE2's 65535 limit, variable-length
  branches no wider than the pinned limit 255, and the exact PCRE2 refusal for
  an unlimited or otherwise unbounded branch;
* `\R` inside lookbehind with width 1..2 per occurrence, including repetition
  up to the variable-width cap; `\X` and genuinely unbounded constructs are
  refused where the pinned build refuses them;
* a backreference inside lookbehind exactly when the uniquely referenced group
  has a finite fixed width; duplicate-name and `MATCH_UNSET_BACKREF` cases stay
  outside M8 with their existing option policy;
* the all-alternatives-`\G` anchoring optimization and wrapper-level find-all,
  including an empty previous match;
* the pinned build's auto-possessification behavior, including the eight 8-bit
  table pairs already recorded in `engine/spec.py` where the optimization is
  observably unsound.

## 3. Two artifact roles, with no “fully proved” shorthand

DESIGN.md currently says that M8 tracks the “newest fully proved artifact” and
the shipped artifact. Before M7R no artifact has a complete S/R/I refinement,
so that phrase has no referent and must not survive into the implementation or
release notes.

M8 uses these terms instead:

* **proof baseline** — the latest immutable artifact capsule whose exact
  theorem inventory has been checked. At M8's start this is the wave 1
  artifact `d60df8a5...` plus the M6 proofs and completed M7 foundation. It is
  not described as fully refined; its Layer I inventory still says one of
  eighty functions proved and one conditional sample.
* **shipped artifact** — the exact generated artifact consumed by the current
  Go and JavaScript backends, with the theorem inventory it actually has. It
  may support additional features only through `allowGatedFeatures`.
* **fully refined artifact** — reserved for a manifest whose complete S, R and
  I chain, including the composed artifact theorem and a complete layer-I
  coverage ledger, is checked by `make verify`. None exists before M7R.

The frozen wave 1 surface remains enabled under the documented 0.x fallback:
layers S and R are proved and Layer I is pinned, decoded, round-tripped and
replayed, but not fully refined. This is an existing, explicitly stated
contract, not evidence that new features may enter the default surface at the
same proof depth. Every wave 2 feature starts gated and stays gated until its
full S/R/I chain exists.

## 4. Gate 0: versioned proof capsules and manifests

This gate lands before any engine edit that changes `gen/engine.tir.json`.
Today `tests/test_freeze.py`, `tests/test_coverage.py`, the Lean artifact
module and `make verify` all read that single live path. Moving it first would
either break M7 or tempt the project to move a historical tag. Gate 0 removes
that choice.

### 4.1 Blob store and logical capsules

Use a content-addressed blob store under a new top-level `proofs/` directory.
A manifest is the capsule: it maps logical build paths to immutable blobs.
The tree does not copy the 55,000-line Lean development, generator and corpora
for every slice.

```text
proofs/
  manifests/
    m7-foundation.v1.json      # role = proof-baseline
    shipped.v1.json            # role = shipped
  blobs/
    sha256/
      <full digest>             # bytes only; one copy for all manifests
```

These are two independent, versioned manifests, not two aliases for one live
file. `VERIFY_MANIFESTS` in the Makefile names exactly the active baseline and
shipped versions. At gate 0 both may map to the same M7 blobs while carrying
different `role` fields; the first wave 2 artifact adds `shipped.v2.json` and
changes only the shipped entry in `VERIFY_MANIFESTS`. Old manifests and
referenced blobs stay in the tree. A published manifest is never edited, and
`wave1-frozen` and both M7 tags retain their existing meanings.

Verification materializes each logical capsule in a fresh build directory,
using hard links where supported and copies otherwise. The self-contained Lean
and generator source closures are intentional. A list of yesterday's source
hashes cannot be built after the live source changes, and a verifier that
checks out a tag depends on Git metadata an exported source archive does not
carry. Dependencies shared by manifests are blobs too. Every byte needed to
reproduce an artifact, build its proofs and replay its recorded corpus is
present in the repository and named by the manifest; verification never
downloads it.

### 4.2 Manifest schema

The schema is strict: unknown, duplicate, missing or wrongly typed fields are
errors. Logical paths are normalized and may not escape the materialized root.
Every blob path is derived from its digest rather than supplied by the
manifest. At minimum a manifest carries:

```text
schema, manifestVersion, capsuleName, role, artifactVersion
artifact.logicalPath, artifact.sha256, artifact.schema
generator.implementation, generator.python, generator.lockSha256
generator.sourceFiles[logical path -> sha256], generator.revision
generator.environment[PYTHONHASHSEED, LC_ALL, TZ]
backends.go[path -> sha256], backends.javascript[path -> sha256]
lean.root, lean.toolchain, lean.files[path -> sha256]
inventory.path, inventory.sha256
featureLedger.path, featureLedger.sha256
compatibilityFixture.path, compatibilityFixture.sha256  # schema v2, gate 1+
features.default[], features.gated[], features.unsupported[]
compileCapabilities.default[], compileCapabilities.gated[]
corpora[path -> sha256], sweep.manifestSha256, sweep.command
oracle.mode, oracle.pinPath, oracle.pinSha256, oracle.version, oracle.buildId
oracle.shimFiles[path -> sha256], oracle.expectations[path -> sha256]
```

`generator.revision` is provenance, never a substitute for the source hashes.
The generator source list is the transitive repository-local closure used by
the capsule's build entry, not a hand-maintained selection of files believed
to matter. `generator.python` pins the complete CPython version, and
`generator.lockSha256` pins `uv.lock`; regeneration refuses a different
interpreter rather than hoping serialization is stable across it. Generator
code may not depend on hash-table iteration, locale, timezone, filesystem
enumeration or absolute paths. The fixed environment above and permutation
tests enforce that rule. The manifest's feature sets are redundant on purpose:
the verifier derives them from the pinned feature ledger and rejects
disagreement.
The gate-0 M7 baseline uses the initial manifest schema and does not pretend to
carry a surface fixture that gate 1 has not built. Gate 1 bumps the shipped
manifest schema and makes `compatibilityFixture` mandatory for that and every
later shipped capsule; the old baseline manifest remains immutable and its
absence is versioned, not treated as an empty universe.
The manifest hash is computed from its canonical JSON bytes and reported by
`make verify` and in the tag annotation. It is not embedded in any file whose
hash the manifest itself contains, which would create a hash cycle. Generated
backend headers record the artifact and feature-ledger hashes; the manifest in
turn records the backend hashes. Artifact identity remains the artifact's
SHA-256, not the manifest hash; the two answer different questions.

The theorem inventory is machine-readable. Each claim names its layer, theorem
identifier, Lean module and source hash, its domain, and whether it is a proof,
an interpreter check, a replay or a differential test. An artifact `#guard`
is never recorded as a theorem. Layer-I per-function entries remain generated
from the artifact's call graph, so adding or removing a helper changes the
inventory before prose can forget it.

### 4.3 Independent verification

`make verify` validates and builds the proof baseline and shipped artifact in
separate build directories. For each active manifest it must:

1. parse the strict schema and recompute the manifest's file closure;
2. recompute every blob, artifact, corpus, compatibility-fixture and
   oracle-provenance file hash;
3. decode the artifact with that capsule's decoder, print it back to identical
   bytes, and settle the canonicality and fuel guards;
4. build that capsule's Lean package from sources inside the capsule;
5. check that every named theorem exists in the named module and that the
   inventory's coverage domain equals the artifact-derived domain;
6. require feature keys to be unique, dependencies to be present, and, for a
   schema-v2 capsule, the source-derived syntax and option universes to agree
   with the fixture and generated parser/API tables; require the
   default/gated/unsupported sets to form the exact partition derived from the
   pinned ledger and proof inventory;
   derive both compile-capability masks and reject any default opcode
   capability whose required proof chain is absent;
7. replay the capsule's recorded expectations through the reference engine it
   names;
8. regenerate that capsule's artifact and backends from its captured generator
   closure and require byte identity; for the shipped capsule, additionally
   require the live generated files to equal those bytes.

The current forced rebuild of the `include_str` artifact module remains, but
becomes a per-capsule operation. A shared `.olean` cache may be used only when
its key includes the complete source-set hash and artifact hash.

The oracle fields are provenance. Set `oracle.mode` to
`recorded-expectations`. `make verify` hashes the pin, shim sources, recorded
expectations and build identity but neither downloads nor rebuilds PCRE2. A
live oracle comparison belongs to `make check`, the per-slice sweep, or a
pin-refresh job. Capsule replay is deliberately offline.

Five tamper tests are part of the gate and operate on scratch copies, never on
the checkout:

* replace a valid artifact with another valid artifact and update the recorded
  artifact hash: regeneration, coverage or source-relation verification fails;
* change only a recorded hash: the named field fails;
* remove, invent or stale one theorem-inventory entry: theorem or coverage
  verification fails;
* remove one listed Lean source, including one not imported by the default
  root: file-closure verification fails;
* put a wave 2 feature in `features.default` while its I chain is incomplete:
  admission verification fails and names the feature.

The last tamper case is run a second way by leaving the syntax feature gated
but putting its opcode in `compileCapabilities.default`; capability
verification must fail and name the same missing proof chain.

Also test swapped active manifests, a logical path escaping its materialized
root, an unlisted file, the wrong oracle pin, and stale generated backend
headers. Once gate 1 supplies the surface fixture, also delete one source row,
regularize the exceptional `pso_list` row zero, add an unpartitioned public
option, and change a shim projection without changing policy; each failure
names the broken universe or join. The five required failures above are the
gate-0 done criterion; these additional cases keep later manifests from making
the schema the weak link.

Done when: the live generator can be changed in a scratch branch, producing a
different shipped artifact, while `make verify` still builds the immutable M7
baseline and then independently verifies the new shipped capsule; all tamper
tests fail for the intended reason; `wave1-frozen` and
`m7-foundation-20260807` still resolve to their original objects.

`make verify-shipped` materializes and builds only the shipped manifest and is
what routine `make check` and pull-request CI depend on. `make verify` always
builds both manifests independently and is mandatory for tag, release and
nightly jobs; any change under `proofs/`, to the verifier, or to a manifest
also triggers it on the pull request. This split changes cadence, not the
release gate. The two capsule builds use disjoint materialized roots and may
run concurrently only after a measured peak-memory check; the default remains
sequential on unqualified hosts. Scope the Makefile's `.NOTPARALLEL` protection
to oracle-producing targets rather than deleting it, because the live oracle
build remains a shared resource even though capsule verification is offline.

## 5. Gate 1: `allowGatedFeatures` and the feature ledger

The admission boundary lands after syntax and reference validation but before
`compile` can return a successful wave 2 pattern. DESIGN.md's provisional name
`allowUnproved` overclaims because the default wave 1 surface itself uses the
documented M7 foundation fallback. Change the design before publishing an API:
the option is `allowGatedFeatures`, named for the policy it actually bypasses.
It is engine policy, not a PCRE2 compile option. It therefore travels as a
separate argument through the Python driver, TIR `compile` entry, Go `Options`
and JavaScript compile options; it consumes no bit in the PCRE2 option mask and
is never sent to the oracle.

The parser recognizes all grammar needed to distinguish a valid wave 2
construct from a malformed one and records, in source order, the feature and
byte offset of each valid gated construct. It finishes PCRE2 syntax,
reference, bound and group validation first. A genuine PCRE2 compile error
therefore beats the policy refusal exactly as it did when the construct was
unsupported. Only a well-formed tree reaches admission:

```text
parse and validate
  -> derive required feature set and first source offset per feature
  -> choose the default or gated compile-capability set
  -> if every required feature is admitted by that set, compile with that set
  -> else UnsupportedFeature at the earliest unavailable feature offset
```

Before replacing the parser's current blanket refusal of `(*...)`, derive the
closed compatibility universes from the pinned source into a versioned
`conformance/pcre2-surface.json`. The project hand-maintains the policy applied
to those universes, never the universes themselves. For PCRE2 10.47 the source
fixture contains:

* the 23 `pso_list` start-item rows as raw
  `(token, declaredLength, type, value)` entries;
* the 19 parallel `alasnames`/`alasmeta` alpha-assertion rows;
* the nine parallel `verbnames`/`verbs` rows, including the explicit empty
  name, as `(name, declaredLength, baseMeta, hasArgRaw)`;
* the 31 symbols in `PUBLIC_COMPILE_OPTIONS`, the 17 in
  `PUBLIC_COMPILE_EXTRA_OPTIONS`, and the 12 in `PUBLIC_MATCH_OPTIONS`,
  resolving their definitions from the pinned public header. Options for JIT,
  DFA, substitute and other PCRE2 entry points are different APIs and remain
  outside these partitions.

Option membership comes from the executable public masks, not from the layout
or prose comments of `pcre2.h`. In particular, the apparent match-option block
contains 19 definitions: nine accepted by `pcre2_match()`, two DFA-only and
eight substitute-only. Read the 12 symbols in `PUBLIC_MATCH_OPTIONS` from
`pcre2_match.c`—three shared with compile and nine match-only—and resolve them
against the header. Likewise expand both `PUBLIC_COMPILE_OPTIONS` and its
`PUBLIC_LITERAL_COMPILE_OPTIONS` submask to obtain 31, and expand
`PUBLIC_COMPILE_EXTRA_OPTIONS` through
`PUBLIC_LITERAL_COMPILE_EXTRA_OPTIONS` to obtain 17. The extractor carries each
row's source mask and constant identity, but no hand-written per-option target
classification decides membership. Adding a header definition outside these
masks does not change an API universe; adding or removing a symbol in a public
mask changes the cardinality and requires a reviewed policy update.

The extractor is deliberately strict. The first `pso_list` initializer is the
only irregular source row: `STRING_UTFn_RIGHTPAR` supplies both token and
length, so it has three literal fields where the other 22 have four. Require
that form at row zero, reject it anywhere else, and reject an ordinary-looking
row zero rather than guessing how columns moved. Preserve delimiters inside
the raw token and its declared length. Normalization removes exactly the
delimiter prescribed by the row shape—`)` for a closed token, `=` for a
decimal-limit prefix—and refuses a missing, doubled or wrong delimiter. A
mutation that regularizes row zero or corrupts `CR)` to `CR))` must fail the
extractor, not produce plausible data.

Names, not lengths, are keys. Declared lengths are checked against the pinned
bytes, and exact names are unique within a source table; equal lengths such as
`MARK`, `FAIL`, `SKIP` and `THEN` do not identify a row. The parser scans the
whole name through its required `:` or `)` terminator and performs an exact
lookup. No admitted-name prefix test is permitted: `atomic` is a proper prefix
of the unsupported `atomic_script_run`, the one admitted-to-unsupported prefix
collision in the alpha table.

The alpha rows collapse to ten base constructs. The five M8 constructs are
`META_LOOKAHEAD`, `META_LOOKBEHIND`, `META_LOOKAHEADNOT`,
`META_LOOKBEHINDNOT` and `META_ATOMIC`; five remain unsupported:
`META_LOOKAHEAD_NA`, `META_LOOKBEHIND_NA`, `META_SCS`, `META_SCRIPT_RUN` and
`META_ATOMIC_SCRIPT_RUN`. This is nine admitted names and ten unsupported
names, an exact disjoint partition of all 19. Shared base meta codes generate
equivalence cases among alphabetic aliases. Separate cross-form tests still
prove that the symbolic spellings in section 2 and their alphabetic aliases
produce the same semantic AST constructor and feature key; the alpha table
does not contain the symbolic parser arms and therefore cannot establish that
half by itself.

All nine verb names remain unsupported, but their grammar is still parsed far
enough to preserve PCRE2's error precedence. `hasArgRaw` is a signed tri-state,
restricted to the literal values `-1`, `0` and `1`, never a Boolean:

* `1` requires a non-empty argument;
* `-1` permits no argument or emits a preceding `META_MARK` for a non-empty
  one;
* `0` permits no argument or selects the arithmetically bumped meta variant for
  a non-empty one.

An empty argument normalizes to absent before that rule. Generated alias tests
compare equal argument forms and their normalized meta sequences, not base
codes alone: the empty name and `MARK` agree only on non-empty-argument forms,
while `F` and `FAIL` agree on absent, empty and non-empty forms. Pin all four
mandatory-argument failures—`MARK` and the empty shorthand, each absent and
empty—with error 166 and their distinct closing-parenthesis offsets. Pin
`(*atomicx:...)` and `(*atomic_:...)` at error 195 and offset 9. A valid
`(*:abc)` selects the empty-name `META_MARK` row and remains unsupported even
in gated mode. All four script-run spellings remain unsupported in gated mode,
so `(*atomic_script_run:a*)ab` can never compile as `(*atomic:a*)ab` merely
because their byte-mode match answers coincide. Keep `(*)` outside all three
extracted tables as an explicit `sourceUniverse: null` ordinary-group routing
fixture; `(*)` and `a(*)b` receive error 109 at offsets 2 and 3.

The start-item table is its own route before ordinary pattern parsing.
Normalize aliases by `(type, value, parameter shape)`, not `type` alone:
`UTF8)` and `UTF)` are aliases in this pinned 8-bit build, as are
`LIMIT_RECURSION=` and `LIMIT_DEPTH=`, while `UCP)` shares `PSO_OPT` but not
the value. `PCRE2_EXTRA_CASELESS_RESTRICT` and
`PCRE2_EXTRA_TURKISH_CASING` each have two entrances: their identities occur
in `PUBLIC_COMPILE_EXTRA_OPTIONS`, while the two `PSO_XOPT` rows set the same
semantic options through pattern text. Keep one semantic policy identity for
each option but two distinct admission routes; neither route is admitted in
M8. Gate 3 admits the `NO_AUTO_POSSESS)` start item. The other 22 rows remain
explicitly unsupported unless a later reviewed slice changes their policy.
Test a valid start item, the same token mid-pattern, an exact-name extension,
consecutive start items, and valid, empty, malformed and overflowing
decimal-limit arguments with PCRE2's code and closing-parenthesis offset. The
named guards include mid-pattern `a(*NO_AUTO_POSSESS)` and
`(*NO_AUTO_POSSESSX)a` at error 160/offset 18, truncated
`(*NO_AUTO_POSSES)a` at offset 16, empty `(*LIMIT_DEPTH=)a` at offset 14 and
the pinned overflowing decimal fixture at offset 23.

The shim is a protocol projection, not an authority. Its four `option_entry`
tables currently expose 29 compile options, eight match options, six newline
names and two BSR names. The pinned public masks contain 31 compile and 12
match options: the shim intentionally omits `ALT_EXTENDED_CLASS` and
`MATCH_INVALID_UTF` from compile, and `PARTIAL_HARD`, `PARTIAL_SOFT`,
`COPY_MATCHED_SUBJECT` and `DISABLE_RECURSELOOP_CHECK` from match. Assert those
exact protocol complements. Then assert the engine policy partitions the full
source universes, while separately checking the shim projections:

```text
public compile 31 = engine 8 + unsupported 23
shim compile   29 = engine 8 + unsupported-in-shim 21
public compile-extra 17 = engine 0 + unsupported 17
public match   12 = engine 5 + unsupported 7
shim match      8 = engine 5 + unsupported-in-shim 3
PSO_NL/shim newline 6 = engine newline 5 + {NUL}
PSO_BSR/shim BSR     2 = engine BSR 2 + {}
```

These are gate-1 counts; a later slice such as gate 3 changes a policy subset
and therefore the shipped fixture/manifest, never the source-universe count.
Join policy by exact names because the engine's internal option and newline
ordinals are not PCRE2's constants. Join each shim name and PCRE2 constant
identity back to the source-derived row before partitioning it; agreement
between two project-maintained tables cannot prove completeness. The API value
`NUL` and the `(*NUL)` syntax route have distinct admission entries under one
unsupported semantic convention. Gated mode admits neither.

`oracle-verify` re-extracts the fixture from the pinned source and compares it
byte for byte. Offline capsule verification hashes the committed fixture and
joins it to the feature ledger, generated parser tables, the four shim tables
and all three public APIs without downloading PCRE2. Cardinality, row-shape,
alias, missing-member, duplicate, substituted-row and prefix-collision
mutations are required failures. A header-only option belonging to DFA or
substitute must not enter the match universe, while a mutation adding the same
symbol to `PUBLIC_MATCH_OPTIONS` must change the extracted count and fail the
old fixture. Removing either `PSO_XOPT` row must fail its route join without
removing the corresponding compile-extra identity; removing that identity from
`PUBLIC_COMPILE_EXTRA_OPTIONS` must fail in the opposite direction. A pin
refresh that adds or removes a public option or syntax row therefore stops for
an explicit policy decision instead of silently changing an uncounted
complement.

`allowGatedFeatures` selects the gated compile-capability set. Its first effect
is admission: an implemented gated syntax family may compile. Its second is
code generation: a semantics-preserving optimization whose emitted opcode is
gated may be omitted in default mode and applied in gated mode. The same
pattern text can therefore produce different bytecode, matcher routing,
certificates and `worstCaseCost`/stack/memory answers in the two modes. Where
both modes admit the pattern, their public match answer and captures must be
equal under the named S/R equivalence theorem; that equality is tested as well
as proved. This is a compile-time choice, not mutable match behavior.

The option never bypasses a syntax error, an unimplemented feature, a size cap,
the TIR validator, the certificate checker, hard runtime limits, or backend
argument validation. A caller cannot use it to request non-atomic assertions,
recursion or any other out-of-scope feature.

Add a canonical `conformance/features.json` with one row per feature. The row
contains the syntax-family identifier, implementation status, required
artifact version, S status, R status, I status, exact theorem names, default
status, whether `allowGatedFeatures` admits it, and the code-generation
capabilities it may emit in default and gated modes. A capsule carries the
exact ledger used to generate it. Generation takes that path explicitly and
emits closed admission and compile-capability masks into TIR; neither matcher
reads JSON at runtime. The shipped capsule's ledger must equal the live
`conformance/features.json`, and the two active manifests repeat the three
feature sets and both capability sets so verification can join every
representation and reject drift. For a wave 2 row:

```text
default = true  iff  implementation = complete
                    and S = complete
                    and R = complete
                    and I = complete
                    and every named proof belongs to the shipped capsule
```

A wave 2 compile capability is in the default mask only if every opcode it may
emit has the same complete chain. The gated mask may include an implemented
opcode with an incomplete chain, but only when the corresponding feature row
is gated and the manifest names every gap.

The wave 1 rows carry an explicit `m7-foundation-fallback` admission basis,
which preserves today's default API without pretending their I chain is
complete. No wave 2 row may use that basis.

The ledger is the sole editable source of admission state. Hand-written
backend conditionals, a second feature list in the parser, or a release-only
override are forbidden. The parser produces a bitset plus first-offset table;
the generated admission function consumes that bitset and the closed masks,
and code generation consumes the selected capability mask. Changing a feature
from gated to default, or admitting one of its emitted opcodes to the default
capability set, therefore changes the generated artifact and requires a new
shipped capsule whose inventory proves the change.

The public APIs default the policy to false: Python takes a trailing
keyword-only `allow_gated_features=False`, Go adds the zero-valued
`Options.AllowGatedFeatures`, and JavaScript accepts optional
`allowGatedFeatures`
defaulting to `false`. Existing positional option masks and zero-value calls do
not change.
An `UnsupportedFeature` result carries the stable feature key, byte offset and
whether gated mode would admit it, so callers can distinguish “available but
gated” from “not implemented.” The generated declarations, type definitions
and examples make the gated mode visible. Compiled-pattern behavior
does not depend on a mutable global policy: the decision is taken at compile
time, and a compiled pattern is immutable afterwards.

Done when: before any actual wave 2 implementation is enabled, the pinned
surface fixture passes every source/shim/engine partition and mutation above,
and one shared pure admission function is exercised through the TIR
interpreter and both generated backends with synthetic feature masks, proving
all four paths—default refusal, explicit gated-mode success for an
implemented/test-only feature, refusal of an unimplemented feature even in
gated mode, and default admission only after a complete mock S/R/I inventory.
Real, well-formed wave 2 syntax still refuses while its implementation bit is
false, even in gated mode; malformed forms prove the parser's error precedence
and offsets. The live parser continues its blanket `(*...)` refusal until the
fixture, exact lookup and routing tests have passed on a behavior-neutral
artifact.

The mock rows live only in strict fixture ledgers under
`tests/fixtures/admission/`, using reserved `test.*` feature keys. Tests feed
one fixture ledger to the generator and build a test-only TIR/Go/JavaScript
artifact in a scratch directory. They never modify `conformance/features.json`
or `gen/`, and production manifest validation rejects the reserved namespace.
One fixture also selects two semantics-equivalent toy programs with distinct
program hashes and analysis answers, proving that the selected capability mask
reaches the TIR, Go and JavaScript execution paths while match results stay
equal. Thus no test-only
row, mask or policy reaches a public artifact or API. Because the compile entry
changes, this gate creates the first new shipped capsule and manifest; the
baseline manifest still builds the M7 entry independently.

## 6. Common engine design for the stateful features

Atomic groups and assertions need nested control state, but they do not need a
copy of the captures or backtrack stack. Add a bounded control-frame vector.
One frame carries only scalar data:

```text
kind, return pc, original subject position,
backtrack-stack watermark, undo-trail watermark,
and the assertion's sign/direction metadata
```

The compiler knows the maximum simultaneously active frame depth from the AST.
It records that number on the compiled pattern. Context creation reserves the
exact deterministic growth-schedule capacity; plain calls charge any growth;
the memory certificate pays for the vector and growth overlap. No operation
copies an ovector, register file, subject slice or stack to enter an atomic
group or assertion.

Failure becomes frame-aware. If the backtrack stack has an entry above the top
frame's watermark, ordinary backtracking continues inside the construct. At
the watermark, the construct's failure action runs before any outer choice is
touched. Successful atomic exit and successful positive assertion truncate
the internal choice stack directly to the watermark. Truncation is constant
time. The existing undo trail remains the authority for captures:

* atomic success retains its writes; an outer backtrack later replays them;
* atomic exhaustion replays to the frame's trail watermark before failing
  outward;
* positive assertion success retains writes and restores only the subject
  position;
* negative assertion success and every failed assertion path replay to the
  frame's trail watermark;
* when no outer choice or live frame can need undo, the trail is truncated so
  a long deterministic run does not retain dead history.

This changes the current `save` condition in one precise way: a register write
is logged when either the backtrack stack or the control-frame stack is
nonempty. A negative assertion with no ordinary choice point still needs its
writes undone. Tests exercise that case directly and also an atomic or positive
assertion whose retained write is later undone by an outer choice.

Every replay is pre-charged at `REG_SIZE` per restored register, as in wave 1.
Every control push, pop, truncate and width-candidate attempt receives an
explicit cost rule before code is emitted. The control-vector capacity is
part of `worstCaseMemory`; if a separate control depth is exposed internally,
the public `worstCaseStackEntries` remains the bound on backtrack entries it
has always documented, while the control vector is paid in memory. No hidden
host stack or recursive matcher call is introduced.

Gate 2a extends the AST, bytecode, lookaround side table, region kinds and
dry-run size vector together, once for the whole wave. The expected bytecode
vocabulary is `AtomicStart`,
`AtomicEnd`, `LookStart`, `LookEnd`, `BackRef` and `AssertG`, with a side-table
entry carrying look direction, sign, branch widths and control-flow targets.
Exact names may change before the first artifact, but the representation must
meet these rules:

* one bytecode is consumed by both matchers;
* every target and side-table index is checked and included in compiler-output
  well-formedness;
* the lowering dry run prices every new code, region, table, register, job,
  patch, visit and fuel entry without expanding a candidate;
* the emitter asserts the extended predicted vector entry by entry;
* width analysis, feature collection and auto-possessification each use an
  explicit arena walk with closed fuel and no copied subtree or recursive host
  call; their compile-time work and scratch have cap-adjacent tests;
* new caps have a fitting and one-past test, and an otherwise valid pattern
  over a cap returns `PatternTooLarge`, never an internal trap;
* the checker reads the new region shape back against bytecode rather than
  trusting the compiler's label.

`pike_ok` rejects `BackRef`, every lookaround opcode and every atomic boundary
through M8. Possessive repetition inherits the atomic rejection. `AssertG`
also remains rejected for the milestone: it is state-free in isolation and
does not break the pc-keyed visited set, but threading the call's original
`startoffset` through Pike and its refinement relation is a separately priced
optimization. No slice admits it incidentally. Matcher routing and complexity
classification remain separate columns in every report.

## 7. The vertical-slice rule

After gates 0 and 1, the structural gate lands once, then features land in
this order:

1. gate 2a: every wave 2 AST, opcode, region and semantic signature;
2. gate 2b: atomic groups;
3. gate 3: possessive quantifiers and exact auto-possessification;
4. gate 4: positive and negative lookahead;
5. gate 5: `\G`;
6. gate 6: backreferences;
7. gate 7: positive and negative bounded lookbehind.

Backreferences move before lookbehind because PCRE2 admits a backreference in
lookbehind when its uniquely referenced group has a fixed width. Gate 7 spends
the group-width rule gate 6 establishes instead of closing with a known hole.

Each slice is one semantic change, not a parser commit followed weeks later by
a matcher. Its done-list is:

1. all listed spellings and invalid near-spellings in the parser, with PCRE2
   errors and offsets before policy admission;
2. activation of the already-declared AST, compiler, bytecode/side-table and
   region cases, with shape validation and all size caps;
3. backtracking execution, failure restoration, hard limits and usage;
4. BOUNDS.md rule first, then independent analyzer and checker changes;
5. context reservation and no-growth behavior;
6. Python, Go and JavaScript API/conformance results;
7. hand-written oracle cases, exhaustive small subjects, generated grammar,
   minimization and promotion routes;
8. layer S semantics and totality, layer R compiler/VM semantics,
   refinement, termination and resource theorems forming the complete S/R row
   of section 14;
9. local Layer I progress recorded by exact theorem name and domain, never
   inferred from a successful artifact decode;
10. feature ledger, shipped capsule, documentation and benchmark report.

A review happens at each slice boundary. It checks preference and capture
semantics, failure restoration, error precedence, bytecode shape, checker
independence, sufficient bounds, context no-growth, Pike rejection, and the
manifest admission row. A green semantic corpus is not a resource review, and
a green checker corpus is not a proof of compiler output.

## 8. Gate 2a: the one structural wave

This gate lands every wave 2 representation change before any feature is
implemented. The current development has 21 `Ast` constructors, 24 `Op`
constructors, nineteen exhaustive definitions over `Ast`, fourteen over `Op`,
and more than one hundred additional case-analysis sites. `Covered`, `FragAt`
and `Frag` mirror the AST, and 23 proofs induct over them in the three largest
proof files. Adding one constructor per feature would repay that structural
repair six times.

Gate 2a has one mandatory internal review seam: premises before constructors.
It remains one gate and one structural milestone, but the first checkpoint is
build-green before any inductive grows.

### Gate 2a.0: premise and call-context preflight

Add `startoffset` to layer S's per-call semantic context and thread it through
the roughly 102 `SCtx` construction/use sites and `mctx` in
`Proofs/Refine.lean`. It is supplied afresh by each match and is never stored in
the reusable public context. Attach the permanent `PikeSafe re` premise to the
Pike refinement, termination and bound theorem interfaces while the opcode set
is unchanged. At this checkpoint `PikeSafe` is satisfied by every currently
Pike-eligible program, so the existing wave 1 theorems must reappear as
corollaries without an inductive repair or feature exclusion.

Stop for a semantic-boundary review here. The old corpus, complete Lean build,
Pike resource results and cross-matcher agreement must pass before adding an
`Ast`, `Op`, region or shadow-inductive constructor. This isolates the
signature and theorem-premise churn from the exhaustive structural churn and
provides the early go/no-go measurement gate 2a otherwise lacks.

### Gate 2a.1: constructors and executable-domain exclusions

Then add, in the rest of the same gate and commit series:

* all atomic, lookaround, backreference and `\G` AST forms, including a
  repetition mode that can represent possessive quantifiers without changing
  `rep` again later;
* all corresponding opcodes, region kinds, lookaround metadata, width records,
  feature bits, dry-run vector entries and decoder/printer variants;
* the bounded control-frame vector and the register-save rule of section 6;
* lookaround as arms of `search`, not `assertionHolds`. The latter remains the
  Bool-valued leaf-anchor helper; nested sub-search, registers and ordered
  results require the former;
* the revised termination measure for nested assertion searches and bounded
  lookbehind candidates, plus a fresh audit of `suffFuel`. Backreference byte
  comparison either uses a total bounded helper with a `≤ subject.size` lemma
  or spends explicit comparison fuel; it is not silently covered by the old
  repetition-only argument;
* the new cases of `Covered`, `FragAt` and `Frag`, and all exhaustive matches in
  S, R, the compiler, bounds and refinement developments.

`search` already receives `regs`, so backreferences do not add another
semantic argument. The `SCtx.startoffset` addition and lookaround recursion are
the two signature-level changes, and they happen here before feature proofs
start.

The structural theorem interface is feature-indexed. `AstEnabled fs a` and
`ReEnabled fs re` describe exactly the constructors/opcodes admitted by one
ledger feature set; compiler success proves both. Unimplemented wave 2 syntax
is fully parsed and validated, then rejected by admission before code
generation. Its cases are eliminated in implementation-specific proofs by
these predicates. A feature's S/R row is not complete until the theorem is
instantiated with that feature enabled and no premise excludes it.

Pike gets a separate, permanent domain predicate, `PikeSafe re`, that excludes
capture-dependent and control-frame opcodes. The existing seen-by-pc argument
is unsound for backreferences because two threads at one pc can carry different
registers. State the Pike refinement, termination and bounds theorems under
`PikeSafe`; prove `pike_ok re = true -> PikeSafe re`; and prove compilation
routes every non-safe program to the backtracker. This is an authorized
matcher-domain premise, not the forbidden act of excluding a feature from the
backtracking theorem and calling that feature proved. Preserve the current
wave 1 Pike theorems as corollaries.

No placeholder opcode is executable. Its VM arm returns the internal
bad-program result, `ReEnabled` excludes it, `pike_ok` rejects it, and parser
admission prevents its emission until its slice. This lets every exhaustive
definition compile without claiming semantics the slice has not supplied.

Done when: the 2a.0 review is recorded; the full Lean build and old corpus pass
after the subsequent single structural churn; all later feature variants
already exist; every unimplemented wave 2 pattern returns
`UnsupportedFeature`; the feature-indexed and Pike-domain theorems preserve the
old wave 1 corollaries; and the complete case-site census and actual proof-line
churn are recorded before gate 2b is scheduled. If the whole gate exceeds ten
reviewed rounds, stop before 2b and decide explicitly whether the structural
foundation becomes its own milestone; do not recover the schedule by dropping
constructors, weakening `PikeSafe`, or leaving an old theorem uninstantiated.

### Gate 2b: atomic groups

Atomic grouping is first because it is the primitive both assertions and
possessive repetition spend. Activate the atomic AST and opcode cases declared
by gate 2a. Compilation opens an atomic region at `AtomicStart`, compiles the
body unchanged, emits `AtomicEnd`, and closes the region. The VM frame records
the choice and trail watermarks. On success it discards choices made inside the
group in constant time; on local exhaustion it removes the frame and fails
outward with the register state restored by the ordinary trail.

Layer S defines an atomic body as the first thread of the body's existing
priority-ordered result list, if one exists. That definition retains the
captures of the committed thread and makes preference observable. Prove
totality and fuel stability for the new constructor, compile refinement for
both atomic spellings, VM refinement for nesting and outer backtracking, and
termination.

The certificate rule charges the worst work, stack and trail needed to find a
success or prove failure inside the body, but caps forward ambiguity at one.
This is where atomic grouping earns both its semantic effect and its
performance: downstream work is not multiplied by paths that have been cut.
The checker validates the matching start/end pair and region nesting before it
uses that rule.

The oracle matrix includes a later suffix forcing failure, an outer
alternative recovering after that failure, captures changed on discarded
paths, nested atomics, empty bodies, quantified atomics, lazy repetition
inside an atomic body, anchors and `\R`. Adversarial cases demonstrate that
`(?>a*)a` and `a*a` differ where PCRE2 says they do and that a large internal
choice set is discarded without a linear scan at `AtomicEnd`.

Done when: both spellings agree with PCRE2 across the matrix and generated
cases; the S and R rows for atomic groups are complete; every atomic pattern
is still gated because I is incomplete; bounds cover the new frame
and region; context matches allocate nothing; the old wave 1 corpus and its
selected paths are unchanged.

## 9. Gate 3: possessive quantifiers and auto-possessification

Open the gate with a one-reviewed-round oracle-only feasibility spike before
changing the optimizer or generated artifact. Add the smallest pinned-source
diagnostic that dumps the final opcode vector for one auto-possessed pattern
and one pattern the pass leaves unchanged; compare both with a compile under
`(*NO_AUTO_POSSESS)`, and tie the known-bad `\S*\R`/`\x85` decision to its
observable match difference. The diagnostic reads the completed code vector
after the single `PRIV(auto_possessify)` post-pass. If a trustworthy dump and
opcode walk do not exist at the end of that round, stop and re-estimate gate 3
rather than beginning the AST re-derivation on an unobservable oracle.

Parse every suffix in section 2, including `{,m}+`, and preserve PCRE2's error
precedence around “nothing to repeat”, malformed braces, a lazy marker followed
by `+`, and repeated quantifier suffixes. A possessive quantifier is always
greedy after inline and whole-pattern `UNGREEDY` processing.

The AST records possessiveness as a distinct repetition mode. Compilation
uses the ordinary repetition construction inside an atomic boundary; it does
not copy the repeated body beyond the lowering already priced, and it does not
introduce a second matcher implementation. Prove the S-level equivalence to
the corresponding atomic greedy repetition, so the atomic S/R results compose
instead of being duplicated for every quantifier spelling.

This slice also removes the wave 1 coarse auto-possess refusal. This is a
re-derivation of the pinned `pcre2_auto_possess.c` decision, not a
transcription: PCRE2 decides over its opcode stream, including `OP_EXACT` and
`OP_UPTO`, while this engine later lowers counted repetitions to star form.
Make the decision over a pre-lowering, source-ordered normalized AST that still
distinguishes every quantifier form, group boundary, option scope and adjacent
item. Document the correspondence from each PCRE2 decision input to that
representation. PCRE2-default optimization under `allowGatedFeatures` must
reproduce the pinned 10.47 behavior, including the exact 8-bit character
identities and every case where its static table is observably wrong. The
current pinned domain projects those cases onto eight distinct identity pairs;
eight is a checked projection, not the definition of the unsafe set.

Match results cannot observe a wrong decision for the semantics-preserving
majority. Extend the pinned-source oracle shim with a diagnostic compile mode
that walks PCRE2's internal opcode stream and returns a normalized dump of the
repeat opcodes, including `OP_POSSTAR`, `OP_POSPLUS`, `OP_POSQUERY`,
`OP_POSUPTO`, their `*I`/negated forms, `OP_TYPEPOS*` and `OP_CRPOS*`. This
diagnostic is oracle-only, tied to the internal layout of the pinned source,
versioned in the protocol and hashed by the manifest; it is not a public PCRE2
API claim. Compile every adjacency
fixture once normally and once with auto-possess disabled, then compare the
decision dump as well as match results. A mutation that flips any decision in
the re-derived table must fail even when semantics do not change.
Update the shim's trust-boundary comment accordingly: ordinary compile/match
answers still use public APIs, while this one diagnostic is explicitly a
pinned-source-layout observation.

Make the safe/unsafe partition structural. Define the finite auto-possess
decision domain—repeated opcode identity, following identity, option scope,
case mode, newline/BSR facts and group adjacency—in layer S. `AutoSafe c` is
the decidable condition for which `Matches (possessify c) = Matches c` is
proved. Define `AutoUnsafe c` as `pcreDecides c && !AutoSafe c`, enumerate it
from that definition, and generate Python's unsafe classifier from the
enumeration. The current `AP_UNSOUND` map is no longer a hand-written source of
truth; any compressed lookup table carries a proof/test that it equals the
enumeration. The manifest pins the concrete domain/table hash, its full case
count, and the cardinality of its identity-pair projection; for PCRE2 10.47
8-bit that projection guard is eight. Exhaust the finite concrete domain in
Lean and in the oracle-decision matrix. If a ninth identity pair exists, it
enters `AutoUnsafe` automatically and changes the projection guard, manifest
and default-refusal fixtures instead of being misclassified as proved safe.

While atomic Layer I remains incomplete, an ungated compile must not emit its
opcodes merely because auto-possess chose them. For an `AutoSafe` decision the
ungated compiler omits the optimization and keeps the proved wave 1 program.
For every derived `AutoUnsafe` decision it returns deterministic
`UnsupportedFeature`. The gated path applies the exact pinned decision.
Consequently “decision agreement” below refers to the gated optimizer; the
default surface remains exactly the manifest's admitted proof basis. Once the
atomic I chain is complete, a later manifest may enable the same optimizer by
default without changing its table.

Add the PCRE2 compile option `NO_AUTO_POSSESS` and the start item
`(*NO_AUTO_POSSESS)` in this slice because they are the user's way to disable
that pinned optimization; both must reproduce PCRE2 and neither is an alias for
`allowGatedFeatures`.

The proof boundary must not turn an `AutoUnsafe` case into a false optimization
theorem. Layer S models the pinned compile semantics as an explicit
option-controlled auto-possess normalization followed by matching. `AutoSafe`
cases spend the equivalence theorem; `AutoUnsafe` cases are specified by the
transformed tree PCRE2 actually executes. With either auto-possess control set,
S uses the untransformed tree. Thus R refines the auditable pinned behavior
without claiming that PCRE2's buggy table preserves its pre-optimization
language.

The analyzer sees the same atomic region an explicit possessive form would
emit. The compiler report records explicit versus automatic possessification,
matcher routing, certificate/classification, and cost/stack/memory as separate
fields. No test asserts that atomicity necessarily lowers every bound; it
asserts the applicable shape and the checker's acceptance.

The exact adjacency walk also narrows today's coarse arena-order refusal, so
the default surface does change even though it gains no wave 2 syntax. Before
the change, freeze a generated census of every pattern the coarse check
refuses. Afterward split it mechanically into derived-unsafe cases, which stay
refused ungated, and coarse-only false positives, which now compile to ordinary
wave 1 bytecode with no atomic opcode. Record both counts, every changed
compile outcome/error offset, the new program hash and PCRE2/NO_AUTO_POSSESS
answers in a before/after fixture referenced by the shipped manifest. No prose
claim may turn that refusal narrowing into “unchanged default surface.”

Done when: all possessive forms and both auto-possess controls agree with the
pinned build; all previously refused unsafe-pair fixtures now produce its
observed answers under gated PCRE2-default mode and the documented semantic
answers with auto-possess disabled; the full gated decision matrix
agrees with the diagnostic opcode dump and catches injected decision errors;
the ungated path emits no atomic opcode and preserves every derived unsafe
refusal (currently eight identity pairs); a mutation that creates a
ninth unsafe pair changes the derived set and fails the projection fixture; no
broad arena-order approximation remains; atomic proofs discharge the
possessive S/R semantic row; I is still inventoried separately and the default
gate remains closed; and the default-refusal before/after fixture accounts for
every newly compiled wave 1 pattern.

## 10. Gate 4: lookahead

Positive and negative lookahead share the control-frame machinery and differ
only in their completion action. A positive success commits the first body
thread, retains its captures, resets the subject position and continues. A
positive exhaustion fails outward. A negative body success restores the frame
and fails outward; complete body exhaustion restores the frame and continues
once. Neither form leaves an internal choice point available to later
backtracking.

Layer S states those rules directly on the priority-ordered thread list. The
proof must cover captures, not merely final match spans: `(?=(a|ab))\1` and a
suffix that fails after a successful assertion distinguish atomic first-thread
selection from an ordinary subexpression. Negative assertions prove their
post-state register file equals their input register file.

Add a lookahead region whose certificate charges the body once per incoming
flow, including the worst path required to find a success or establish
failure, and yields at most one forward continuation. The trail bound includes
the rollback of a negative or failed assertion. Empty, nested and quantified
assertions are covered; PCRE2's rule that an unlimited assertion repetition is
normalized to one above its minimum is pinned by compile and match cases.

Done when: every symbolic and alphabetic spelling agrees with PCRE2; positive
capture retention and negative rollback are proved; S totality, R refinement,
termination and applicable resource/context theorems cover both signs without
a feature-exclusion hypothesis; the feature ledger says S complete, R
complete, I incomplete, default false, `allowGatedFeatures` true.

This is one of M8's two required proof families. “Lookahead proved” in M8
means the complete S/R row just described. It does not mean artifact
refinement, and no document or tag may shorten it to that.

## 11. Gate 5: `\G`

Activate the `SCtx.startoffset` and `AssertG` cases introduced in gate 2a. The
value belongs to per-call semantic/matcher state, never to the reusable public
preallocated context. `AssertG` succeeds only when `pos == startoffset`. It is
independent of `ANCHORED`, `NOTBOL`, multiline and newline conventions.
Compilation marks a pattern anchored when every top-level alternative begins
with `\G`, matching the pinned optimization, while the semantic opcode remains
present and checked.

The wrapper tests are load-bearing. Repeated calls used for find-all pass a new
start offset, so `\G` may chain matches; an empty previous match follows the
project's existing advance rule rather than Perl's persistent `/g` state. A
single match call that bumps from its start to a later attempt must not make
`\G` true there.

`AssertG` costs one visit and no scratch. It starts on the backtracking path.
It remains Pike-ineligible throughout M8. The call's `startoffset` and the
current closure position are fixed, so `pos == startoffset` is uniform across
threads at one pc and does not invalidate the pc-keyed visited set the way a
backreference does. Admission is nevertheless a separate optimization: it
requires threading the call start through `pikeAdd`, preserving its distinction
from each thread's originating attempt in the refinement relation, and proving
the Pike resource theorem and cross-matcher agreement. Price and review that
work after M8 rather than hiding it inside this slice's 2–4-round range.
Classification follows the certificate and is not hard-coded from routing.

Done when: direct calls, anchored optimization and Go/JavaScript find-all
wrappers agree with PCRE2's per-call behavior; the assertion is constant-time;
its S/R row is complete; and its I and Pike statuses are recorded
independently, with Pike recorded as ineligible for this milestone.

## 12. Gate 6: backreferences

Backreferences land before lookbehind because the latter consumes their
fixed-group-width rule. They read mutable capture state, can consume up to the
subject length per visit, interact with lookahead captures, and add a
subject-dependent opcode price. The parser already records references until all
groups are known; extend that machinery rather than introducing a second
resolver. Resolve every section 2 spelling to an absolute capture number while
preserving the pinned decimal/octal ambiguity, signed-relative base,
forward-reference rules, whitespace handling under `EXTENDED`, name
validation and first-error order. Branch-reset groups `(?|...)` remain
unsupported; no reference numbering rule assumes them silently.

Before changing bytecode, prototype the bound composition against the existing
degree-four `base^n` polynomial representation. Price `(a+)\1*` and
`(\w+)\s+\1`, then forced-failure variants such as `^(a+)\1*b$` and a
backreference-bearing body under two nested repetitions with an impossible
suffix. Exercise both ways the representation can refuse: multiplication that
would require a degree above four, and `satAdd`/`satMul` value saturation that
sets `over`. Run the same candidates through the independent analyzer and
checker and require an explicit no-certificate result rather than a truncated
coefficient. If common intended patterns require a bound-language extension,
stop before implementing `BackRef`; that extension is a separate reviewed gate
across TIR, APIs and proofs, not part of the feature commit.

At runtime, an unset group fails. A set group names two subject offsets. Check
their order and range as compiler/run invariants, then compare directly against
the current subject position without allocating or copying a substring. Stop
at the first unequal byte. Caseful comparison is byte equality; caseless
comparison uses the pinned C-locale fold table according to the options in
force at the backreference, not those that were in force when the group was
captured. A zero-length capture succeeds without consuming and therefore
participates in the existing empty-iteration rule.

Charge the instruction visit plus one unit per byte actually compared,
including the byte that discovers a mismatch. The checker uses `n` as the
maximum captured length, so a backreference visit contributes at most
`n + 1`; composition may raise the polynomial degree or overflow the existing
representation, in which case the honest result is no certificate rather than
an understated one. The stack and trail rules remain explicit. Context memory
does not grow with capture length because the subject is borrowed and captures
are offsets.

Layer S reads the most recent capture from the register vector and compares
the subject slice. Layer R compiles the resolved number and case mode and proves
the VM loop equivalent, terminating in the remaining capture length. This
discharges gate 2a's revised comparison-fuel obligation. Reopen lookahead
theorems for references to captures created inside an assertion. A reference
inside its own repeated group uses the previous iteration exactly as PCRE2
10.47 does; it is not confused with subroutine recursion, which remains
unsupported.

Also compute a sound group-width table for gate 7. A numeric or uniquely named
reference has a fixed width only when its resolved capturing group does;
variable, cyclic, duplicate-name and option-dependent cases are unknown. Prove
the table against the S width relation before lookbehind consumes it. The
unsupported `DUPNAMES` and `MATCH_UNSET_BACKREF` options do not become implicit
assumptions: their refusal is a named premise of the compatibility surface.

The test matrix crosses numeric boundaries 1, 7, 8 and multi-digit forms;
absolute, relative and forward forms; every named spelling; a following digit;
unset, empty and previous-iteration captures; capture overwrite and rollback;
ASCII caseless changes at the reference site; nested repetitions, atomics and
both lookahead signs; start offsets and match options. Large captures test
early mismatch, full success and one-byte-short subjects while checking both
reported usage and certified cost.

Done when: every admitted spelling and interaction agrees with PCRE2; no
substring allocation exists in any backend; the byte loop is metered and
proved terminating; analyzer/checker mutation tests catch a missing `n + 1`
factor; the fixed-group-width table is proved sound; the S/R row is complete;
and I and admission statuses are exact. Backreferences remain Pike-ineligible
throughout M8.

## 13. Gate 7: bounded lookbehind

Lookbehind reuses lookahead's sign and capture rules, but its matching order is
new. Compute a branch width interval over the normalized AST at compile time.
Widths are byte counts in M8's non-UTF mode. Top-level branches keep their
source order. A fixed branch starts exactly at `pos - width`; distinct fixed
branch widths are allowed up to 65535. A variable branch is accepted only when
its maximum is finite and no greater than the pinned 255 limit, and tries
candidate starts from maximum width down to minimum so captures match PCRE2.
Every successful candidate must finish exactly at the assertion position.

The width analysis is total, saturating and independent of code emission. It
handles concatenation by addition, alternation by interval union, bounded
repetition by checked multiplication, zero-width assertions as zero, `\R` as
width 1..2, and backreferences through gate 6's fixed-group-width table. `\X`,
unlimited repetition, recursion and every other genuinely unbounded construct
produce the same PCRE2 compile error and offset as the oracle. Nesting a
lookbehind does not add its own width to its containing branch, but its
inspected prefix is still accounted in runtime cost and memory.

The look side table records the checked widths so the VM does no structural
analysis. The certificate multiplies the branch work by at most
`max - min + 1` candidate starts and includes position-reset and rollback
charges. The width is pattern-derived, not subject-derived, and all arithmetic
uses the existing checked counter operations. A context reserves no storage
proportional to the subject merely because a lookbehind has width 255.

Boundary tests name the path to each limit. `(?<=\R)b` matches the `b` in
`"a\nb"`; `(?<=\R{127})b` compiles while `(?<=\R{128})b` fails with error 200
at the 255 variable-width cap. A single `{65536}` only tests quantifier error
105, so the fixed-width boundary uses concatenation:
`(?<=a{32767}a{32768})b` reaches 65535 and compiles, while
`(?<=a{32768}a{32768})b` reaches 65536 and fails with lookbehind error 187.
The matrix also covers too little subject, distinct fixed branch lengths,
maximum-first capture preference, nested lookaround, start offsets, every
newline convention, `\X`, empty branches, zero-width bodies, and both
`(a)(?<=\1)` and variable-width `(a+)(?<=\1)`, the latter failing with error
125 at offset 4.

Gate 7 also reopens gate 6 in the other direction: a positive lookbehind may
create a capture that a later backreference consumes. Prove in S and R that the
chosen maximum-first successful candidate retains those registers, that a
negative or failed candidate restores them, and that later outer backtracking
restores the pre-lookbehind values. Oracle and bound cases include
`(?<=(a))\1` on `"aa"`, a variable-width captured body whose selected width
changes the later reference, and a negative lookbehind followed by a reference
to its unset capture. This interaction is part of the final backreference row,
not merely a lookbehind test.

Done when: both signs and all six spellings agree with PCRE2, the width
analyzer and its errors are held by the named boundary tests, analyzer and
checker independently price every candidate, the fixed-backreference cases
close without a feature hole, lookbehind-created captures and later
backreferences close symmetrically in S/R and the feature inventory, the S/R
row is complete, and the exact I status is in the feature ledger. Lookbehind
stays gated if its complete I chain is absent.

## 14. What “S/R coverage” means in M8

M7R is scheduled after M8. Therefore DESIGN.md's explicit atomic-group and
lookahead proof requirement means layers S and R, not a completed layer-I
refinement. M8's vertical-slice rule applies that same S/R standard to every
wave 2 family. This deliberately strengthens DESIGN.md's literal minimum of
atomic groups and lookahead: the full PLAN-M8 target requires complete S/R rows
for atomic groups, possessive quantifiers, both lookaround directions, `\G`
and backreferences. Atomic groups and lookahead remain the earlier roadmap's
named minimum and must never be abbreviated to “proved.” A complete S/R row
is:

| Obligation                 | Required statement                                                                                                            |
| -------------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| S syntax and meaning       | Extended AST and priority/capture semantics, with no constructor silently mapped to an old one.                               |
| S totality                 | Sufficient fuel, stability and total `Matches` over the extended constructors.                                                |
| R compiler and VM          | Extended bytecode, compiler, execution and context definitions.                                                               |
| Semantic refinement        | Backtracking execution returns exactly `Matches` for every well-formed pattern in the feature family under sufficient limits. |
| Termination                | Every plain and context run terminates; bounded loops have explicit measures/fuel.                                            |
| Resource soundness         | Accepted certificates bound cost, backtrack stack and scratch memory, including refusal attempts and replay.                  |
| Context sufficiency        | Certificate-sized contexts succeed under sufficient cost/stack and do not grow during matching.                               |
| Bad input and monotonicity | Existing public theorems extend without a feature carve-out.                                                                  |

Pike refinement and cross-matcher agreement are not required for stateful wave
2 features because those programs are deliberately ineligible. They are
required before any new opcode is declared Pike-eligible.

Layer I has its own columns: decoder/printer support, local function
simulations, coverage-ledger count, composed compiler theorem, composed matcher
theorem and final artifact theorem. M8 records whatever actually lands by
theorem name. It never promotes a feature because the artifact decoded, a
`#guard` ran, a corpus replay passed, or one local simulation exists. Atomic
groups and lookahead remain behind `allowGatedFeatures` at M8 close unless all I
columns, including composition, are complete. M7R begins with the symbolic
executor PLAN-M7.md section 10 names and owns that completion.

No backtracking S/R theorem is weakened to close a row. In particular, adding
a `CoveredWithoutLookaround` premise and then calling lookahead proved is not a
completion. Gate 2a's `AstEnabled` parameter is discharged with the feature bit
on before that feature's row can close. The separate `PikeSafe` premise is
different: it states the domain of an optional matcher whose seen set indexes
only pc, and the compiler theorem proves all stateful programs are routed away
from it. No stateful feature is claimed as a Pike result. Compiler-output
invariants are derived from `Ref.compile`; the checker remains responsible only
for the arbitrary programs its documented rules admit.

## 15. Differential, conformance and negative testing

Every slice adds three kinds of evidence, because none substitutes for the
others.

### Hand-written oracle corpus

One case per semantic distinction and boundary, with a sentence saying what it
pins. Compile-only cases retain capture count, names, code and offset. Match
cases retain the entire ovector. Mixed-feature cases are added when the later
feature lands, so an earlier family is not declared permanently covered before
its new interactions exist.

### Exhaustive small domains

For a fixed matrix of feature-bearing patterns, enumerate subjects through
length four over an alphabet chosen for that feature: matching/nonmatching
bytes, newline bytes, case pairs and empty captures. Cross every compile and
match option that can change that construct, starts from zero through one past
the subject, and LF/CRLF at minimum. Options proved irrelevant are held at the
baseline value plus one invariance case rather than multiplied into every row.
Invalid syntax is exhaustive over short prefixes around `(?`, `(*`, `\g`,
`\k`, quantifier suffixes and closing delimiters and is compile-only.

The generator has a count-only mode. Before a slice commits its matrix it
writes the exact product—patterns × subjects × relevant compile-option tuples
× relevant match-option tuples × starts × newline/BSR tuples × engines—plus a
per-dimension breakdown into the slice manifest. Gate 0 measures oracle and CI
throughput and sets the per-PR comparison cap before these matrices exist. A
matrix above that cap must be partitioned into a committed PR shard and a
nightly exhaustive shard at review; the generator refuses to run an unreviewed
larger product. The engine may skip only outcomes the oracle policy names;
`InternalError` is always a failure.

### Generated campaign

Extend the one deterministic sweep grammar rather than adding a second fuzzer.
Generation is feature-aware and reports coverage for each syntax spelling,
sign, direction, nesting relation, capture dependency, matcher route,
certificate result and limit edge. At least one third of accepted generated
patterns in the M8 closeout campaign contain two or more wave 2 features, and
every feature has cases nested inside and around repetition and alternation.

Per-slice CI keeps a committed shard and a generated smoke campaign. M8 closes
on a pinned campaign of at least 10,000 feature-bearing structured patterns
plus 2,500 hostile-syntax patterns, at least eight generated subjects per
matchable pattern, zero oracle disagreements, zero backend disagreements, zero
bound violations and zero cross-matcher disagreements on the still-eligible
wave 1 intersection. The exact seed, population shape, command, pcre2 build ID,
artifact/manifest hashes, comparison counts, declined reasons and coverage
table are committed. Failures minimize and promote through the existing
semantic-versus-invariant split.

For every distinct observed positive cost, stack and memory usage, edge tests
run at the observation and one below, subject to the existing deterministic
deduplication cap. Context creation is edged at its memory reservation. New
certificate rules get direct adversarial claims: wrong region kind, mismatched
start/end, wrong look width, omitted control frames, understated byte compare,
wrong ambiguity and a certificate from another program.

## 16. Performance and memory gates

“Excellent performance” is not a claim made from one benchmark. M8 carries
structural gates that are deterministic and benchmark evidence that is
published.

The structural gates are mandatory:

* no host recursion in parser, compiler, matchers, analyzer or generated code;
* atomic exit and committed assertion exit discard internal choices with one
  vector truncate, not a loop over discarded entries;
* assertion entry copies no register file, ovector, subject or stack—only the
  scalar frame is pushed;
* negative and failed assertion restoration uses the existing undo trail and
  charges every restored register;
* lookbehind widths are computed once at compile time; runtime reads the side
  table and tries no more than the certified candidate count;
* backreferences compare the borrowed subject in place, stop at first
  mismatch, allocate nothing, and charge every examined byte;
* the wave 1 Pike path allocates no new nonzero-capacity scratch structure and
  retains its selected matcher and certificate unless an explicit
  auto-possess compatibility fixture says otherwise;
* a context-backed match for every finite-certificate wave 2 sample reports no
  growth, zero Go heap allocations and zero JavaScript backing-store
  constructions under the existing instrumentation;
* analyzer and checker arithmetic is saturating-with-refusal exactly as in
  wave 1; no bound is sampled at finite lengths to justify a formula.

Before gate 2a changes the artifact, add a reproducible benchmark harness and
record thirty runs of the M7 artifact after warmup on fixed hardware metadata.
It measures compile time, match time, artifact/code size, context creation,
resident scratch, and allocations for representative wave 1 patterns. Each
slice adds successful, failing and adversarial PCRE2/Go/JavaScript cases and
reports median and dispersion against the frozen baseline and the pinned
non-JIT PCRE2. Wall-clock ratios are evidence, not proof and not silently
chosen after the implementation. After baseline variance is known, the plan
records review thresholds before the rest of gate 2a lands; crossing one
requires an explained design review, never a larger threshold in the same
commit.

The algorithmic expectations are fixed now:

* `\G` is constant work per visit;
* an atomic or possessive boundary adds constant entry/exit work and can reduce
  downstream ambiguity to one;
* lookahead costs at most the certified body search per incoming flow;
* variable lookbehind adds at most its pattern-derived candidate width factor;
* a backreference visit is linear in the referenced capture length and uses
  constant additional memory;
* nested constructs compose through BOUNDS.md, so exponential or
  unrepresentable cases return a conservative exponential form or no
  certificate while still obeying hard runtime limits.

M8's closeout publishes the benchmark inputs, raw results, summaries and
artifact identities. It does not call a conservative certificate “measured
runtime”, does not compare the engine's cost units with PCRE2 instructions, and
does not infer complexity class from matcher routing.

## 17. Documentation and API migration

The compatibility table, generated API docs and release notes use the feature
ledger as their input. README examples show default refusal and explicit
`allowGatedFeatures` use without recommending the latter as safe by default.
They also show a semantics-preserving auto-possess case whose default and gated
compiles have different analysis accessors; the conformance fixture records
the internal program hashes. Callers must not mistake the flag for a
result-only admission switch.
`UnsupportedFeature` continues to mean “valid PCRE2 construct outside this
call's admitted engine surface”; incomplete proof status is exposed separately
in metadata and never disguised as a PCRE syntax error.

DESIGN.md sections 6 and 9 are updated with the
`allowGatedFeatures` name, the terminology of section 3 and the exact M8 proof
boundary of section 14 before any public API is generated. THEOREMS.md gains a
wave 2 inventory beside, not over, the frozen wave 1 one. BOUNDS.md receives
each rule before its code. TIR-SPEC.md receives any new struct, enum variant,
size, trap or evaluation order before a generated artifact uses it.
`api-faq.md` records PCRE2 behaviors that contradicted an implementation
assumption. MISTAKES.md remains for actual mistakes, not routine design
decisions.

The full plan intentionally strengthens DESIGN.md's older M8 done-criterion.
If gates 6 and 7 overrun and the project chooses the older atomic/lookahead
minimum, that is a named descope, not an interpretation of this document: edit
DESIGN.md and this completion audit together, cut a separately named milestone
for the deferred backreference/lookbehind work, and rerun the manifest surface
audit before claiming M8 complete. No status row changes merely because the
older sentence can be read more weakly.

No old tag moves. Every shipped capsule gets an annotated milestone or slice
tag only after its manifest exists and `make check` and `make verify` pass on
the committed tree. A remote or off-machine bundle is operational
preservation, not evidence for a semantic gate.

## 18. Delivery size, midpoint and replanning rules

M8 is M6-scale work, and may be larger; DESIGN.md's older relative ranking is
not a schedule. The structural census alone reaches nineteen exhaustive `Ast`
definitions, fourteen exhaustive `Op` definitions, over one hundred other case
sites, three shadow inductives and three proof files above 7,000 lines. The
auto-possess diagnostic, dual-manifest verifier, benchmark harness and final
campaign are additional scope that the older M8 paragraph did not price.

Use a **reviewed round** as the planning unit: one bounded deliverable ending
in a clean tree, its relevant full verification, and an adversarial review.
These are initial ranges, not promises:

| Gate                           | Initial range | Dominant uncertainty                                     |
| ------------------------------ | ------------- | -------------------------------------------------------- |
| 0, blob manifests and verifier | 3–5 rounds    | hermetic materialization and two independent Lean builds |
| 1, admission ledger/API        | 2–3 rounds    | strict source extraction and parser/API partitions       |
| 2a, structural wave            | 6–10 rounds   | premise preflight, exhaustive Lean repair and measures   |
| 2b, atomic groups              | 4–6 rounds    | ordered captures, frame restoration and bounds           |
| 3, possessive/auto-possess     | 5–8 rounds    | diagnostic spike and representation correspondence       |
| 4, lookahead                   | 6–10 rounds   | nested search, capture effects and resource composition  |
| 5, `\G`                        | 2–4 rounds    | S-context churn already absorbed by gate 2a              |
| 6, backreferences              | 7–12 rounds   | bound prototype, byte charging and capture dependence    |
| 7, lookbehind                  | 7–12 rounds   | width rules, candidate order and composed bounds         |
| closeout                       | 3–5 rounds    | campaign, benchmark and manifest audit                   |

The whole range sums to 45–75 reviewed rounds. The gates 0–3 midpoint sums to
20–32, including both halves of gate 2. Those totals are the scale argument for
cutting the midpoint rather than asking readers to add the rows themselves.

Re-estimate after gates 0 and 2a from actual code/proof lines, compile
iterations and review findings. Do not extrapolate from constructor count
alone. A range overrun pauses the next gate and produces a written variance
report; it does not silently expand the milestone.

Gates 0 through 3, with both 2a and 2b included, are the shippable midpoint.
They add no wave 2 feature to the default surface, provide atomic and
possessive behavior under `allowGatedFeatures`, and reproduce PCRE2's
auto-possess decisions. Gate 3 nevertheless expands the default wave 1 pattern
set by replacing the coarse auto-possess refusal with the exact derived-unsafe
set; section 9's before/after fixture makes that narrowing explicit. Cut a
midpoint manifest/tag and rerun the completion audit restricted to those rows
before starting lookahead.

After lookahead, re-estimate gates 6 and 7 together against their initial
14–24-round range. An overrun invokes the explicit scope decision in section
17 before either family is partially defaulted or the completion audit is
weakened. The midpoint remains shippable independently of that decision.

Gate 0 is allowed five reviewed rounds. If it has not independently rebuilt
both manifests by then, stop M8 and close a separately named M8A
infrastructure milestone. No `gen/engine.tir.json` move and no wave 2 parser or
AST change may land while it is open. Replan the materializer or dependency
closure; do not weaken byte identity, offline verification or the five tamper
tests to recover the schedule.

## 19. M8 completion audit

M8 is complete only when all of the following are true in one clean committed
checkout:

1. Gates 0, 1 and 2a are closed: two versioned manifests materialize and build
   independently from immutable blobs, every required tamper test fails, the
   admission ledger and compile-capability masks control all three APIs, the
   source-derived surface fixture accounts for all 51 `(*...)` table rows,
   all three public option masks, every shim projection and the explicit `(*)`
   fallback, and the structural wave preserves the old wave 1 corollaries.
2. Atomic groups, possessive quantifiers, both lookahead signs, both bounded
   lookbehind signs, `\G` and every backreference spelling in section 2 are
   implemented end to end under `allowGatedFeatures`.
3. The admitted surface agrees with the pinned PCRE2 build in compile outcome,
   error code/offset, capture metadata, match/no-match and full ovector over
   the hand-written, exhaustive and generated evidence of section 15.
4. Every wave 2 family has a complete S/R row as section 14 defines it;
   in particular this discharges DESIGN.md's named atomic-group and
   positive/negative-lookahead proof requirement. Every I gap is named by
   feature, theorem and artifact in the machine inventory.
5. No wave 2 feature with an incomplete I chain is default-enabled. The wave 1
   default surface remains available under its explicitly named M7 foundation
   fallback, and every default compile newly admitted by the narrowed
   auto-possess refusal appears in section 9's before/after fixture.
6. BOUNDS.md, the analyzer and the independent checker cover every new opcode,
   region, control frame, look width, replay and backreference byte. Mutation,
   bound-edge and context-reservation tests pass.
7. Every stateful wave 2 opcode is Pike-ineligible, and `AssertG` remains
   ineligible under the explicit post-M8 deferral. Any later exception has its
   own Pike refinement, bound and agreement proof rather than a predicate edit.
8. The final 12,500-pattern minimum campaign reports zero findings with its
   manifest, comparison counts, decline reasons and coverage committed.
9. The structural performance gates and context no-allocation tests pass;
   the benchmark report and raw data are committed; wave 1 regressions are
   explained and accepted at a review boundary rather than hidden in noise.
10. `make check` and the dual-manifest `make verify` pass end to end, the Lean
    build contains no `sorry` or `partial`, and theorem axiom reports name no
    axiom beyond the three already recorded unless the project makes and
    documents a new foundational decision.
11. `wave1-frozen`, `m7-foundation-20260806` and
    `m7-foundation-20260807` still point to the same objects and annotations
    they did before M8.
12. Release documentation states the exact default and gated surfaces, the
    S/R/I inventory, the tested parser/backend links and the pinned PCRE2
    identity without using “fully proved” for either active artifact. It names
    script runs, the explicit unsupported compile-option, match-option and
    convention complements, and `PCRE2_NEWLINE_NUL` rather than asking an
    inclusion list to imply their exclusion.

The completion audit reads every row back from the active manifests and the
feature ledger; it does not reconstruct the result from prose. If a condition
is not mechanically established, it is open. M7R then starts where
PLAN-M7.md section 10 says it does—with the symbolic executor, followed by the
dependency-ordered simulation campaign, L-4/L-5 and the composed artifact
theorem. M8 does not spend hand-written Layer-I lemmas merely to make its own
inventory look busier.

## 20. Principal risks and their stop rules

**Capture semantics drift.** Positive assertions and atomic commits can look
right at group 0 while inner captures are wrong. Stop the slice on any ovector
disagreement; do not proceed from match-span-only evidence.

**A hidden copy makes assertions expensive.** Stop if an implementation
snapshots captures or scans discarded choices at construct exit. Redesign
around scalar watermarks before adding the next feature.

**The checker learns the analyzer's answer rather than checking it.** Stop if
new composition code is shared between the two beyond the existing arithmetic
and opcode-cost vocabulary. Add adversarial certificates before proceeding.

**Lookbehind width becomes a second parser.** Width is over the normalized AST,
not pattern text or bytecode. Stop if runtime or the certificate checker has to
rediscover source structure from instructions.

**Backreference bounds outrun the polynomial representation.** Refuse the
certificate honestly. Do not add a higher degree, a sampled inequality or an
unbounded arbitrary-precision value in the same feature commit; changing the
bound language is a separate reviewed design decision across TIR, APIs and
proofs.

**Compatibility expands invisibly.** A new spelling or option is either in
section 2 and the feature ledger, with oracle/error/resource/proof coverage, or
it remains unsupported. No parser convenience silently grows the claim. For
every closed pinned table or public mask imported to define a compatibility
universe, alias relation or semantic decision, derive the universe from the
pinned source into a versioned extraction fixture with a cardinality and row-
shape guard. The project hand-maintains only the policy partition. Stop if the
admitted, gated and unsupported sets do not form an exact disjoint cover of
that source universe, if a shim or backend projection has an unexplained
complement, or if a parser route such as `(*)` belongs to no table and has no
explicit fallback fixture. A list of supported entries is not evidence that
the omitted entries were considered.

**The two artifacts become two stories told by one checkout.** Stop if either
manifest needs uncommitted bytes, Git history, a network fetch or a logical
file supplied only by the other manifest to verify. Sharing a named
content-addressed blob is allowed; depending on the other manifest is not.
Independence is the reason gate 0 exists.
