# M7: Layer I, the refinement to the frozen artifact

DESIGN.md section 6 gives Layer I its shape: TIR syntax as inductive types
with a definitional interpreter, a Lean-side decoder that reads the canonical
`gen/engine.tir.json` bytes directly, a round-trip self-check, refinement
theorems against layer R, and a `make verify` gate that fails when anyone
edits the engine without re-proving. Section 10 calls it the schedule risk
and the largest milestone. This plan is where it gets sequenced, and where
its first decision gets made rather than inherited.

The target is the artifact the `wave1-frozen` tag pins, sha256 `d60df8a5…`.
It does not move during M7. An engine change after the freeze re-opens
proofs deliberately and visibly: the pinned hash moves only together with
the proof increment that covers the change, which after gate 3 below is
enforced by the build rather than by discipline.

## 1. The endpoint, stated first

When M7 closes, this sentence is provable and `make verify` checks it:

    The engine artifact the backends consume, read through the audited
    Lean decoder, refines layer R: from related compile arguments and
    parser work area for any well-formed wave 1 AST, the decoded
    compilation pipeline agrees with `R.compileFull`, and the decoded
    match functions agree with `R.run`, so the universal layer S and R
    theorems — semantics, termination, bounds, cross-matcher agreement —
    compose through to the artifact itself.

Universal is doing work in that sentence, and so is "from related compile
arguments and parser work area". R-10 is a corpus replay, not a theorem to transfer, and it stays
one; nothing here relates the specification to the pinned pcre2 — that
correspondence rests on the trusted-spec caveat and the differential
testing THEOREMS.md section 4 states, exactly as before; and the
artifact's `compile` entry parses before it generates, so the statement
starts where the parse ends — its corollary about the exported entry is
conditional on the parser relation gate 5 states, which is the tested
link until M10. The trusted base grows by exactly one audited
item, the decoder's constructor-per-constructor schema mapping, and
DESIGN.md section 6 already states why the round-trip self-check pins
losslessness without being the semantic argument. The Go and JS printers
stay tested links, as THEOREMS.md section 4 says they remain.

## 2. The first decision: where the lowering proof boundary sits

THEOREMS.md section 4 leaves the quantifier lowering inside the tested
pattern-text-to-AST link, and section 6 prices moving it inside `R.compile`.
That deferral was correct for landing the post-M6 change; it is not a
foundation M7 can build on, and the reason is compositional rather than
aesthetic.

Layer I's compiler theorem wants to say: the decoded TIR compile function
agrees with `R.compile` on every AST. But the TIR compile function *lowers*
— DESIGN.md section 4.3 is implemented inside the code generator — and
today `R.compile` does not. For a counted repetition the two functions
disagree on purpose, and no honest simulation lemma connects them. The
statements would only compose over trees the lowering fixes, which is a
carve-out in the milestone's central theorem.

Two routes exist and both were considered:

1. Prove the lowering first, as the M7 prelude, and integrate it into
   `R.compile`. Then the refinement theorem quantifies over original ASTs,
   the tested link narrows back to the parser alone, and THEOREMS.md
   section 4 loses a paragraph. THEOREMS.md section 6 already inventories
   the work and found none of it a research question.

2. Keep the lowering tested and state the compiler theorem against
   `R.compile (lower a)`. Weaker endpoint: the refinement would be of the
   lowered tree, not the written pattern, and every coverage sentence
   would carry the caveat forever. It must not be described as
   original-AST refinement, because it is not one.

Route 1 is the decision. It front-loads the mechanical-but-real proof work
where it belongs — before the deep embedding multiplies every statement's
size — and it is the only route whose endpoint matches the objective's
sentence. Route 2 stays available as the documented fallback if the
preference-order proof stalls; falling back means moving the carve-out
into THEOREMS.md section 4 explicitly, not rounding it up.

## 3. The prelude: proving the lowering (gate 0)

The inventory is THEOREMS.md section 6's list, given labels here so the
gate has a ledger. All of it is over layer S and R, none of it touches the
deep embedding, and `lowered.py` is the transcription source the same way
`compiler.py` was for `Ref/Compile.lean`.

    +------+----------------------------------------------------------------+
    | L-1  | `Spec.lower`, the rewrite as a function on `Ast`, mirroring    |
    |      | `lowered.py`'s `rewrite`: bounded reps become copies ending in |
    |      | nested optionals, unbounded ones copies ending in a pure star, |
    |      | the already-star-form spellings kept. With it `Spec.lowerFit`, |
    |      | the dry run and decision, mirroring `size` and `decide`.       |
    +------+----------------------------------------------------------------+
    | L-2  | the preference-order theorem, stated where the order lives:    |
    |      | `search` and `searchRep` on the lowered tree return the same   |
    |      | ordered thread list — positions and capture registers alike —  |
    |      | under the sufficient-fuel relation, the fuel side an           |
    |      | implication rather than an equation since the lowered form     |
    |      | spends none on a bounded quantifier. `Matches` exposes only    |
    |      | the final `MatchAnswer`, `scan` having already picked the      |
    |      | first surviving thread, so the equality everyone quotes,       |
    |      |                                                                |
    |      |   Matches { p with root := lower p.root } s start mo           |
    |      |     = Matches p s start mo                                     |
    |      |                                                                |
    |      | for every pattern, subject, start and match options, is the    |
    |      | lift of that stronger statement through the L-3 preservation   |
    |      | results, not the theorem that carries the claim.               |
    +------+----------------------------------------------------------------+
    | L-2a | the bounded case, `x{m,n}` with n finite: at count k the       |
    |      | repetition's remaining behaviour is the optional chain at      |
    |      | n - k, by induction downward on n - k, both greediness         |
    |      | orientations and the registers carried through every splice.   |
    +------+----------------------------------------------------------------+
    | L-2b | the unbounded case, `x{m,}`: below the minimum a copy, and at  |
    |      | the minimum the pure star, using that past the minimum an      |
    |      | unbounded repetition's count stops mattering — the             |
    |      | empty-match rule reads `cnt + 1 ≥ lo` and nothing else does.   |
    |      | Its own count-irrelevance lemma, proved before the splice.     |
    +------+----------------------------------------------------------------+
    | L-3  | Preservation, structural and small: `Wf`, `CapsBelow`,         |
    |      | `Covered`, `maxGroup`, and `crWalk` for the bumpalong bit.     |
    +------+----------------------------------------------------------------+
    | L-4  | The counting theorem of `ReWfCompile.lean` restated over the   |
    |      | dry-run sizes instead of four cells per arena node, which the  |
    |      | lowering breaks by design. Roughly the size of what it         |
    |      | replaces.                                                      |
    +------+----------------------------------------------------------------+
    | L-5  | Integration: `R.compile` lowers when the decision says fit,    |
    |      | exactly as the engine does. `RepCompile.lean` and the two      |
    |      | refinement files follow through mechanically. The bridge then  |
    |      | exports the *original* tree and `lake exe corpuscheck` holds   |
    |      | the now-lowering `R.compile` to the engine's bytecode, which   |
    |      | is the moment the tested link narrows to the parser.           |
    +------+----------------------------------------------------------------+

Done when: `lake build` proves L-2 through L-4 with no `sorry` and no new
axiom, the corpus replay passes against the original exported trees with
any change to its inventory recorded, and THEOREMS.md section 4 no longer
names the lowering as a tested transformation. The artifact hash does not move — the
engine is untouched; only the Lean account of it deepens.

L-2 is the semantic checkpoint of the whole route, and the reason it is
split in two above is that the two quantifier families fail differently.
The bounded one is a finite splice whose risk is bookkeeping — register
writes, the order the optionals nest in, the greediness flip. The
unbounded one turns on a semantic fact, that a count past the minimum
changes nothing the search can observe, and that fact has to be a lemma
before the splice can use it. Once both close, the route is de-risked and
the rest of the prelude is structural. If either stalls on preference
order, the fallback of section 2 applies and is written down before any
gate 4 work begins, not after.

## 4. The vertical gates

Each gate lands proved and checked, so a stall leaves a coherent smaller
thing rather than a half of a big one. The ordering exists to surface the
architecture risk (gate 4) before the volume work (gate 5).

Gate 1, the deep embedding. TIR syntax as inductive types under
`Pcrevera/Tir/`, covering exactly what the M2 schema admits and the wave 1
artifact uses, plus the definitional interpreter: environment, store, fuel.

One contract has to be settled here rather than discovered in gate 5,
because every simulation lemma is stated in it. Two are available. TIR
carries a variant on every `while` (TIR-SPEC.md section 8.6), so
evaluation could be well-founded, each loop terminating by its own
variant. But a variant is an expression over the mutable store, so its
descent is not a fact about the syntax: it needs the loop's invariant,
which would make the *definition* of the interpreter wait on 83 hand
proofs, and one unproved variant would leave the whole artifact
uninterpretable. The other is step indexing, which is how layer S already
earns its totality, and it is the choice here: the interpreter takes fuel,
returns `Option`, and is total by construction.

What keeps step indexing from leaking fuel arithmetic into every lemma is
one relation, defined once and used everywhere after:

    Runs prog f σ args σ' r  :=  ∃ n, evalCall n prog f σ args = some (σ', r)

with two theorems making it behave like the evaluation everyone wants.
Stability: more fuel answers the same, `n ≤ m → evalCall n … = some x →
evalCall m … = some x`. Determinism, which follows from it: `Runs` relates
each start state to at most one outcome. Gate 5's lemmas are then all of
the form `Runs prog "f" σ args σ' r → r = ⟦R.f …⟧`, one judgment, no fuel
bound quoted in a statement, and a caller's lemma composes with a callee's
by transitivity rather than by adding budgets. The variants stay what they
are in the Python interpreter: a run-time check and a proof aid, not the
termination argument.

Done when: the interpreter is total by construction, stability and
determinism are proved, and hand-built toy programs (the bounded-Fibonacci
example of M2, an early-exit loop, a saturating counter) evaluate to their
known answers under `#eval` and `decide`-checked lemmas.

Gate 2, the decoder and printer. A Lean JSON decoder for the artifact's
schema and a canonical printer, written constructor by constructor for
auditability against the M2 spec document, since the mapping is a
trusted-base item next to the layer S spec. The round trip is stated as a
theorem over the type, not over one file:

    decode (print p) = some p          for every well-formed `p : Program`

which is the direction that says the decoder loses nothing the printer
knows. Its converse holds only on canonical bytes and is gate 3's job.
Done when: that equation is proved by structural induction (or
`native_decide`-checked where a table makes induction pointless), and both
directions have negative tests for the malformed cases the validator
rejects.

Gate 3, the artifact, decoded and pinned. Where gate 2 quantifies over
programs, gate 3 quantifies over nothing: it is one closed equation about
the frozen bytes,

    decode artifactBytes = some P  ∧  print P = artifactBytes

so the file is reproduced byte for byte and not merely parsed, and
`sha256 artifactBytes = d60df8a5…` is pinned in Lean source beside it. A
regenerated artifact then fails the build until the pin moves with a proof
increment. Done when: `lake build` fails on a one-byte edit to the
artifact, and the freeze test learns the Lean pin as one more copy of the
recorded hash to read back — a copy check, like the two rows read out of
the pcre2 pin, not a new row in the table the tag is asked for, since the
tag predates every M7 file and must stay checkable.

Gate 4, one function, end to end. The target is `region_kids`, against
`R.regionKids` (Ref/Poly.lean:237). It is the smallest function in the
artifact that exercises the whole store model rather than a corner of it:
two loops — one counting up under `total - i`, one counting down under `i`
— a frozen vec of structs read through a field, two inout vecs, pushes
that grow a sequence, and indexed writes whose aliasing is the thing the
linearity discipline exists to control. A
pure table lookup like `class_has` would prove the expression evaluator
and nothing else, and would tell us nothing about the cost of a round trip
through the store — which is the number this gate exists to measure. Done
when: the lemma is proved in the gate 1 judgment and the pattern it sets
is written into this plan as the template the next gate follows. If gate 4
is disproportionately painful, that is the earliest possible warning
DESIGN.md section 10 asks for, and the fallback conversation happens here.

Gate 5, the volume: compiler, backtracking VM, Pike VM, contexts,
analyzer checker, accessors. Per-function simulation lemmas in the gate 4
shape, in dependency order — helpers, then compile, then each VM, then the
context machinery and the accessors over them. DESIGN.md calls this
tedious but mechanical because the TIR engine and layer R were written
structurally parallel; the automation built in gate 4 is what keeps it
mechanical in practice.

It is also by far the largest thing in M7, and "every function" is not a
condition anyone can check by reading. The artifact holds 122 functions,
roughly 4,540 statements and 83 loops. So gate 5 opens with a ledger, not
with a lemma: a generated, checked coverage manifest that walks the call
graph from the exported entries, and maps every function it reaches after
the parse to either the name of its simulation theorem or an explicit,
reasoned exclusion — the parser-exclusive part of the graph until M10, and
nothing else without a sentence saying why. Exclusive is the word that
matters: `newline_at` and `ct` are the matcher's as much as the parser's,
so they stay owed a lemma and the manifest records that it knows. The manifest is regenerated from the
artifact and compared, so a new callee cannot appear without failing the
build, and completion becomes arithmetic: every reachable name accounted
for. Done when: the ledger is complete in that mechanical sense, and
`lake build` proves every theorem it names — the parser stays outside, as
section 5 says, until M10.

The compile side needs one statement of where the parser sits, because
the exported `compile` is not `R.compile` applied to a tree: it takes
pattern bytes and options, parses into a `Work`, then generates,
finalizes, decides Pike eligibility and installs certificates, while
`R.compile` takes a `Pat` and `R.compileFull` carries the pipeline from
there. So the simulation is stated across a relation
`WorkRel w popts nltype bsr p`, parameterized over the entry's own
arguments because finalization reads the options, the newline convention
and the \R convention from them rather than from the work area — `Work`
holds `opts`, `nltype` and the CR/LF record, and no BSR field at all.
The relation says, together: the arena holds what `p.root` says, and the
arguments what `p.opts`, `p.nltype` and `p.bsrtype` say. The options half
of that needs one sentence of care, because `popts` is a raw bitmask and
`p.opts` is two booleans. Most of the mask is not a fact layer R models at
all — case folding, multiline, dotall, extended and ungreedy are resolved
into the tree during the parse, and `Re` has no field for them; the entry
copies the mask into `Out.re.opts` verbatim and nothing downstream reads
those bits. The two `Re` does model, `anchored` and `endanchored`, are
exactly the two an inline option group cannot set (`spec.INLINE_OPTIONS`
admits only `i`, `m`, `s`, `x` and `U`), which is why the entry may read
them from its own argument while the parse mutates `w.opts` underneath,
and why the relation can equate them. The simulation
splits in three: code generation from any related work area, against
`R.compile p`, with the `endanchored` flag `generate` is handed related
to `p.opts.endanchored`; finalization, eligibility, analysis and
certificate installation, against `R.compileFull p`; and the
exported-`compile` corollary, conditional on `parse` producing a related
work area from the pattern bytes. That condition is exactly the parser
link M10 discharges. The relation carries everything compilation reads
out of the parse, so what stays on the tested side with the condition is
only what layer R never models: the name table and the parser's error
codes and offsets. The layer I section of THEOREMS.md names them when it
lands.

Gate 6, the composed theorem. The public refinement statement of section 1,
composed from the gate 5 lemmas and stated over original ASTs, which the
gate 0 prelude is what makes possible. THEOREMS.md gains its layer I
section with the same per-theorem inventory discipline as layers S and R.
The inventory the gates build toward, so it exists before the entries do —
I-5 through I-9 name families rather than single theorems, and it is the
gate 5 ledger, not this table, that fixes who belongs to each:

    +------+----------------------------------------------------------------+
    | I-1  | the deep TIR syntax and the definitional interpreter,   gate 1 |
    |      | total by construction, with `Runs` stable under fuel and       |
    |      | deterministic (definitions plus two lemmas, like S-1 and S-5)  |
    | I-2  | `decode (print p) = some p` for every well-formed       gate 2 |
    |      | program, with negative tests for what the validator rejects    |
    | I-3  | the frozen bytes decode and print back to themselves,   gate 3 |
    |      | and their sha256 is pinned in Lean source                      |
    | I-4  | `region_kids` simulates `R.regionKids`, the template    gate 4 |
    | I-5  | compile simulation, split where the parser sits: code   gate 5 |
    |      | generation from a related work area against `R.compile`,       |
    |      | finalization through certificate installation against          |
    |      | `R.compileFull` over related compile arguments, and the        |
    |      | exported-`compile` corollary, conditional on the parser        |
    |      | relation                                                       |
    | I-6  | backtracking VM simulation against `R.run`              gate 5 |
    | I-7  | Pike VM simulation against `R.run`                      gate 5 |
    | I-8  | context machinery and accessor simulation               gate 5 |
    | I-9  | certificate checker simulation, so layer A's soundness  gate 5 |
    |      | covers the checker the artifact actually ships                 |
    | I-10 | the composed refinement of section 1                    gate 6 |
    +------+----------------------------------------------------------------+

Gate 7, the `make verify` gate. One target that regenerates the artifact,
recomputes its hash against the pin, runs `lake build` (which decodes,
round-trips, and proves), and fails on any mismatch: regeneration drift,
hash drift, decode failure, round-trip failure, broken proof. Done when:
`make verify` passes in the completed M7 checkout against the artifact
`wave1-frozen` pins — the tag stays on the freeze commit, so the tagged
state cannot be asked to contain the gate that checks it — and each of
those five failure modes has been induced once and observed to fail. From then on the
DESIGN.md rule — the hash moves only with its proof increment — is a
property of the build.

## 5. What M7 does not do

No engine changes, no new features, no wave 2 syntax: the artifact is
frozen and M8 owns what comes after. No parser theorem — the
pattern-text-to-AST step stays a tested link until M10, and after the
prelude that link is the parser alone. No printer proofs: Go and JS remain
tested links per DESIGN.md section 7. And no silent weakening: if any gate
falls back, the weaker statement is written into THEOREMS.md in the same
motion.

## 6. Where this stands

The plan above is the whole milestone. This section is the ledger of what
has actually landed, kept here rather than in a commit message so that the
next person reads the state and the intent in one place.

    +--------+--------------------------------------------------------------+
    | gate 0 | L-1, L-2 and L-3 are proved and in the build.                |
    |        | `Spec.lower`, `Nullable` and `LowerSafe` transcribe          |
    |        | `lowered.py`; `lower_searchEq` is the ordered-thread         |
    |        | statement and `Matches_lower` its public lift; `maxGroup`,   |
    |        | `crWalk`, `WfAst` and `CapsBelow` all survive the rewrite,   |
    |        | gathered at the pattern as `wf_lowered`. No `sorry`, no      |
    |        | axiom beyond Lean's three, and the corpus replay is          |
    |        | unchanged at 331 cases and 0 disagreements.                  |
    |        | Outstanding: L-4, the counting theorem over the dry-run      |
    |        | sizes; and L-5, which moves the lowering inside `R.compile`  |
    |        | and re-proves what follows it.                               |
    +--------+--------------------------------------------------------------+
    | gate 1 | Done. `Tir/Syntax.lean` is the grammar, `Tir/Interp.lean`    |
    |        | the definitional interpreter, `Tir/Exec.lean` the statement  |
    |        | evaluator and `Runs`, `Tir/Stable.lean` stability and        |
    |        | determinism, `Tir/Toy.lean` four programs run against known  |
    |        | answers at elaboration time.                                 |
    +--------+--------------------------------------------------------------+
    | gate 2 | In, as checks rather than as theorems. `Tir/Print.lean` is   |
    |        | the canonical printer, `Tir/Decode.lean` the audited decoder,|
    |        | and `Tir/PrintCheck.lean` holds the printer to               |
    |        | `serialize.dumps` byte for byte and runs the round trip both |
    |        | ways on the toy programs, with negative cases for the schema |
    |        | number, an unknown key and a non-object. What is outstanding |
    |        | is the *theorem*: `decode (print p) = ok p` for every well-  |
    |        | formed `p`, by structural induction, rather than on the      |
    |        | programs there happen to be.                                 |
    +--------+--------------------------------------------------------------+
    | gate 3 | In. `Tir/Artifact.lean` embeds the 2.8 megabytes of          |
    |        | `gen/engine.tir.json` with `include_str`, decodes them, and  |
    |        | prints the result back to the same bytes, checked at         |
    |        | elaboration time; the recorded sha256 sits beside it and     |
    |        | `tests/test_lean_pin.py` reads it back against the file.     |
    |        | A one-byte edit fails the build, provided the module is      |
    |        | re-elaborated — lake does not treat an `include_str` input as|
    |        | a dependency, so `make verify` deletes that one module's     |
    |        | build products first.                                        |
    +--------+--------------------------------------------------------------+
    | gate 4 | Not started: `region_kids` against `R.regionKids`.           |
    +--------+--------------------------------------------------------------+
    | gate 5 | The ledger is in and checked: `conformance/layer-i.json`,    |
    |        | 80 functions owed a lemma, 42 parser-exclusive, 0 proved.    |
    |        | The lemmas themselves are the milestone's bulk and are all   |
    |        | outstanding.                                                 |
    +--------+--------------------------------------------------------------+
    | gate 6 | Not started, and it cannot start before gate 5 closes.       |
    +--------+--------------------------------------------------------------+
    | gate 7 | In. `make verify` fails on generator drift, freeze-record    |
    |        | drift, ledger drift, a decode failure, a round-trip failure  |
    |        | and a broken proof. Each has been induced once and observed  |
    |        | to fail. What it still does not do is bind the *proofs* to   |
    |        | the artifact — the decode says the bytes are the program the |
    |        | Lean side names, and the lemmas that would say the program   |
    |        | means what layer R means are gate 5's.                       |
    +--------+--------------------------------------------------------------+

The artifact hash has not moved, which is the one invariant the whole plan
rests on: everything above deepens the Lean account of the frozen engine
and changes nothing the backends consume.
