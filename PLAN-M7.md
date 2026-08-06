# M7: Layer I, the refinement to the frozen artifact

DESIGN.md section 6 gives Layer I its shape: TIR syntax as inductive types
with a definitional interpreter, a Lean-side decoder that reads the canonical
`gen/engine.tir.json` bytes directly, a round-trip self-check, refinement
theorems against layer R, and a `make verify` gate that fails on a moved
hash, a drifted generated file, a failed decode or round trip, and any proof
that no longer builds. The stronger reading of that gate — that an engine
edit cannot land without the proof increment covering it — needs a lemma
per function before it has anything to withhold, so section 10 below
reschedules it to M7R, and the schedule risk goes with it. This plan is
where the milestone gets sequenced, and where its first decision gets made
rather than inherited.

The target is the artifact the `wave1-frozen` tag pins, sha256 `d60df8a5…`.
It does not move during M7. An engine change after the freeze re-opens
proofs deliberately and visibly, and gate 3 below is what makes that a
property of the build rather than of discipline — but only as far as the
proofs there are: a moved hash fails the build, and every proof that exists
is rebuilt against the new bytes. What it cannot yet do is refuse a change
to a function no lemma covers, because the lemmas are M7R's. The stronger
rule — the hash moves only together with the proof increment that covers
the change — becomes true when M7R closes, and section 10 is where that
was rescheduled.

## 1. The endpoint, stated first

This is the sentence the refinement exists to make provable, and `make
verify` is what will check it:

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

Section 10 moved the milestone boundary but not this sentence. It is M7R's
endpoint now rather than M7's, and M7 closes instead on the foundation the
gates below actually built: the embedding and its interpreter, the printer
and the audited decoder, the pinned artifact, the `make verify` gate, the
two simulation samples and the proof automation. Where each of those stands
is section 6; what the split cost and why is section 10.

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

    decodeProgram n (jsonOf (programJ p)) = .ok p

for every canonical `p : Program` and every budget past its nesting depth,
which is the direction that says the decoder loses nothing the printer
knows. Its converse holds only on canonical bytes and is gate 3's job.

The statement starts at the printer's tree rather than at its text on
purpose, and section 11 is where that boundary is argued: `decode` parses
before it decodes, and relating `renderJ` to `Lean.Json.parse` is a
parser-correctness development rather than a structural induction. What
covers the parse step is gate 3's byte comparison, on the artifact, and
`PrintCheck`'s on the toy programs.

Done when: that equation is proved by structural induction over all five
decoder families, the artifact is checked to be canonical, and there are
negative tests for the malformed cases the validator rejects.

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
    | I-2  | `decodeProgram n (jsonOf (programJ p)) = .ok p` for     gate 2 |
    |      | every canonical program at a sufficient budget, with negative  |
    |      | tests for what the validator rejects; the parse step stays     |
    |      | gate 3's byte comparison, per section 11                       |
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
those five failure modes has been induced once and observed to fail. From
then on a moved hash cannot pass unnoticed and no existing proof can go
stale against it. The stronger DESIGN.md rule — the hash moves only with the
proof increment that covers the change — needs a lemma per function to have
anything to withhold, so it arrives with M7R and not here.

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
    | gate 2 | Checks in, theorem started. `Tir/Print.lean` is the canonical|
    |        | printer, `Tir/Decode.lean` the audited decoder, and          |
    |        | `Tir/PrintCheck.lean` holds the printer to `serialize.dumps` |
    |        | byte for byte and runs the round trip both ways on the toy   |
    |        | programs, with negative cases for the schema number, an      |
    |        | unknown key and a non-object. `Tir/RoundTrip.lean` is the    |
    |        | theorem, and section 11 says how far it goes: the bridge to  |
    |        | `Lean.Json` is proved, and four of the five decoder families |
    |        | are inverted — the types, the constants, the expressions and |
    |        | places, and the statements. The declarations and the program |
    |        | remain, and the step from printed text to a parsed value is  |
    |        | named rather than proved.                                    |
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
    | gate 4 | Done. `Tir/RegionKids.lean` holds both loop invariants and   |
    |        | `region_kids_simulates`: the `Runs` statement against        |
    |        | `R.regionKids` from related inputs, under the parent-order   |
    |        | premise the checker's shape pass supplies and the size       |
    |        | bound the declared vec maximum supplies. Section 8 records   |
    |        | the pattern and the cost as the gate 5 template.             |
    +--------+--------------------------------------------------------------+
    | gate 5 | The ledger is in and checked: `conformance/layer-i.json`,    |
    |        | 80 functions owed a lemma, 42 parser-exclusive, 1 proved —   |
    |        | gate 4's. `pike_take` is proved conditionally on its callee  |
    |        | and does not count. The 79 others are the milestone's bulk,  |
    |        | and section 10 moves them to the refinement milestone.       |
    +--------+--------------------------------------------------------------+
    | gate 6 | Not started, and it cannot start before gate 5 closes, so    |
    |        | it moves with gate 5.                                        |
    +--------+--------------------------------------------------------------+
    | gate 7 | The verification infrastructure is complete: `make verify`   |
    |        | fails on generator drift, freeze-record drift, ledger        |
    |        | drift, a decode failure, a round-trip failure and a broken   |
    |        | proof, each induced once and observed to fail. It does not   |
    |        | yet bind the *proofs* to the artifact — the decode says the  |
    |        | bytes are the program the Lean side names, and the lemmas    |
    |        | that would say the program means what layer R means are      |
    |        | gate 5's — so this row is the harness in place, not the      |
    |        | proof gate closed.                                           |
    +--------+--------------------------------------------------------------+

The artifact hash has not moved, which is the one invariant the whole plan
rests on: everything above deepens the Lean account of the frozen engine
and changes nothing the backends consume.

Sections 8 to 10 are what those rows cost to find out, and section 10 is
where the milestone splits.

## 7. The checkpoint, and the order the next session opens in

Commit `53068bd` is the verified handoff: `make verify` passes there end to
end — 26 verification tests, the full Lean build, the corpus replay at 331
cases and 0 disagreements — on a clean tree. This closeout commit on top of
it changes documentation only, and the annotated tag `m7-foundation-20260806`
marks it; `wave1-frozen` does not move, for the reason gate 3 already gave.
The endpoint of section 1 has not been weakened anywhere. M7 stops here
because it is incomplete and too large to finish responsibly in one
stretch, not because anything is blocked — that distinction matters, and it
is why this is a checkpoint rather than a fallback.

The next proof session should not open with L-4. L-4 is owed eventually,
but it reveals nothing about whether the 80-function simulation campaign is
affordable, and that affordability is the decision the project currently
lacks. Gate 4 was designed as exactly that measurement point, so the order
is:

1. Prove gate 4's two `region_kids` loop invariants and the simulation
   theorem. Everything under them — the encoding, the artifact-read
   guards, the store algebra, `Tir/Step.lean` — is already in the build.

2. Review gate 4 the moment its statement, invariants and final lemma
   land, at that semantic boundary rather than per edit or eight commits
   late. Record the proof's size, the effort it took, what automation came
   out reusable, and how brittle it is.

3. Before scheduling gate 5, stratify the 80 owed functions by proof shape
   and dependency depth. `region_kids` exercises loops and the mutable
   store, not call-heavy VM composition; sample at least one function from
   that harder class before extrapolating a completion estimate.

4. Decide, explicitly. If the gate 4 pattern generalizes, close gate 2's
   theorem, then L-4 and L-5, then run gate 5 in reviewed dependency
   slices. If it does not, keep the endpoint but split M7 into this
   completed foundation and a later refinement milestone, or redesign the
   simulation automation — an 80-lemma manual treadmill is the one path
   this plan rules out.

All four steps are now done. Gate 4 is closed and reviewed (section 8),
the ledger is stratified and a second sample proved (section 9), and the
go/no-go is written down there.

## 8. Gate 4, measured

The number the gate existed to produce. The whole of it — the guarded
transcription, the automation it drew out of `Tir/Step.lean`, both
invariants, the end-to-end theorem, the review — cost one working session
and six compile iterations, none of which stalled on anything semantic:
the errors were constructor-name ambiguity, elaboration order around
tactic-block arguments, and one genuinely missing premise, the size bound,
which the proof surfaced and the statement now carries. `Tir/RegionKids.lean`
is ~550 lines; `Tir/Step.lean` grew 110 lines of automation that is not
`region_kids`-shaped at all — whole-statement steps (`evalStmt_push_var`,
`evalStmt_assign_var`, `evalStmt_assign_index_var`), reads through frozen
sequences, the `declare`/`get` algebra, and the in-range `u32` wrap.

The template, which is what gate 5 follows:

1. Transcribe the function as a term and `#guard` it against the decoded
   artifact — never state it from memory. The guard failing is the build
   telling you the artifact moved.

2. One invariant `structure` per loop, stated over what `Env.get` answers
   rather than over the store's shape — a body that declares in a loop
   shadows the previous round's local instead of replacing it. Capacities
   are existential where pushes happen and parameters where nothing grows.

3. One per-round lemma per loop under a universal budget (`∀ f`, since a
   straight-line body spends none), one loop lemma under an existential
   one, and `evalWhile_mono` to join loops under `max` at the very end.
   No statement anywhere quotes a fuel bound, which is `Runs` doing its
   job.

4. Intermediate stores named by `obtain ⟨env1, henv1⟩ : ∃ e, _ = e`, every
   fact about them derived through the `get_set`/`get_declare` algebra,
   and value spellings kept syntactic — `markVal n`, not a raw cast — so
   rewriting connects. The get-chains are the verbose part; they grow with
   statements times live locals and are entirely mechanical.

What this prices: `region_kids` is three parameters, three locals, twelve
statements counted the way the gate 5 ledger counts them, two loops — and
cost ~550 lines plus reusable automation. For
this one function, the mechanical get-chain portion tracked statements
times live locals; whether other control-flow and call shapes behave the
same is exactly what remains unmeasured. In particular it does not price
call composition — `region_kids` calls nothing — so the
`Runs`-transitivity story that gate 5's VM functions live on is still
unmeasured, which is exactly why section 7's step 3 samples a call-heavy
function before extrapolating.

## 9. The second sample, and the go/no-go

Gate 4 priced a loop-and-store function that calls nothing. The question it
could not answer is what a *call* costs, since gate 5's bulk is call-heavy.
So the 80 owed functions were stratified mechanically — `conformance/layer-i-strata.json`,
regenerated and compared by `tests/test_strata.py`, one row per function with
its shape, parameter modes, callees, dependency depth and transitive
closure — and a sample was chosen by a rule recorded in the report rather
than by feel: among unproved functions with at least one call inside a loop
and at least two call sites, minimise statements plus ten per loop. That
picked `pike_take` (21 statements, 1 loop, 2 call sites, 1 distinct callee)
over the provisionally suggested `pike_add` (187 statements, 49 in-loop
calls), which the rule ranks twelfth of fourteen.

`Tir/PikeTake.lean` proves `pike_take_simulates` against `Ref.pikeTake`,
*conditionally* on `ChargeGrowSim` — the `Runs`-shaped contract for its one
callee, which gate 5 owes `charge_grow` anyway. The ledger still reads 1 of
80 and must: a conditional lemma counts when its callee premises are
discharged and not before. To keep the hypothesis from being a wish, the
contract is also run against the artifact: seven `#guard`s interpret the
decoded `charge_grow` and compare it to `Ref.chargeGrow`, one input per
outcome the function has — reservation hit, growth at the floor, growth by
doubling, memory refusal, cost refusal, the declared maximum, and the
second call site's width. That is evidence, not the universally quantified
contract, which stays gate 5's lemma. Swapping two fields of the out-list
makes all seven fail, so they do discriminate.

What it measured:

    +--------------------------------+---------------+------------------+
    |                                | `region_kids` | `pike_take`      |
    +--------------------------------+---------------+------------------+
    | statements / loops / calls     | 12 / 2 / 0    | 21 / 1 / 2       |
    | proof lines, sample-specific   | ~550          | ~1240            |
    | lines per statement            | ~46           | ~59              |
    | reusable automation added      | 110           | 106 + ~85        |
    | store get-chain steps          | ~40           | 78               |
    | write-back expansions          | 0             | 4                |
    +--------------------------------+---------------+------------------+

The shape generalises: nothing about the call was hard, `Runs` composed by
transitivity exactly as gate 1 designed it, no lemma quotes a fuel bound,
and `evalStmt_call_runs` turned each call into a store update in one step.
Per statement the call-heavy function costs somewhat more than the
loop-heavy one, and what it costs it on is branching rather than calling:
`pike_take` has five exit paths and each re-steps the body in front of
it.

The cost does not generalise, and that is the finding. Per-statement cost
sits between 45 and 60 lines, and the artifact's owed functions hold 3052
statements. Linear extrapolation puts gate 5 near a hundred and sixty
thousand lines of proof. No schedule survives that, and it is not a
question of effort: the same two mechanical patterns are what fill the
lines. Seventy-eight get-chain steps in one function, each a rewrite that
says a name survived a write to another name. Four write-back expansions,
one per call site per callee outcome, each thirty-five lines of the same
plumbing — and the ledger holds 448 call sites.

So: **no-go for gate 5 as a manual campaign, go for an automation-first
redesign.** Concretely, before any further per-function lemma:

1. A store normaliser: a tactic that answers `Env.get n` against any chain
   of `set` and `declare` by walking the chain, instead of one rewrite per
   step. This is syntax-directed and decidable — the names are string
   literals — and it is where most of both proofs went.

2. A call-site tactic: given the callee's contract, discharge argument
   evaluation and write-back in one step rather than expanding them per
   outcome. `evalStmt_call_runs` already provides the semantic content;
   what is missing is the plumbing around it.

3. Re-measure on these same two functions. If the two together do not cut
   per-statement cost by roughly an order of magnitude, M7 splits: this
   foundation closes as its own milestone and the refinement of section 1
   becomes a later one, with THEOREMS.md stating plainly that layer I
   covers the interpreter, the decoder, the pinned artifact and two
   simulation lemmas rather than the composed theorem.

The endpoint of section 1 is not weakened by any of this. What changed is
the estimate of what reaching it costs, which is what the two samples were
built to find out — and finding it out before the campaign rather than a
third of the way through it is the whole reason the gates were ordered
this way.

Two numbers above were corrected after the fact. `region_kids` holds twelve
statements by the strata report's own count, not seven, and since that
report is where the 3052 comes from the two have to be counted the same
way; the per-statement figures and the extrapolation here are the corrected
ones. The claim about *where* the lines go was wrong too, at least across these
two functions, which is what section 10 measured rather than argued.

## 10. The automation, measured, and the split

Section 9 named two tools and a rule: build them, re-measure the same two
samples, and if together they do not cut per-statement cost by roughly an
order of magnitude, M7 splits. Both are built, both do what they were
supposed to do, and the rule fires anyway.

### What was built

`Tir/Step.lean` grew by 131 lines, in two pieces.

The store normaliser is four unconditional lemmas and a tactic. `Env.get_set`
and `Env.get_declare` say what a write answers for *any* name — an `if` on
the two names rather than a lemma per case — and since every name in the
artifact is a string literal, the condition decides itself. `readPlace_var_eq`
and `evalExpr_var_eq` do the same for a read, and `writePlace_var_isSome`
states a write's precondition on `Option.isSome` so that normalising the
store discharges it. `store [...]` is the `simp only` that runs all of them,
with the frame's base facts in the bracket and `← henv3` for whatever
intermediate stores the proof has named.

The call-site tool is `writeOuts`, `writeBack_eq_writeOuts` and
`evalStmt_call_outs`. The last is what a caller steps a call with now: given
the callee's contract in `Runs`, it gives the statement's effect in terms of
the out list alone, with no trace of the callee's frame left in it — so the
write-back is a chain of `set`s that `store` normalises like any other. The
one thing an out list cannot say by itself is whether a `false` in an `inout`
position is a value the callee left or a name the callee lost, which
`writeBack` tells apart. `OutsPresent` carries that, and it costs one `simp`
per callee — `cgOuts_present` here — because `charge_grow` writes back the
meter's three counters and an integer is never `false`.

That is a fast path and not a general answer, which is worth naming before
M7R leans on it. Fourteen of the eighty owed functions take a boolean
`inout` parameter — `sat_add`, `charge_call`, `cert_install`, both `poly_`
functions, both `sat_` ones, the four `price_` ones, the three `scan_` ones
and `pike_room` — and for a callee that legitimately answers `false`
through one, `OutsPresent` is not merely inconvenient but false. What that
case wants is either the name-preservation theorem, that no TIR statement
removes a binding, which is a walk over the whole interpreter about the
size of `Tir/Stable.lean`, or a call step stated over the callee's frame
instead of over its outs. Either way it is M7R's, and it is on the list
before the campaign rather than during it.

### What it removed

Every explicit walk past a write: 143 uses of `Env.get_set_other` and
`Env.get_declare_other` between the two files, now none, in favour of 63
`store` calls. The four write-back expansions: 16 `writePlace_var`
applications and 12 `slot_of_out` applications, now none, one `store` line
each. The five out-list read-outs, twenty hand-written lines apiece, now one
`store` call each. The two mechanical patterns section 9 named are not
reduced; they are gone.

### What it measured

Code lines, comments and blanks stripped, which is why these baselines are
smaller than the raw-line figures in section 8.

    +-----------------------------+---------------+------------------+
    |                             | `region_kids` | `pike_take`      |
    +-----------------------------+---------------+------------------+
    | statements                  | 12            | 21               |
    | proof lines before          | 455           | 1293             |
    | proof lines after           | 364           | 836              |
    | lines per statement, before | 38            | 62               |
    | lines per statement, after  | 30            | 40               |
    | store-fact `have`s, before  | 19            | 37               |
    | store-fact `have`s, after   | 10            | 29               |
    +-----------------------------+---------------+------------------+

Together the two samples fell from 1748 lines to 1200, against 131 lines of
shared automation. Over the 33 statements they hold — counted the way the
strata report counts the 3052 the ledger owes, which section 9 did not do
for `region_kids` — that is 53 lines per statement down to 36, a factor of
1.45.

### Why so little

Because the estimate section 9 rested on was wrong, and that is the part
worth writing down. It said the two mechanical patterns "are what fill the
lines". Removing them completely took out about a third of the proof. The
rest was never the walking. It is the *saying*.

What is left, largest first. The statements themselves: thirty-nine `have`s
that spell out what the store holds at some intermediate point, each with a
full type and value, because the step lemma wants it as a typed hypothesis
and because `simp only` will not close a goal against a metavariable — so
the implicits get pinned by hand at the call site instead. Then the branch
plumbing: `pike_take` has five exit paths and each one re-steps the prefix
of the body that precedes it, which no lemma about a single statement can
share. Then the step applications themselves, one per statement per path.
And last the genuine side conditions — the bounds, the `omega`s,
`chargeGrow_cap` — which are the semantic content and are supposed to be
there.

A third tool would go after the first of those: a symbolic executor that
reads the step lemma off the statement's head, computes the store it leaves,
discharges the preconditions with `store`, and hands back only the real side
conditions as goals. On these two samples that looks worth another factor of
two or three. It is worth having. It is not an order of magnitude either,
and the honest reason is that the second and third items on that list do not
move for it.

### The decision

Thirty-six lines per statement over the 3052 statements the ledger owes is
about 110,000 lines, down from 162,000. Section 9's rule fires: **M7
splits.**

What that means, concretely:

* M7 closes as the layer I *foundation*: the deep embedding and its
  interpreter, stability and determinism, the printer and the audited
  decoder with their checks, the pinned artifact, the `make verify` harness,
  two loop-invariant samples — one proved outright, one conditional on its
  callee — and the automation this section measured. THEOREMS.md section 5
  now carries a layer I inventory saying exactly that and no more.
* The refinement of section 1 becomes its own milestone — M7R in DESIGN.md
  section 9 — scheduled after M8 rather than in front of it. Its first task
  is the symbolic executor, not the next per-function lemma. Gate 0's L-4
  and L-5 travel with it, since what they exist for is the compiler
  simulation lemma; gate 2's round-trip theorem stays with the foundation,
  where it belongs.
* Nothing in section 1's endpoint is weakened or withdrawn. What changed is
  when it arrives, and the estimate of what it costs.
* Until it does arrive, the fallback DESIGN.md section 10 already documents
  is the one in force: releases stay 0.x, with layers S and R proved and
  layer I covered by the decoder, the pin, the round trip and the corpus
  replay — stated as such, which THEOREMS.md now does.

The artifact hash still has not moved.

## 11. Gate 2, decomposed

`decode` is `Lean.Json.parse` and then `decodeProgram`, so `decode (print p)
= ok p` is two theorems and not one, and they are not the same size.

The *syntactic* half — `Json.parse (renderJ v 0 ++ "\n") = ok (jsonOf v)` —
relates the renderer to a parser this repository did not write and Lean does
not give a compositional account of. That is a parser-correctness
development, not a structural induction, and it is not what gate 2 was
scoped as. It stays covered the way it is covered today: gate 3 prints what
it decoded and compares bytes, on the artifact, and `PrintCheck` does the
same on the toy programs.

The *semantic* half is the one being proved, and it starts one step in:

    decodeProgram n (jsonOf (programJ p)) = .ok p

for `p` canonical and `n` past its nesting depth. `jsonOf` is the bridge —
the same `Json.mkObj` a parser would have built from a canonical document,
so nothing in the statement is invented to make the proof easier.

What landed:

* the map fact everything rests on. The decoder reads an object as the list
  `Std.TreeMap.Raw.toList` hands back, so the round trip needs that building
  a map from a strictly key-sorted list and reading it back is the identity.
  `jFields_mkObj` is that, over `Std`'s own `ordered_keys_toList` and a
  thirty-line lemma that two sorted lists with the same members are the same
  list;
* `jsonOf` and the leaf readers, and the one-key-object step every tagged
  form goes through;
* `decodeTy_tyJ`: the first of the five decoder families, with `tyDepth` for
  the budget and `Ty.Canonical` for the premise — which for a type is only
  that the names it carries are names;
* the hex round trip, `hexToBytes_hexBytes`, which a constant's bytes need
  and which holds of every byte list rather than of a canonical one, so it
  is proved outright instead of assumed;
* `jFields_mkObj_perm`, the map bridge generalised to a permutation, since
  what the printer hands the map for a constant's fields or a struct value's
  is the sorted list and what the canonicality premise talks about is the
  original;
* `decodeConst_constJ` and its two list companions: the second family, and
  the first one whose premise says something about order. A constant's
  fields are printed as an object, an object hands its members back sorted,
  so `ConstValue.Canonical` requires the entries to be in that order
  already. `SortedKeys` is that condition, and `jFields_constEntries` is
  where `jFields_mkObj_perm` gets spent;
* a decision procedure for every canonicality predicate. This was not on the
  list for the constants step, and it is here because the artifact's premise
  has to be discharged by reduction rather than by hand: a `Canonical` no
  machine can settle is a premise that can only be stated. `by decide`
  settles it now on every family proved so far, and each family carries the
  same three checks: the predicate on a sample, the inversion instantiated at
  exactly the depth its `*Depth` function gives, and a guard that one unit
  less fails. The types were the family that had the theorem but not the
  evidence, and a review is what found that;
* `decodeExpr_exprJ`, `decodeExprFields_exprEntries` and
  `decodePlace_placeJ`: the third family. A struct value's members are the
  second and last place in the schema where the keys are a program's own
  names, so `SortedKeys` and `jFields_mkObj_perm` come back unchanged; a
  `cast` carries a type, so its clause spends `decodeTy_tyJ` and the premise
  reaches back into the first family; and the operators cost the premise
  nothing, since they are written from a closed table and read back through
  its inverse;
* `jsonOf_jobj_fields`, the bridge for a form with more than one key. This is
  where `jobj`'s sort stops being a formality: expressions are the first
  family that prints members out of key order — `op` before `left` and
  `right` — so the sorted list has to be computed rather than read off the
  printer, which `simp [jobj, List.mergeSort]` does even where the values are
  variables.
* `decodeStmt_stmtJ`, `decodeBody_bodyJ` and `decodeArms_armsJ`, with
  `decodeArg_argJ` and `decodeArgs_argsJ` beside them: the fourth family, and
  the first whose recursion has three layers rather than two. The three
  mutual proofs carry the decoder's own `(fuel, kind, length)` measure, a
  body outranking the statements in it and an arm list the bodies in it; the
  two argument proofs sit outside the block, because an argument holds an
  expression or a place and never a statement. The arms carry no ordering
  premise, since the printer writes them as an array and does not sort it;
* `optD_optExprJ` and `optD_optPlaceJ`, for the optional fields. `optD` reads
  `null` as absent, so each of these has an absent half that is `rfl` and a
  present half that needs to know the printer wrote something other than
  `null` there — which is a fact about the printer rather than about the
  program, and is proved once for an object and once for an array. The switch
  default is the one occurrence spelled out where it stands instead, because
  its body belongs to the mutual induction and a lemma outside the block
  could not mention it;

What that cost, because what is left wants an estimate rather than a guess:
222 code lines at the type-family checkpoint, of which 80 are the seven type
clauses and the rest is shared; 269 with the two constant prerequisites
added; 436 with the constants family in; 867 with expressions and places in
and the type family's own evidence beside it; and 1387 with the statements
in. Every clause spends the shared part rather than growing it. Almost every
object the printer builds has the schema's own keys rather than a program's,
so `jobj`'s sort and the map's order both *compute* — `simp [jobj,
List.mergeSort]` runs them, and the `closed`/`need` chain after that is
`rfl`. The two clauses whose keys are a program's own — a constant's fields
and a struct value's — are where `jFields_mkObj_perm` is spent, and they are
the only two the schema has.

The constants figure, seven lines to a clause on sixty of scaffolding,
turned out to be the wrong unit and it is worth saying why before it is used
again. Expressions and places cost 420 lines: 229 for the nineteen
expression clauses and the exhausted-budget one, 14 for the list companion
that walks a struct value's members, 100 for the scaffolding, 52 for places
and 25 for the evidence. That is about twelve lines a clause rather than
seven, and the reason is that a clause costs roughly what its object has
members, not what its family has forms. Most constant forms are a leaf or a
single payload; most expression forms are a two- or three-member object, and
every member is a line of the `show` that spells out what the decoder's step
left and a rewrite that discharges it.

Statements were predicted to be the wider of the two that remained, and they
were. Measured against the denominator this section wrote down beforehand,
the family came to 520 code lines: 248 for the nineteen `decodeStmt_stmtJ`
clauses, 10 for the body companion and 22 for the arm-list one, 25 for the
two argument inversions, 149 for the scaffolding — depths, canonicality
predicates and decision procedures, seven shapes of each — 34 for the
optional-field lemmas and the two not-null facts underneath them, 8 for
`stmtDepth_pos`, and 24 for the evidence.

Nineteen clauses rather than the eighteen the denominator counted, because
the switch splits on whether it has a default; that is what lets `stmtDepth`
and `Stmt.Canonical` stay structural instead of reaching through an
`Option`. At thirteen lines a clause that is the expression figure again,
one line up, and it holds for the same reason: a clause costs what its
object has members. What did *not* repeat is the scaffolding, 149 lines
against expressions' hundred, because the family has seven shapes where
expressions had two and each wants a depth, a predicate and a decision
procedure — and the decision procedures alone are 66 lines of
`instDecidableAnd` with nothing to say.

Two things came in under the estimate. The three-component measure was
expected to be the hard part and was not: `(n, 0, 0)`, `(n, 1, body.length)`
and `(n, 2, arms.length)` transcribed off the decoder are what Lean wanted,
and nothing about the fuel needed proving. And the four optional fields cost
34 lines rather than a clause apiece, because three of the four go through
one of two lemmas and only the switch default, whose body belongs to the
mutual induction, had to be spelled out where it stands.

The declarations and the program are fewer forms but bring one genuinely new
obligation — `programJ` sorts the four declaration lists by name, so
`Program.Canonical` has to require them *strictly* ordered by name the way
`SortedKeys` orders object members, which rules out duplicate declaration
names as well as undoing the sort, and it has to carry each declaration's
own canonicality underneath. That premise then has to be shown true of the
artifact rather than merely stated of it, and if the kernel cannot reduce
`decide` over 2.8 MB the check stays a `#guard` — which is the interpreter
and not the kernel, and has to be written down as such wherever the result
is quoted. Then `decodeDepth`, the composed theorem, and the artifact check.
That is what is left. Gate 2 is started and is not closed, and M7 does not
get its tag until it is.