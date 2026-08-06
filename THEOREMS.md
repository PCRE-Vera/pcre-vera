# The frozen wave 1 artifact, and what M6 has to prove about it

DESIGN.md section 9 asks M6 to begin by freezing and tagging a wave 1 IR
artifact, so that the reference proofs of M6 and the refinement proof of M7
target one fixed thing while M8 goes on landing features. This document is that
freeze and the inventory that goes with it: what will be proved, in what order,
against which bytes, and — just as important — what will not be.

The inventory was written before the Lean, deliberately. Writing the statements
down first is what turns "prove the engine correct" into a list somebody can
argue with, and it is cheaper to find out now that a theorem is unstatable than
after a month of tactic work. Section 5 records what has since been proved
against it, item by item; nothing there rounds up.

## 1. What is frozen

Every hash below names a file in this checkout, and `tests/test_freeze.py`
holds it to that file. A freeze record that has quietly gone stale is worse
than none, since the thing it is for is being the one place where the identity
of the frozen artifact is written down.

    +--------------------------+------------------------------------------+
    | the artifact             | gen/engine.tir.json                      |
    | the artifact sha256      | d60df8a5600a4a0d4d1d1ea21e90883eab44d35a |
    |                          | 8f71e1d5450daf0a61b5dd1f                 |
    | the commit               | the one tagged wave1-frozen              |
    | the pcre2 version        | 10.47                                    |
    | the pcre2 tarball sha256 | 47fe8c99461250d42f89e6e8fdaeba9da057855d |
    |                          | 06eb7fc08d9ca03fd08d7bc7                 |
    | the pin file             | oracle/pcre2-pin.toml                    |
    | the pin sha256           | 297b9f5d284069196d340c9e14adba54ea7bbe4f |
    |                          | fc2d89897dbe27c48d130e1a                 |
    +--------------------------+------------------------------------------+

The commit row is the only line in this document that no file can contradict,
so it has a check of its own. The tag moves onto whichever commit lands the
hashes above, and from then on `tests/test_freeze.py` requires it to hold that
artifact: a tag left pointing at the previous freeze is the same silent
staleness the hashes exist to prevent, and worse, since the record would be
true of the working tree and wrong for anyone who followed it. While a refreeze
is still only in the working tree there is nothing to compare and the test says
so rather than passing quietly.

The corpora the artifact is held to, by content hash:

    +--------------------------------------+------------------------------------------+
    | oracle/corpus/wave1.json             | 983a3413fa73df9177e88f93186ec81d80733d26 |
    |                                      | 80caf1cf925b496648f1a714                 |
    | oracle/corpus/sweep-regressions.json | 815d58542aba14629d859b0f9978627c3293d3ee |
    |                                      | ddba3c0fc4e2b367a9f954bf                 |
    | oracle/corpus/pre-lowering.json      | c792f47491acc1da164579210f52b144f326144e |
    |                                      | 4ba0a4da7b65d0e2dd53b2c8                 |
    | conformance/corpus.json              | a7349f418f8fbd2c139d5a487284686f1111cd4c |
    |                                      | 13b600736dde421acd518092                 |
    | conformance/certificates.json        | 587da12e186553d784d813e0d99a13bc6c1423c5 |
    |                                      | 3b7cf4f76083d92ca9ac3daf                 |
    | conformance/lowering.json            | 88f537fcd39b5c718b12167fdbdc85e9782383eb |
    |                                      | 872dc432b7637ad9ac369748                 |
    | conformance/migration.json           | 71134fb9e29a5cfafbf9e930c3150b9482fc0505 |
    |                                      | 962207f8280e212fccc7b182                 |
    | conformance/sweep.json               | ee48262d0088ea45caf8d6f7f603c724f3b2afa0 |
    |                                      | cbae2b062647a232f4994a75                 |
    +--------------------------------------+------------------------------------------+

One of those is not a corpus this artifact answers.
`oracle/corpus/pre-lowering.json` is what the engine of the commit named in it
said about the same 334 patterns, which is the half of the quantifier
lowering's census that compares two engines rather than describing one. It is
hashed here with the rest because it is evidence a test reads, and a
measurement nobody can take again is exactly the kind of file that goes stale
without anyone noticing. Most of it is not taken on trust either: 218 of those
patterns were left alone by the lowering, and `tests/test_migration.py` asks
this engine to reproduce every column the recording holds about them, the hash
of the emitted program included. They compile to what they always compiled to.
The 116 the lowering rewrote are the part only the recording can speak for.

And the campaign that refroze the artifact after the quantifier lowering,
which is reproducible rather than kept:

    make sweep SWEEP="--seed 20260805 --structured 2000 --hostile 400 \
        --subjects 32 --jobs 8 --out tmp/sweep-post-m6"

    manifest sha256
      424981106c7c589964c25bb766b8c6f150b86e6481d7af1eff99f8c9fe5b82e3

The LOG entry carries its counts. A rerun of that command on this
artifact reproduces the manifest hash exactly — the test rebuilds the manifest
from those five numbers and checks it — and the answers are a function of the
artifact, so a rerun that disagrees is a regression rather than noise.

## 2. Layer S, the specification

Two parts, because one function cannot honestly describe both what PCRE means
and when our matchers give up (DESIGN.md section 6).

    +------+------------------------+--------------------------------------+
    | S-1  | Pattern                | the wave 1 AST as an inductive type, |
    |      |                        | options as parameters                |
    | S-2  | Matches                | priority-ordered big-step search;    |
    |      |                        | Found with captures, NotFound, or    |
    |      |                        | BadInput, and nothing else           |
    | S-3  | matches_stable         | beyond a computable sufficient fuel  |
    |      |                        | the answer no longer changes         |
    | S-4  | Matches, total         | S-2 read at the stable fuel of S-3,  |
    |      |                        | so totality is earned                |
    | S-5  | Config, Limits, Exec   | the internal configuration domain,   |
    |      |                        | wider than the public API: Pike,     |
    |      |                        | backtracking, memoized, each with    |
    |      |                        | or without a context                 |
    | S-6  | CreateCtx              | the creation step, its one-time      |
    |      |                        | reservation and zeroing charged      |
    |      |                        | against the creation limits          |
    | S-7  | exec_badinput_iff      | Exec answers BadInput exactly where  |
    |      |                        | Matches does, plus the execution-    |
    |      |                        | only cases: invalid limits, a        |
    |      |                        | subject past a context's declared    |
    |      |                        | maximum, a call raising a limit or   |
    |      |                        | switching configuration              |
    | S-8  | exec_refines           | whenever Exec cfg answers Found or   |
    |      |                        | NotFound, that answer is Matches     |
    | S-9  | exec_monotone          | raising a limit never changes a      |
    |      |                        | Found or NotFound; it can only turn  |
    |      |                        | ResourceExceeded into one. Both      |
    |      |                        | limit vectors have to be ones the    |
    |      |                        | configuration admits, which on a     |
    |      |                        | context means at or below the baked  |
    |      |                        | ceilings: raising a call past them   |
    |      |                        | is the BadInput of S-7, not a        |
    |      |                        | counterexample to monotonicity       |
    | S-10 | exec_sufficient        | every limit at or above the          |
    |      |                        | analyzer's bound for that            |
    |      |                        | configuration rules ResourceExceeded |
    |      |                        | out                                  |
    | S-11 | ctx_sufficient         | S-10 for a context, conditional on   |
    |      |                        | creation having succeeded, over the  |
    |      |                        | calls the context admits             |
    | S-12 | matchers_agree         | corollary of S-8 and S-10: on a      |
    |      |                        | Pike-eligible pattern the Pike and   |
    |      |                        | plain-backtracking configurations    |
    |      |                        | agree under sufficient budgets       |
    +------+------------------------+--------------------------------------+

S-12 is the theorem the cross-matcher half of the sweep is the empirical
shadow of, and the sweep is why it is worth stating: the harness has already
run both matchers against each other on every Pike-eligible case of a 2400
pattern campaign, so a proof attempt that fails here is far more likely to be
a bad statement than a real disagreement.

## 3. Layer R, the reference engine

Executable Lean, structured like the real engine, so the M7 simulation lemmas
are mechanical rather than inventive.

    +------+------------------------+--------------------------------------+
    | R-1  | R.compile              | spec AST to bytecode, the compiler   |
    |      |                        | of the real engine restated          |
    | R-2  | R.run                  | the bytecode under a configuration:  |
    |      |                        | same VM loops, same cost accounting, |
    |      |                        | same context split                   |
    | R-3  | R.createCtx            | the creation step of S-6, executable |
    | R-4  | run_compile_eq_exec    | R.run cfg (R.compile p) s pos opts   |
    |      |                        | lim = Exec cfg p s pos opts lim,     |
    |      |                        | soundness and completeness in one    |
    |      |                        | equation                             |
    | R-5  | run_terminates         | every R.run call halts: the          |
    |      |                        | backtracking loop by the cost        |
    |      |                        | charge, the Pike loop by the         |
    |      |                        | position and list bounds             |
    | R-6  | run_cost_le            | the cost R.run charges is at most    |
    |      |                        | the certificate's cost bound at the  |
    |      |                        | subject length                       |
    | R-7  | run_stack_le           | the same for backtrack entries       |
    | R-8  | run_mem_le             | the same for scratch bytes, memory   |
    |      |                        | counted as BOUNDS.md section 3       |
    |      |                        | counts it: peak allocated capacity,  |
    |      |                        | growth overlap included              |
    | R-9  | ctx_reserves_bound     | a created context's resident bytes   |
    |      |                        | are worstCaseMemory at the declared  |
    |      |                        | maximum, and no call on it allocates |
    | R-10 | ref_agrees_with_corpus | R.compile and R.run, evaluated on    |
    |      |                        | the committed corpora, give the      |
    |      |                        | recorded answers                     |
    +------+------------------------+--------------------------------------+

R-6 through R-9 are the resource-bound family, and they are stated against the
certificate the analyzer produced rather than against a freshly derived
number: the checker of DESIGN.md section 5 is what makes a certificate
believable, and layer A proves the checker rather than the search. The bounds
are the ones BOUNDS.md writes down, so a proof that needs a different equation
is a bug in BOUNDS.md first.

R-10 is the one that runs rather than proves, and it comes early on purpose.
The moment `R.compile` and `R.run` exist they get pointed at
`conformance/corpus.json` and `conformance/sweep.json`, so executability and
pcre2 agreement are exercised the whole way through M6 instead of being
discovered at the end. It ended up as a compiled executable rather than
`#eval`, because the sweep shard's resource half wants the observed cost,
stack and memory of every trial compared to the unit and `make lean` should
be able to say so in one line. A reference engine that cannot be run
is a reference engine nobody has checked against the arbiter, and the corpora
are already the form every other implementation is held to.

## 4. What is not claimed

The trust boundary is DESIGN.md section 11's, restated here because an
inventory that lists only what is proved reads as a claim about everything
else.

Parser correctness is deferred to M10. Until then every theorem above
quantifies over spec ASTs, and the step from pattern text to AST is a tested
link — the oracle corpus, the sweep and pcre2 itself — not a proved one.
Wherever coverage is described, that sentence goes with it.

The quantifier lowering of DESIGN.md section 4.3 is still inside that link,
and naming it is the point of saying so: the tree the theorems are about is
the one the code generator walked, which for a lowered pattern is the
rewritten one. The rewrite itself is no longer untheorised — L-1 to L-3 of
section 6 are proved, and `Matches_lower` says the lowered tree answers what
the written one answers — but the *pipeline* still relies on the bridge
handing `R.compile` the rewritten tree rather than on `R.compile` doing the
rewrite, so the link is as wide as it was. Narrowing it is L-4 and L-5, and
until they land what holds this step is the corpus replay, which compiles the
exported tree and compares the bytecode, the region tree, the ovector and the
usage to the engine's, plus the sweep's comparison with pcre2.

The generated Go and JavaScript are tested links too, and stay that way. The
proofs cover the TIR artifact under the TIR semantics; the printers are kept
dumb and are held to the artifact by the conformance corpora, the lowering
probe and the sweep shard, in all three languages bit for bit. No theorem
mentions Go or JavaScript.

The specification itself cannot be related to the pinned C library by any
theorem. The spec-to-pcre2 correspondence rests on the spec's auditability and
on differential testing of everything downstream of it, feature by feature.
That is the standard trusted-spec caveat, and the release notes carry it
verbatim.

Wave 2 and wave 3 constructs are outside the frozen artifact entirely. They
land in M8 and M10, each with its own artifact and its own inventory, and the
gating rule of DESIGN.md section 6 keeps an unproved feature behind
`allowUnproved` rather than in the default surface.

## 5. What is proved

The Lean lives in `lean/Pcrevera`: `Spec/` is layer S, `Ref/` is layer R,
`Corpus/` is the replay of section 3's R-10, and `Proofs/` is everything
below. `lake build` checks all of it and `make lean` runs the replay after
it. Nothing anywhere uses `sorry` or `partial`, and every theorem named
below depends on nothing beyond Lean's own three axioms.

    +------+------------------------+--------------------------------------+
    | S-1  | proved                 | Spec/Ast.lean                        |
    | S-2  | proved                 | Spec/Match.lean, matchesF            |
    | S-3  | proved                 | Spec/Total.lean, matches_stable      |
    | S-4  | proved                 | Spec/Total.lean, Matches             |
    | S-5  | proved                 | Ref/Exec.lean, Config and Exec       |
    | S-6  | proved                 | Ref/Exec.lean, createCtx             |
    | S-7  | proved                 | Proofs/BadInput.lean                 |
    | S-8  | proved for both        | Proofs/Refine.lean,                  |
    |      | matchers, over the     | btRun_refines_matches;               |
    |      | whole Config domain    | Proofs/PikeRefine.lean,              |
    |      |                        | pikeRun_refines_matches; the Exec    |
    |      |                        | wrappers in Proofs/ExecBacktrack.lean|
    |      |                        | and Proofs/ExecPike.lean; contexts   |
    |      |                        | in Proofs/ExecContext.lean,          |
    |      |                        | exec_refinesAnswers                  |
    | S-9  | proved                 | Proofs/Monotone.lean, exec_monotone  |
    | S-10 | proved for both        | Proofs/RepRun.lean,                  |
    |      | matchers, plain call   | btRun_inBudget_counted;              |
    |      | and context call alike | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_inBudget and                 |
    |      |                        | pikeRun_inBudget_ctx                 |
    | S-11 | proved, with nothing   | Proofs/CtxSufficient.lean,           |
    |      | assumed about the run  | ctx_sufficient; the two paths in     |
    |      |                        | ctx_sufficient_pike and              |
    |      |                        | ctx_sufficient_bt                    |
    | S-12 | proved for every wave  | Proofs/ExecPike.lean,                |
    |      | 1 pattern, the budget  | matchers_agree_wf; the budgets       |
    |      | premise inherent;      | discharged in                        |
    |      | discharged from        | Proofs/AgreeSufficient.lean,         |
    |      | certificates for every | matchers_agree_sufficient            |
    |      | Pike-eligible pattern  |                                      |
    +------+------------------------+--------------------------------------+

    +------+------------------------+--------------------------------------+
    | R-1  | proved                 | Ref/Compile.lean                     |
    | R-2  | proved                 | Ref/VM.lean, Ref/Pike.lean           |
    | R-3  | proved                 | Ref/Context.lean                     |
    | R-4  | proved                 | Ref/Exec.lean                        |
    | R-5  | proved                 | Proofs/BtTermination.lean,           |
    |      |                        | Proofs/PikeTermination.lean          |
    | R-6  | proved for both        | Proofs/RepRun.lean,                  |
    |      | matchers               | btRun_cost_le_counted;               |
    |      |                        | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_cost_le_check                |
    | R-7  | proved for both        | Proofs/RepRun.lean,                  |
    |      | matchers               | btRun_stack_le_counted;              |
    |      |                        | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_stack_le                     |
    | R-8  | proved for both        | Proofs/RepRun.lean,                  |
    |      | matchers               | btRun_mem_le_counted;                |
    |      |                        | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_mem_le_check                 |
    | R-9  | creation proved; the   | Proofs/CtxReserve.lean,              |
    |      | no-allocation half     | ctx_resident_eq_reservation;         |
    |      | proved for a context   | Proofs/CtxSufficient.lean,           |
    |      | call on both matchers  | ctxMatch_no_growth_pike and          |
    |      |                        | ctxMatch_no_growth_bt; the cores     |
    |      |                        | underneath in Proofs/RepRun.lean,    |
    |      |                        | btRun_no_growth_ctx_counted, and     |
    |      |                        | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_no_growth                    |
    | R-10 | proved by running      | lean/CorpusCheck.lean                |
    +------+------------------------+--------------------------------------+

Layer I is the deep embedding of the artifact's own IR and what has been
proved about it. It is a *foundation* and not the refinement: the composed
statement PLAN-M7.md section 1 writes down is not proved, and the reason it
is not is measured rather than guessed — PLAN-M7.md section 10 prices the
per-function simulation campaign at roughly 110,000 lines of proof after
automation, and splits the milestone on that number. What the entries below
say is what they say and nothing beyond it.

    +------+------------------------+--------------------------------------+
    | I-1  | proved                 | Tir/Syntax.lean, Tir/Interp.lean,    |
    |      |                        | Tir/Exec.lean; Tir/Stable.lean,      |
    |      |                        | runs_stable and runs_unique          |
    | I-2  | checked; the theorem   | Tir/Print.lean, Tir/Decode.lean;     |
    |      | started, not finished  | Tir/PrintCheck.lean holds the        |
    |      |                        | printer to serialize.dumps byte for  |
    |      |                        | byte and round-trips the toy         |
    |      |                        | programs both ways, with negative    |
    |      |                        | cases. Tir/RoundTrip.lean proves the |
    |      |                        | Json.mkObj bridge and inverts the    |
    |      |                        | type, constant, expression and place |
    |      |                        | decoders; the statements, the        |
    |      |                        | declarations and the program are     |
    |      |                        | outstanding. The step from printed   |
    |      |                        | text to a parsed value stays a check |
    |      |                        | rather than a theorem. PLAN-M7.md    |
    |      |                        | section 11                           |
    | I-3  | proved by elaborating  | Tir/Artifact.lean: the 2.8 MB of     |
    |      |                        | gen/engine.tir.json decode and print |
    |      |                        | back to the same bytes, and the      |
    |      |                        | sha256 beside them is the one        |
    |      |                        | tests/test_lean_pin.py reads off the |
    |      |                        | file                                 |
    | I-4  | proved                 | Tir/RegionKids.lean,                 |
    |      |                        | region_kids_simulates, against       |
    |      |                        | Ref.regionKids                       |
    | I-5  | not started            | see PLAN-M7.md section 10            |
    | I-6  | not started            | see PLAN-M7.md section 10            |
    | I-7  | one function, and      | Tir/PikeTake.lean,                   |
    |      | conditionally: proved  | pike_take_simulates, the pool        |
    |      | given a contract for   | allocator. It assumes ChargeGrowSim, |
    |      | charge_grow, which is  | the Runs contract the campaign owes  |
    |      | itself unproved        | charge_grow anyway. Seven #guards    |
    |      |                        | run the decoded charge_grow against  |
    |      |                        | Ref.chargeGrow, which is evidence    |
    |      |                        | for the hypothesis and not a proof   |
    |      |                        | of it. The coverage ledger does not  |
    |      |                        | count this theorem                   |
    | I-8  | not started            | see PLAN-M7.md section 10            |
    | I-9  | not started            | see PLAN-M7.md section 10            |
    | I-10 | not started; it is the | see PLAN-M7.md section 1 for the     |
    |      | composition of I-5 to  | statement it would be                |
    |      | I-9 and cannot precede |                                      |
    |      | them                   |                                      |
    +------+------------------------+--------------------------------------+

So the artifact is pinned, audited into Lean, and read back to its own
bytes, and one of its eighty post-parse functions is proved to mean what
layer R means. The engine the backends consume is still tied to layers S
and R by the corpus replay and the sweep rather than by a theorem, which is
the fallback DESIGN.md section 10 documents, and it is the one in force.

No entry carries a class of patterns any more. What every theorem with a
backtracking run in it does carry is `ReRules`, the six rules listed at the
end of this section: properties of the compiler's output that `cert_check`
does not check. All six are proved of `Ref.compile` in
`Proofs/RepCompile.lean`, so a pattern discharges them rather than a caller
asserting them, and the theorems stated over a pattern carry none of them.
What still carries them is a theorem stated over an arbitrary program, which
has to. Naming that once rather than in seven rows is the honest shape of
it.

S-8 is proved for both matchers, at every start offset, under every
combination of match options, and over the whole `Config` domain rather
than the two plain configurations alone. A context configuration runs the
same core on scratch reserved earlier, and the core theorems quantify over
the starting scratch, so `exec_refinesAnswers` carries the refinement
across every configuration `Exec` admits. It states the two clauses the
inventory names — Found and NotFound are `Matches` — and not the BadInput
coincidence the plain wrappers can also offer, because a context refuses
calls the specification has no opinion about at all: the wrong matcher,
creation parameters the engine declines, a memory limit off the
reservation, a subject past the declared maximum, a limit raised past what
creation paid for. Those are S-7's, and `exec_badinput_iff` is where they
are characterized. The backtracking half covers every wave 1
construct — literals, classes, the dot, `\R`, every anchor, groups,
alternation and every quantifier. The lockstep half is stated over the same
patterns but carries one side condition the other does not: the program is
eligible. That is the hypothesis `(compile p).pike = true`, and it is a real
restriction rather than a formality — `pike_ok` refuses a program holding
`\R`, a repetition that is not a pure star, or a star whose body can finish an
iteration without consuming a byte. That is a condition on the program rather
than on the spelling, and since the quantifier lowering a counted repetition
usually compiles to copies and a star, the patterns it leaves out are the
three carve-outs of DESIGN.md section 2.1. It sits in the statement rather
than in the conclusion because an ineligible program is one the matcher
declines at the door, for a reason the specification has no opinion about.
The argument is four layers deep — the
epsilon closure against the backtracking mirror, one position's thread list
against the merge of the attempts still running, one position's seed, and
the position loop against `Spec.scan` — and the middle layers are where the
lockstep matcher earns what it does differently: a built list is several
attempts side by side in leftmost order, and its visited set deduplicates
across them.

S-12 is proved as the corollary DESIGN.md section 6 says it is — two runs
refining the same specification and both completing answer the same thing.
Both of its refinement premises are discharged rather than assumed:
`matchers_agree_wf` asks only for the pattern conditions the two halves of
S-8 already ask for, plus the premise that is inherent, that neither run
blew its budget. Those pattern conditions are the ones listed at the end of
this section — `Wf` and the subject cap — and, for the lockstep side,
eligibility.

That budget premise is what the inventory means by sufficient budgets, and
`matchers_agree_sufficient` discharges it from certificates rather than
assuming it — no hypothesis of that theorem mentions how a run ended. The
lockstep side needs only its accepted certificate, since its sufficiency
covers every program the checker admits. The backtracking side used to be
the one that narrowed the statement, because its sufficiency was proved for
the programs BOUNDS.md sections 4.1 to 4.3 cover and the discharged form was
the intersection of that class with eligibility — the patterns whose every
reachable quantifier stops at one and which reach no `\R`. Section 4.4
closed, so it does not narrow anything now: the discharged form holds for
every Pike-eligible pattern, which is what the inventory says. Not one of its
hypotheses mentions the bytecode — they are the premises the two halves of
S-8 already ask for, `Wf`, `PatFits`, `Covered` and the subject cap, plus
eligibility, the two certificates and the caller's own limits. `ReRules` is
discharged from the pattern by `compile_reRules` rather than asserted.

The widening is not theoretical. `a*b*`, `(a|b)*c` and every other eligible
pattern with a star in it were outside the old statement and are inside this
one; the intersection had been almost exactly the optional items.
Eligibility itself is unchanged as a predicate and is still a real
restriction, though the lowering moved which patterns meet it: `a{2,5}b`
compiles to copies and a star now and is inside S-12, while `a+\R` and
`(?:a?)+b` are outside it for the reason bounded quantifiers used to be —
there is no second run to agree with. Their backtracking bounds are proved.

The backtracking half of R-6, R-7, R-8, R-9's no-allocation clause and S-10
was for a long time proved only for the patterns whose constructs are
groups, alternations and optional items — BOUNDS.md sections 4.1, 4.2 and
4.3. Counted repetitions, section 4.4, are the rest of it, and they are
proved now.

What was between the two ends was a pricing. A counted repetition's control
flow is a loop, but its *price* is a
closed form: `repLeft ways each base k`, read at the number of passes the
head still has left, turns the head into a leaf of the walk rather than a
way back into the body. Every other edge then goes forward, so the whole
pricing is `costAt` with the counters carried along and `code.size` is
enough fuel — no measure, no well-founded recursion, and none of the
lexicographic word the earlier note at the end of `Proofs/BtBounds.lean`
expected to need.

The pass count is where the subject enters, and it enters once. Bounded, it
is the counter value the head's own test leaves at. Unbounded, the head
never leaves by its counter and the empty-match rule stops it instead, so
what is left is the unmet part of the minimum plus one pass per byte still
ahead. One more than that number, at the counter a `RepZero` leaves behind,
is at most the checker's `repPasses` — equal to it at the start of a subject
and smaller further in — and covering `repPasses` is exactly what the
checker's flow does. The two halves of section 4.4 meet there rather than by
construction.

`Proofs/RepBounds.lean` is that walk — `repCostAt` with its fuel argument,
the reading that a `Save` naming a capture slot is invisible to it, and the
reading that the price never rises as the cursor moves forward.
`Proofs/RepShape.lean` is what the walk needs of the code, with the
optional-item hypothesis dropped: every repetition opcode sits inside the
range its own record names, and a walk that has left a repetition never
reads its counter again. `repLeft_dom` and `repRegion_dom` in
`Proofs/BtBounds.lean` now charge `A + (1 + w) * X` per pass rather than
`A + X`, because a pass leaves the region `1 + w` times — once at the head
when the count is spent, once per way the body found to finish — which is
what BOUNDS.md's `outs = S * (1 + w)` says and what the old shape was too
rigid to state.

The join is `Proofs/RepFlow.lean` and `Proofs/RepPriced.lean`. The first is
`RegFlow` over the walk: every clause is definitional except the head's, and
the head's needs what one pass through the body charges, which is the region
tree's business rather than one instruction's. The second is that tree
induction, `region_priced` generalized off `flowCost`, which discharges it and
delivers the root's claim at the same time. `Proofs/RepOnce.lean` supplies the
one fact the two numbers per repetition rest on — that a repetition index
names one region and not two — and `Proofs/RepRun.lean` carries the family
through to the theorems the inventory names, with the optional-item
hypothesis gone.

Three things about that construction are worth keeping. The counter never
wraps, and what rules it out is the head's own maximum test rather than
anything about the run's history: the recurrence is only unfolded on the arm
where the head enters the body, and unbounded, the maximum it tests against is
the sentinel, which is the largest value a counter can hold. The price walk
has to be stepped alongside the *shape* walk rather than composed with the
price walk alone, because a counted region's body runs to one short of its own
end and only the shape walk refuses a child that runs past it. And the span
composition had to be restated with its per-instruction hypothesis guarded by
what a span actually admits, since a nested repetition's head sits inside the
range and is priced by a closed form rather than by one more than the next
point.

The Pike configuration is further along, because its accounting is a
closed form rather than a composition: R-6, R-7, R-8 and S-10 hold there
against any certificate the checker accepted, on every program the checker
admits and at every start offset — no class restriction and nothing like
`AttemptsWithin`. The lockstep call through a preallocated context is
covered too: `pikeRun_inBudget_ctx` holds at any starting scratch the
growth schedule admits — `Rooms re init`, every capacity inside the
schedule's own answer at its array's entry bound, which is what creation
reserves — and the `{}` call is its instance. R-9's no-allocation clause
has a lockstep counterpart as well: `pikeRun_no_growth` says a call handed
the six arrays already at the schedule's final capacities allocates
nothing, `pikeLoop_no_growth` is the capacity reading underneath it, and
neither mentions the caller's limits. What the two context statements
conclude is that shape rather than an allocation event: the call reports the
reservation creation took, and underneath it the core's own memory reading
never passes its setup, which is what "no growth step was reached" comes to
in an account that weighs capacities. They are about the calls a context
admits; one over a cap is BadInput and never reaches a core at all. And they
are about a context call and not about a plain one, which is not a gap but
the clause itself: a plain call starts on empty scratch and grows it, which
is what the growth schedule is for and what R-6 and R-8 price. What R-9 says
is that paying for the scratch once, at creation, buys a call that never
pays again. `Reserved.ofRoom` is where those
capacities meet `pike_room`, so the ceiling the two theorems ask for is the
one creation weighs and not a number invented for them.

S-11 is what those meet in. `ctx_sufficient` used to take the core's own
sufficiency as a premise and nothing supplied it; it now assumes nothing
about how a run ends. What it asks for instead is what a caller can check —
creation succeeded, the subject is admitted, and the per-call cost and
stack sit at or above what the accessors answered at the caller's own
subject length — together with what the two cores need of the program.
`ctx_created_caps` is the bridge that was missing: `ctx_create` sizes every
array from the selected certificate and nothing read those capacities back.
The backtracking path carries the compiler rules of this section and nothing
else, and it carries one more of them than the plain call does — a
`CompiledPat` is whatever creation was handed, so nothing in its type ties
it to compiler output, and the register-file rule cannot be discharged the
way it can for `Ref.compile p`.

Getting there cost two changes to the backtracking account, and both are
worth recording because they were hidden by the plain call rather than
absent from it. The first is that `Within` was reading one pair of numbers
two ways at once: as the certificate's claims, which is what the depth line
and the replay charge are about, and as the arrays' capacities, which is
what the rooms and the scratch are about. A plain call starts empty and the
two coincide; a context reserves at its declared maximum and is called at a
shorter subject, and then they do not. They are separate parameters now.

The second is subtler. Weakening the memory line from an equation to an
inequality is enough for sufficiency, but the equation was load-bearing
somewhere else: what rules out the growth schedule clamping at an array's
declared maximum is a *lower* bound on the meter, and a preallocated call
has no such bound — its meter honestly does not account for scratch it did
not buy. So the account carries what the caller arrived with, and the
no-clamp step has two arms: a plain call, where nothing was carried and the
old argument stands, and a preallocated one, where the memory limit itself
rules the maxima out because the schedule's factor and the allocation
ceiling separate exactly.

S-10's Pike half reads the same per-position account over the
charges a run *attempts* rather than the ones it completes, since a refusal
on this path is exactly a pre-charge test failing; `pikeRun_inBudget` is
the statement, and it asks for the cost and memory limits only, the stack
limit having nothing to refuse. What that half reads the program through is
`ReWf`, four clauses — a non-empty program whose jump and fork targets are
in range, and sizes inside the declared maxima — and
`Proofs/ReWfCompile.lean` now derives all four from `Ref.compile`. The
first two hold of the compiled form of every covered tree. The other two
cannot: `Ref.compile` has no size guard, faithfully, since the engine's
codegen refusals are unreachable for parser output, so the maxima are
properties of the pattern and travel as `PatFits` — the parser's own
MAX_NODES and MAX_GROUPS, restated over the tree. `compile_reWf` is the
theorem, and the four bounds are restated over `Ref.compile p` beneath it.

Five things found while proving the resource bounds are worth recording,
because they are about the engine rather than about the Lean. The first: `cert_shape` never
asks whether a
program contains an `Accept`, and a straight-line region of tests without
one walks off the end of its own code. The two layers part company there:
TIR's checked indexing traps (TIR-SPEC.md T-01) while the Lean reference
reads a default instruction, so the per-attempt bound is false in the model
for such a program. No pattern can produce one — `generate` always emits the
trailing `Accept` — and the bound theorems carry its existence as an
explicit hypothesis rather than assume it away. Whether the checker should
refuse a program without an `Accept` is a BOUNDS.md question, and moving it
would move the frozen artifact, so it is written down here instead.

The second is the same shape. `cert_shape` pins a counted repetition's four
opcodes and its three offsets, but it leaves a `Save`'s slot free — and a
program whose `Save` named a counter register would move that counter with
no `RepZero` or `RepNext` to account for it, which breaks both the pass
count of BOUNDS.md section 4.4 and the measure the proof of that section
descends on. The rule that settles it is that a `Save`'s slot sits below
`novec`, which the compiler guarantees, since it emits one only for a
numbered group. Like the `Accept`, it is a rule the checker could have and
has not, and it is written down rather than added, for the same reason.

The third turned up in section 4.4's pricing and is the same shape again.
A repetition's counter is a `UInt32`, and the pricing reads it as a number:
the recurrence at the head needs the successor of that reading to be its
successor, and a counter at the sentinel would wrap to zero, which is priced
for *more* passes than the value before it. What rules that out is the head's
own maximum test rather than anything about the run's history — the
recurrence is only ever unfolded on the arm where the head enters the body,
and that arm is guarded by the counter being below the minimum or below the
maximum. Unbounded, the maximum *is* the sentinel, which is the largest value
a counter can hold, so the head leaves before a wrap can happen. All that is
left is that a repetition's two declared bounds are themselves counter
values, which the compiler guarantees and `cert_shape` does not ask, so it
travels as a hypothesis beside the other two.

The fourth and the fifth came out of finishing that pricing. `cert_check`
never mentions `re.nregs`, so nothing says a program's register file has room
for the counters its own repetitions name; a `RepEnter` with nowhere to write
would leave the position it remembers unset, the empty-match rule would never
fire, and an unbounded repetition would count without ever spending a byte.
`Ref.compile` sizes the file so it holds with equality, so no pattern can
produce one. And `cert_shape` bounds the region count nowhere, while the
region tree is walked through child and sibling arrays that use `none32` as
their empty marker — so a region at index `none32` files itself as absent from
its parent's child list and is invisible to every walk. A program with two
counted repetitions over one range, hidden that way, would have the analyzer's
two numbers read off whichever region the walk happened to meet. In the engine
the index is a `u32` and the sentinel is not an index; in the Lean reference
it is a `Nat`, so the bound travels as a hypothesis.

All of them are rules the checker could have and has not, and they travel
together as `ReRules` — beside `ReWf`, which is what the lockstep bound reads
a program through, and for the same reason. None of them narrows what a
pattern may be: each is a property of the compiler's output rather than a
condition on the source.

All six are proved of `Ref.compile` in `Proofs/RepCompile.lean`, from the
three conditions the refinement theorems already ask of a pattern — `Wf`,
`Covered` and `PatFits`. `compile_ends` was the last, and it wanted one more
walk of the region table carrying three clauses: the table is non-empty, its
head is the root, and every alternation and repeat region in it closes at or
before the code emitted so far. The root is exempt not because it is the root
but because `compile` closes it after the trailing `Accept`, which is the one
emission that happens with every other region already shut.

A context call carries all six anyway, `Ref.compile` or not, because
`ctx_create` takes whatever `CompiledPat` it is handed and nothing in that
type says the thing came out of the compiler. Closing that is not another
walk over the compiler; it wants an invariant on `CompiledPat` that does not
exist.

The refinement theorems quantify over patterns satisfying `Wf`, which names
the three shapes a parse never emits: an alternation with no branches, a
quantifier bound past spec.py's MAX_QUANT, and a capture slot outside the
ovector window. Until M10 proves the parser that is a claim to be tested
rather than assumed, so `Proofs/WfDecide.lean` decides it and the corpus
replay asks it of every tree the engine's own parser produced, along with
the `PatFits` size clauses the lockstep bounds read the program through.
All 331 replayed patterns satisfy both.

Those two, with the subject cap, are the whole list. There used to be a
third, `suffFuel s.size p.root < none32`, and it was an overclaim in the
other direction: it kept a repetition's counter register faithful to the
count the specification threads, but it read that need off the whole
search's fuel, which adds across sibling repetitions. `a*b*` — a
parser-produced, `Wf`, Pike-eligible pattern — puts `suffFuel` past the
sentinel at the longest subject DESIGN.md section 2.4 admits, so the
theorems were quietly excluding part of the domain they advertised.

What a counter needs is a bound per repetition, and that is now
`Spec.repCap`: the largest count any single repetition in the tree can
reach, a maximum over the tree rather than a sum. A bounded repetition
stops entering at `max lo hi`, and an unbounded one is stopped by the
empty-match rule, which makes every round past the minimum eat a byte —
so nothing counts higher than `lo` plus the subject's length, plus the one
the ended round takes with it. `Wf.repCap_lt` discharges it outright:
MAX_QUANT is 65535 and a subject stops at `2 ^ 31 - 1`, so the worst any
counter can reach is about `2 ^ 31`, half of what a `UInt32` holds. Both
caps are load-bearing there, the quantifier one and the subject one, since
an unbounded repetition counts one per byte. The premise is gone from the
statements rather than weakened in them, and `a*b*` at any admissible
length is back inside S-8 and S-12 where it belongs.

## 6. Where the quantifier lowering sits, and what proving it would cost

PLAN-POST-M6.md changes what the compiler emits for a counted repetition, and
it asks for the price of replaying M6 against the new artifact before the
first line of it is written rather than after. This section is that price and
the decision it led to.

The lowering is a function on the AST: a counted repetition that is not
already an optional, a singleton or a pure star becomes copies of its body
followed by either a pure star or a chain of one-split optionals. Every node
it generates is one the emitter already compiles, so the rewrite could sit on
either side of `R.compile` — ahead of it, in the step from pattern text to
tree, or inside it.

It sits ahead of it. `Ref.compile` is the emission half of the compiler
restated and it compiles the tree it is handed; `gen/lean/bridge.json` hands
it the tree the code generator really walked, which for a lowered pattern is
the lowered one. That puts the rewrite inside the pattern-text-to-AST link
section 4 already declares tested rather than proved, and it widens that link
by exactly one transformation. Section 4 says so.

What the link is tested by is not weak. `lake exe corpuscheck` compiles the
exported tree with `R.compile`, runs it with `R.run`, and holds the bytecode,
the region tree, the outcome, the ovector and the observed cost, stack and
memory to the engine's numbers, case by case — 331 replayed cases, every one
of them well formed for the refinement theorems. Beside it, the differential
sweep compares 51,198 answers to pcre2 with full ovector equality and 41,043
of them across both matchers. A rewrite that disagreed with the compiler by
one instruction, or with pcre2 by one capture, fails a build.

So every theorem of sections 2 and 3 holds unchanged, of the trees it is
given. What changes is coverage rather than statement, and it changes in one
direction: S-12 is quantified over Pike-eligible patterns, and the lowering
makes 116 more of the 334 patterns the corpora pin eligible, none fewer.

    +---------------+------------------------+-------------------------------+
    | obligation    | dependence             | what the replay cost          |
    +---------------+------------------------+-------------------------------+
    | S-1 .. S-12   | none                   | the trees moved, the theorems |
    |               |                        | did not; S-12 covers more     |
    | R-1 .. R-9    | none                   | `R.compile` compiles what it  |
    |               |                        | is handed, as before          |
    | R-10          | numeric                | rerun against the regenerated |
    |               |                        | corpora, 0 disagreements      |
    +---------------+------------------------+-------------------------------+

The alternative — moving the rewrite inside `R.compile` — was priced here
and is now half done, as M7's prelude. It wanted four things; the first and
the third are proved, `Covered` by derivation rather than by a preservation
lemma of its own, and what they came to is recorded after the list.

- `Matches (lower a) = Matches a`, for a tree the lowering is sound on: that
  the lowered tree matches the same strings with the same captures in the
  same preference order. A theorem
  about the specification alone, with no VM and no certificate in it, and the
  one that carries the whole claim. The shape is settled — `x{m,n}` at count
  k is the optional chain at `n - k`, and past the minimum an unbounded
  repetition's count stops mattering — and the fuel side is an implication
  rather than an equation, since the lowered form spends no fuel on a bounded
  quantifier.
- A replacement for the per-node size invariant. `ReWfCompile.lean` bounds
  the emitted program at four cells per arena node, and the lowering breaks
  that by design; what replaces it is the compiler's dry run, so the counting
  theorem has to be restated over the lowered sizes rather than over
  `nodeCount`. Roughly the same size as the one it replaces.
- Preservation lemmas, all structural and all small: `WfAst`, `CapsBelow`,
  `Covered`, `maxGroup`, and `crWalk` for the bumpalong bit.
- The definitional follow-through in `Ref/Compile.lean`, `RepCompile.lean`
  and the two refinement files, which is mechanical once the above exist.

What is proved, as of M7's gate 0:

    +------+----------------------------------------------------------------+
    | L-1  | `Spec.lower`, `Nullable` and `LowerSafe`: the rewrite as a     |
    |      | function on `Ast`, transcribed from `lowered.py`, with the     |
    |      | condition under which it preserves the search. That condition  |
    |      | is the proof's, not the engine's: the engine also refuses a    |
    |      | pattern holding \R, declines when nothing needs unrolling,     |
    |      | and falls back when the unrolled form would not fit. None of   |
    |      | those change what the rewrite means.                           |
    +------+----------------------------------------------------------------+
    | L-2  | `lower_searchEq`: a tree and its lowered form return the same  |
    |      | ordered thread list, end positions and capture registers       |
    |      | alike, from every position. `Matches_lower` lifts it to the    |
    |      | public answer. The fuel side is an implication, each tree      |
    |      | reading the search at its own sufficient fuel.                 |
    +------+----------------------------------------------------------------+
    | L-2a | the bounded splice, `evRep_bounded` and its tail: a finite     |
    |      | induction needing no semantic hypothesis. `x{5,2}` works out   |
    |      | too, since the count reaches the minimum before the high       |
    |      | stops it.                                                      |
    +------+----------------------------------------------------------------+
    | L-2b | the unbounded splice, `evRep_unbounded`, over                  |
    |      | `searchRep_count_free`: past the minimum the count is read in  |
    |      | two places and both have stopped caring, so the tail can be a  |
    |      | star whose count restarts at zero. It is also where the body   |
    |      | has to consume, which is `LB_NULLABLE`'s semantic reason.      |
    +------+----------------------------------------------------------------+
    | L-3  | `maxGroup_lower`, `crWalk_lower`, `wfAst_lower`,               |
    |      | `capsBelow_lower`, gathered at the pattern as `wf_lowered`.    |
    |      | `Covered` is `covered_lower`, which reads it off `WfAst`       |
    |      | rather than preserving it structurally: nothing asks           |
    |      | `Covered` of a tree that is not well formed.                   |
    +------+----------------------------------------------------------------+

L-4 and L-5 are outstanding, which is why section 4 still calls the lowering
part of the tested link: the theorems exist, and the pipeline does not use
them yet.

Nothing in that list is a research question, and none of it blocks the
guarantee being stated honestly with the carve-outs in place. It is the piece
of this plan that was deliberately deferred, and this is where it is written
down.
