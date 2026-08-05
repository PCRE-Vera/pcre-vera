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
    | the artifact sha256      | 6a6dfaddef328fdb85950946041356ab3a55a766 |
    |                          | 835ab415dc7d764d02569451                 |
    | the commit               | the one tagged wave1-frozen              |
    | the pcre2 version        | 10.47                                    |
    | the pcre2 tarball sha256 | 47fe8c99461250d42f89e6e8fdaeba9da057855d |
    |                          | 06eb7fc08d9ca03fd08d7bc7                 |
    | the pin file             | oracle/pcre2-pin.toml                    |
    | the pin sha256           | 297b9f5d284069196d340c9e14adba54ea7bbe4f |
    |                          | fc2d89897dbe27c48d130e1a                 |
    +--------------------------+------------------------------------------+

The corpora the artifact is held to, by content hash:

    +--------------------------------------+------------------------------------------+
    | oracle/corpus/wave1.json             | 0c5ff7d00d40d43ecd4e27b436c5aab0bdac20ae |
    |                                      | 840ca1aca7676e310f1368a5                 |
    | oracle/corpus/sweep-regressions.json | 815d58542aba14629d859b0f9978627c3293d3ee |
    |                                      | ddba3c0fc4e2b367a9f954bf                 |
    | conformance/corpus.json              | 97c8affaa99d062e423837192adf702c000cc1cf |
    |                                      | c5de7967fb754eb17683c26c                 |
    | conformance/certificates.json        | db318a71e6b23bc2f0f3c119bb1f5fc806f61ba0 |
    |                                      | c7867de084944d8f1966c58d                 |
    | conformance/lowering.json            | 88f537fcd39b5c718b12167fdbdc85e9782383eb |
    |                                      | 872dc432b7637ad9ac369748                 |
    | conformance/sweep.json               | 7f3a0cb28cca6857c642b7f7ffd7a99e27c02339 |
    |                                      | 834ad108e54443d64eb39f3a                 |
    +--------------------------------------+------------------------------------------+

And the campaign that closed M5, which is reproducible rather than kept:

    make sweep SWEEP="--seed 20260803 --structured 2000 --hostile 400 \
        --subjects 32 --jobs 8 --out tmp/sweep-m5"

    manifest sha256
      348c195ed6fe84f54137e79cceefff79595e3ad5e4b71d9accc19241971feac5

The LOG entry for M5 carries its counts. A rerun of that command on this
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
    |      | matchers               | btRun_refines_matches;               |
    |      |                        | Proofs/PikeRefine.lean,              |
    |      |                        | pikeRun_refines_matches; the Exec    |
    |      |                        | wrappers in Proofs/ExecBacktrack.lean|
    |      |                        | and Proofs/ExecPike.lean             |
    | S-9  | proved                 | Proofs/Monotone.lean, exec_monotone  |
    | S-10 | proved for the         | Proofs/BtBounds.lean,                |
    |      | backtracking half on   | btRun_inBudget_forward;              |
    |      | one class of programs; | Proofs/PikeBounds.lean,              |
    |      | proved for the Pike    | pikeRun_inBudget                     |
    |      | half                   |                                      |
    | S-11 | proved from the        | Proofs/CtxSufficient.lean            |
    |      | plain-call premise     |                                      |
    | S-12 | proved; both S-8       | Proofs/ExecRefine.lean,              |
    |      | premises now           | matchers_agree; Proofs/ExecPike.lean,|
    |      | discharged             | matchers_agree_wf                    |
    +------+------------------------+--------------------------------------+

    +------+------------------------+--------------------------------------+
    | R-1  | proved                 | Ref/Compile.lean                     |
    | R-2  | proved                 | Ref/VM.lean, Ref/Pike.lean           |
    | R-3  | proved                 | Ref/Context.lean                     |
    | R-4  | proved                 | Ref/Exec.lean                        |
    | R-5  | proved                 | Proofs/BtTermination.lean,           |
    |      |                        | Proofs/PikeTermination.lean          |
    | R-6  | proved for one class   | Proofs/BtBounds.lean,                |
    |      | backtracking; proved   | btRun_cost_le_forward;               |
    |      | for the Pike half      | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_cost_le_check                |
    | R-7  | proved                 | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_stack_le;                    |
    |      |                        | Proofs/BtBounds.lean,                |
    |      |                        | btRun_stack_le_forward               |
    | R-8  | proved for one class   | Proofs/BtBounds.lean,                |
    |      | backtracking; proved   | btRun_mem_le_forward;                |
    |      | for the Pike half      | Proofs/PikeBounds.lean,              |
    |      |                        | pikeRun_mem_le_check                 |
    | R-9  | creation proved; the   | Proofs/CtxReserve.lean,              |
    |      | no-allocation half     | ctx_resident_eq_reservation;         |
    |      | for one class          | Proofs/BtBounds.lean,                |
    |      |                        | btRun_no_growth_forward              |
    | R-10 | proved by running      | lean/CorpusCheck.lean                |
    +------+------------------------+--------------------------------------+

Five of those entries carry a qualifier the inventory does not — S-10,
S-11, R-6, R-8 and R-9 — and the narrowing is the point of writing this
section at all.

S-8 is proved for both matchers, at every start offset and under every
combination of match options. The backtracking half covers every wave 1
construct — literals, classes, the dot, `\R`, every anchor, groups,
alternation and every quantifier. The lockstep half is stated over the same
patterns but carries one side condition the other does not: the program is
eligible. That is the hypothesis `(compile p).pike = true`, and it is a real
restriction rather than a formality — `pike_ok` refuses `\R`, every bounded
quantifier, and any star whose body can finish an iteration without
consuming. It sits in the statement rather than in the conclusion because an
ineligible program is one the matcher declines at the door, for a reason the
specification has no opinion about. The argument is four layers deep — the
epsilon closure against the backtracking mirror, one position's thread list
against the merge of the attempts still running, one position's seed, and
the position loop against `Spec.scan` — and the middle layers are where the
lockstep matcher earns what it does differently: a built list is several
attempts side by side in leftmost order, and its visited set deduplicates
across them.

S-12 is proved as the corollary DESIGN.md section 6 says it is — two runs
refining the same specification and both completing answer the same thing.
Both of its refinement premises are now discharged rather than assumed:
`matchers_agree_wf` asks only for the pattern conditions the two halves of
S-8 already ask for, plus the premise that was always inherent, that neither
run blew its budget. Those pattern conditions are the ones listed at the end
of this section — `Wf`, the subject cap, the counter-wrap bound — and, for
the lockstep side, eligibility.

The backtracking half of R-6, R-7, R-8, R-9's no-allocation clause and S-10
is proved outright for every pattern whose constructs are groups,
alternations and optional items — BOUNDS.md sections 4.1, 4.2 and 4.3 — at
any nesting depth. Counted repetitions, section 4.4, are open, and for them
the family is proved conditional on one hypothesis, `AttemptsWithin`, which
is that section's composition read against the VM's own pushes. The reason
4.4 is a step rather than another case is written down at the end of
`Proofs/BtBounds.lean`: the pricing that carries the other three is a
function of the program point, and a counted repetition's tail jumps
backwards, so the pricing has to gain a counter index and the stack's
weights stop being pointwise. Everything else that half needs is done —
the section 5 whole-call arithmetic, the growth schedule, the checker's
tree facts and per-region dominance, the fork account, the charge
sites priced against a claim, and both ends of 4.4 itself: the run side
takes the four repetition opcodes as they come, and `scanRepeat_counted`
reads the checker's counted arm back to that section's four equations. What
is between them is the pricing, and `repRegion_dom` is the statement it has
to satisfy.

The Pike configuration is further along, because its accounting is a
closed form rather than a composition: R-6, R-7, R-8 and S-10 hold there
against any certificate the checker accepted, on every program the checker
admits and at every start offset — no class restriction and nothing like
`AttemptsWithin`. S-10's half reads the same per-position account over the
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

Two things found while proving R-6 are worth recording, because they are
about the engine rather than about the Lean. The first: `cert_shape` never
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

The refinement theorems quantify over patterns satisfying `Wf`, which names
the three shapes a parse never emits: an alternation with no branches, a
quantifier bound sitting on the u32 sentinel, and a capture slot outside the
ovector window. Until M10 proves the parser that is a claim to be tested
rather than assumed, so `Proofs/WfDecide.lean` decides it and the corpus
replay asks it of every tree the engine's own parser produced. All 248
replayed patterns satisfy it.
