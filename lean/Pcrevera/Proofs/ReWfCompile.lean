import Pcrevera.Proofs.PikeRefine

/-!
# `ReWf` for compiler output

`PikeBounds.lean` proves R-6, R-7, R-8 and S-10 for the lockstep
configuration against any certificate the checker accepted, and it does so
under one standing assumption: `ReWf re`, the program-shape predicate. This
file discharges that assumption for everything `Ref.compile` can produce, so
the four results become facts about every pattern the engine can compile
rather than facts about programs nobody has exhibited.

`ReWf` has four clauses, and they do not all cost the same.

`sized` and `targets` are unconditional — they hold of the compiled form of
every covered tree. The first is immediate: `compile` always closes with an
`accept`. The second is the substantial one, and it is a composition rather
than a new induction. `Refine.lean`'s fragment relation already says where a
construct's compiled form sits, `FragAt.targets` already says such a form
never spells an address outside its own range, and `compile_shape` already
covers the whole program with the root's fragment. What is left is the
difference between the two successor readings — the closure's
`hollowTargets`, which the fragment theorem is stated against, and
`pikeTargets`, which is what the matcher actually follows — plus the
`eod?`/`accept` tail the root fragment does not reach.

`coded` and `slots` are *not* facts about arbitrary compiler output.
`Ref.compile` has no size guard of its own, which is faithful: the engine's
`PatternTooLarge` checks during codegen are unreachable for parser output
because `spec.py` sizes MAX_CODE above what MAX_NODES can generate. So the
two maxima are properties of the pattern, and they arrive here as `PatFits`,
which restates the parser's own two refusals — MAX_NODES on the arena and
MAX_GROUPS on the capture count — in the vocabulary the compiler speaks.
`nodeCount` is the arena measure, and the whole of that half is the one
counting theorem `compileNode_size`: a construct emits at most four
instructions per node, and two fewer than that, which is exactly the slack
the alternation chain's per-branch split and jump need.

`compile_reWf` puts the four together, and the section at the end restates
the Pike results for `Ref.compile p` with the hypothesis gone.
-/

open private emit patch openRegion closeRegion dropEmptyRegion from
  Pcrevera.Ref.Compile

/- The compiler's emitters are private to `Compile.lean`, and the closed
form of each compound construct is private to `Refine.lean`. Both are
borrowed rather than restated: the counting theorem below is the same
walk over the same four constructs, and it should read against the same
terms the fragment theorem reads against. -/
open private rootSt altSplitSt altBranchSt altMid altOut compileAlt_nil_eq
  compileAlt_cons_eq patchAll_facts grpSt compileNode_grp_pos
  compileNode_grp_zero repOptSt compileNode_repOpt_eq repGenSt repGenOut
  compileNode_repGen_eq compileNode_assn from Pcrevera.Proofs.Refine

namespace Pcrevera.Refine

open Pcrevera Pcrevera.Ref

/-! ## How much code a tree compiles to

The engine's parser refuses a pattern whose arena passes MAX_NODES, and
`spec.py` sets MAX_CODE at `4 * MAX_NODES + 16` for one reason: no tree that
survived the first refusal can generate that much code. `nodeCount` is the
arena measure and `compileNode_size` is that reason, proved.

The bound carries two cells of slack — `emitted + 2 ≤ 4 * nodeCount` — and
the slack is not decoration. An alternation pays a split and a jump per
branch but the last, and the four cells its own node buys are what covers
them; a counted repetition spends its four exactly. -/

mutual

/-- Arena nodes: one per tree node, the count the parser's MAX_NODES
refusal is stated against. -/
def nodeCount : Ast → Nat
  | .cat kids => 1 + nodeCountList kids
  | .alt arms => 1 + nodeCountList arms
  | .grp _ body => 1 + nodeCount body
  | .rep _ _ _ body => 1 + nodeCount body
  | _ => 1

/-- A list of children, one after the other. The list itself is not a node
— the `cat` or `alt` that owns it is. -/
def nodeCountList : List Ast → Nat
  | [] => 0
  | a :: rest => nodeCount a + nodeCountList rest

end

/-- Every node counts, the ones that compile to nothing included — `nul`
and a `{0}` repetition still passed through the parser's arena. -/
theorem nodeCount_pos (a : Ast) : 0 < nodeCount a := by
  cases a <;> simp only [nodeCount] <;> omega

/-- A list's nodes, one child at a time, which is how the counting theorem
walks a concatenation and an alternation alike. -/
theorem nodeCount_cat_cons (k : Ast) (kids : List Ast) :
    nodeCount (.cat (k :: kids)) = nodeCount k + nodeCount (.cat kids) := by
  rw [nodeCount, nodeCount, nodeCountList]
  omega

theorem nodeCount_alt_cons (a : Ast) (arms : List Ast) :
    nodeCount (.alt (a :: arms)) = nodeCount a + nodeCount (.alt arms) := by
  rw [nodeCount, nodeCount, nodeCountList]
  omega

/-! ### What the emitters cost

Four one-line facts about the state helpers, all of them saying the same
thing: only `emit` lengthens the code, and everything else is region and
table bookkeeping. -/

private theorem emit_size (st : CState) (i : Inst) :
    (emit st i).1.code.size = st.code.size + 1 := by
  simp [emit]

private theorem close_size (st : CState) (at_ : Nat) :
    (closeRegion st at_).code.size = st.code.size := rfl

private theorem finish_size (st : CState) (at_ : Nat) :
    (dropEmptyRegion (closeRegion st at_) at_).code.size = st.code.size := by
  rw [dropEmptyRegion]
  split
  · split <;> rfl
  · rfl

private theorem branch_size (inside : Nat) (st : CState) :
    (altBranchSt inside st).code.size = st.code.size := rfl

private theorem split_size (st : CState) :
    (altSplitSt st).code.size = st.code.size + 1 := by
  simp [altSplitSt]

private theorem patch_size (st : CState) (pc : Nat) (f : Inst → Inst) :
    (patch st pc f).code.size = st.code.size := by
  simp [patch]

private theorem out_size (arm : Ast) (inside : Nat) (st : CState) :
    (altOut arm inside st).code.size =
      (altMid arm inside st).code.size + 1 := by
  simp [altOut]

private theorem grp_size (here : Nat) (st : CState) :
    (grpSt here st).code.size = st.code.size := rfl

private theorem repOpt_size (here : Nat) (st : CState) :
    (repOptSt here st).code.size = st.code.size + 1 := by
  simp [repOptSt]

private theorem repGenSt_size (lo' : Nat) (hi : Option Nat) (greedy : Bool)
    (here : Nat) (st : CState) :
    (repGenSt lo' hi greedy here st).code.size = st.code.size + 3 := by
  simp [repGenSt]

private theorem repGenOut_size (r : Nat) (st : CState) :
    (repGenOut r st).code.size = st.code.size + 1 := by
  simp [repGenOut, emit]

/-- The alternation chain, counted. Every branch but the last pays for its
own split and jump out of the four cells its arm's root node buys, so the
chain costs no more than the nodes in it — which is the same accumulator
statement `compileAlt_facts` carries, read on sizes alone. -/
private theorem compileAlt_size {n : Nat}
    (ih : ∀ {a : Ast}, sizeOf a ≤ n → Covered a →
      ∀ (here : Nat) (st : CState),
        (compileNode a here st).code.size + 2 ≤
          st.code.size + 4 * nodeCount a) :
    ∀ (rest : List Ast) (arm : Ast), sizeOf arm ≤ n → Covered arm →
      (∀ x ∈ rest, sizeOf x ≤ n ∧ Covered x) →
      ∀ (inside : Nat) (jumps : Array Nat) (st : CState),
        (compileAlt arm rest inside jumps st).code.size + 2 ≤
          st.code.size + 4 * nodeCount (.alt (arm :: rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro arm hsz hc _ inside jumps st
      have hcode : (compileAlt arm [] inside jumps st).code.size =
          (compileNode arm st.regions.size
            (altBranchSt inside st)).code.size := by
        rw [compileAlt_nil_eq, ← Array.foldl_toList]
        exact (patchAll_facts _ jumps.toList _).1
      have harm := ih hsz hc st.regions.size (altBranchSt inside st)
      rw [branch_size] at harm
      rw [hcode, nodeCount_alt_cons, nodeCount, nodeCountList]
      omega
  | cons next rest' ihrest =>
      intro arm hsz hc helems inside jumps st
      have hnext : sizeOf next ≤ n ∧ Covered next :=
        helems next (by simp)
      have hrest' : ∀ x ∈ rest', sizeOf x ≤ n ∧ Covered x :=
        fun x hx => helems x (by simp [hx])
      have harm := ih hsz hc (altSplitSt st).regions.size
        (altBranchSt inside (altSplitSt st))
      rw [branch_size, split_size] at harm
      have hmid : (compileNode arm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st))).code.size =
          (altMid arm inside st).code.size := rfl
      rw [hmid] at harm
      have htail := ihrest next hnext.1 hnext.2 hrest' inside
        (jumps.push (altMid arm inside st).code.size) (altOut arm inside st)
      rw [out_size] at htail
      rw [compileAlt_cons_eq, nodeCount_alt_cons arm (next :: rest')]
      omega

/-- Compiling a covered node: at most four instructions per node, and two
fewer than that. The induction is `compileNode_facts`'s, over the same
closed forms, with everything but the code length forgotten. -/
theorem compileNode_size :
    ∀ (n : Nat) {a : Ast}, sizeOf a ≤ n → Covered a →
    ∀ (here : Nat) (st : CState),
      (compileNode a here st).code.size + 2 ≤
        st.code.size + 4 * nodeCount a := by
  intro n
  induction n with
  | zero =>
      intro a hsz hc
      exfalso
      cases hc with
      | assn ha => cases a <;> simp [assnOp] at ha ⊢ <;> simp_all
      | _ => simp_all
  | succ n ih =>
      intro a hsz hc here st
      have hpos := nodeCount_pos a
      cases hc with
      | nul =>
          rw [compileNode]
          omega
      | chr b =>
          rw [compileNode, emit_size]
          omega
      | chrCI folded =>
          rw [compileNode, emit_size]
          omega
      | cls bits =>
          rw [compileNode, emit_size]
          show st.code.size + 1 + 2 ≤ _
          omega
      | any =>
          rw [compileNode, emit_size]
          omega
      | anyNoNL =>
          rw [compileNode, emit_size]
          omega
      | bsr =>
          rw [compileNode, emit_size]
          omega
      | assn ha =>
          rw [compileNode_assn ha, emit_size]
          omega
      | catNil =>
          rw [compileNode, compileCat]
          omega
      | @catCons k kids hck hckids =>
          have hszk : sizeOf k ≤ n ∧ sizeOf (Ast.cat kids) ≤ n := by
            simp at hsz ⊢
            omega
          have hunfold : compileNode (Ast.cat kids) here
              (compileNode k here st) =
              compileCat kids here (compileNode k here st) := by
            rw [compileNode]
          have hstep : compileNode (.cat (k :: kids)) here st =
              compileNode (.cat kids) here (compileNode k here st) := by
            rw [compileNode, compileCat, hunfold]
          have h1 := ih hszk.1 hck here st
          have h2 := ih hszk.2 hckids here (compileNode k here st)
          rw [hstep, nodeCount_cat_cons]
          omega
      | @altOne a1 hca =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have hstep : compileNode (.alt [a1]) here st =
              compileNode a1 here st := by
            rw [compileNode]
          have h1 := ih hsza hca here st
          rw [hstep, nodeCount_alt_cons, nodeCount, nodeCountList]
          omega
      | @altCons a1 b rest hca hcrest =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have helems : ∀ x ∈ b :: rest, sizeOf x ≤ n ∧ Covered x := by
            intro x hx
            refine ⟨?_, covered_alt_mem hcrest x hx⟩
            have := List.sizeOf_lt_of_mem hx
            simp at hsz this ⊢
            omega
          have hstep : compileNode (.alt (a1 :: b :: rest)) here st =
              closeRegion
                (compileAlt a1 (b :: rest) st.regions.size #[]
                  { st with regions := (st.regions.push
                      ⟨.alt, here, st.code.size, st.code.size⟩) })
                st.regions.size := by
            rw [compileNode] <;> first | rfl | simp
          have hchain := compileAlt_size (fun h hc => ih h hc) (b :: rest) a1
            hsza hca helems st.regions.size #[]
            { st with regions := (st.regions.push
                ⟨.alt, here, st.code.size, st.code.size⟩) }
          rw [hstep, close_size]
          exact hchain
      | @grp cap body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          by_cases hcap : (cap != 0) = true
          · rw [compileNode_grp_pos body here st hcap, finish_size, emit_size]
            have hopen := emit_size (grpSt here st) ⟨.save, 2 * cap, 0⟩
            rw [grp_size] at hopen
            have hbody := ih hszb hcbody st.regions.size
              (emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1
            rw [hopen] at hbody
            rw [nodeCount]
            omega
          · have hzero : cap = 0 := by
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hcap
              simpa using hcap
            subst hzero
            rw [compileNode_grp_zero body here st, finish_size]
            have hbody := ih hszb hcbody st.regions.size (grpSt here st)
            rw [grp_size] at hbody
            rw [nodeCount]
            omega
      | @repNone lo greedy body =>
          rw [compileNode]
          omega
      | @repOne greedy body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hstep : compileNode (.rep 1 (some 1) greedy body) here st =
              compileNode body here st := by
            rw [compileNode]
            simp
          have hbody := ih hszb hcbody here st
          rw [hstep, nodeCount]
          omega
      | @repOpt lo greedy body hlo hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hlo' : (lo == 1) = false := by simpa using hlo
          rw [compileNode_repOpt_eq greedy body here st hlo', close_size]
          have hbody := ih hszb hcbody st.regions.size (repOptSt here st)
          rw [repOpt_size] at hbody
          rw [patch_size, nodeCount]
          omega
      | @repGen lo hi greedy body hnot0 hnot1 hbound hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          rw [compileNode_repGen_eq greedy body here st hnot0 hnot1,
            close_size, repGenOut_size]
          have hbody := ih hszb hcbody st.regions.size
            (repGenSt lo hi greedy here st)
          rw [repGenSt_size] at hbody
          rw [nodeCount]
          omega

/-! ## Every successor is a real instruction

`FragAt.targets` says a construct's compiled form never spells an address
outside its own range. That is the whole of `ReWf.targets` bar two gaps, and
neither needs an induction of its own.

The first is that the two files read a program's successors differently. The
closure's `hollowTargets` is the non-consuming walk, so a consuming
instruction is a dead end there where the matcher goes on to the next cell,
and a `repNext` offers its deciding head where the matcher offers the body.
The next cell is in range because the pc is not the last (the last is the
`accept`, which defers nowhere), and the body is in range because
`RowOk` puts it one past the head with the block's exit above it — which is
`compile_rows`, already proved.

The second gap is the tail: the root's fragment stops where the root's code
does, and behind it sit the ENDANCHORED assertion and the accept. -/

/-- The lockstep successors, read against the walk the fragment theorem is
stated over: a successor is the next cell, a non-consuming target, or the
block body a `repNext` returns to. -/
theorem mem_pikeTargets {re : Re} {pc t : Nat} (ht : t ∈ pikeTargets re pc) :
    t = pc + 1 ∨ t ∈ hollowTargets re.code re.reps pc ∨
      ((re.code[pc]!).op = Op.repNext ∧
        t = (re.reps[(re.code[pc]!).arg]!).body) := by
  cases hop : (re.code[pc]!).op <;>
    simp only [pikeTargets, hollowTargets, hop, List.mem_cons,
      List.not_mem_nil, or_false] at ht ⊢ <;>
    first
      | exact Or.inl ht
      | exact Or.inr (Or.inl ht)
      | exact Or.inr (Or.inl ht.symm)
      | (rcases ht with h | h
         · exact Or.inr (Or.inr ⟨trivial, h⟩)
         · exact Or.inr (Or.inl (Or.inl h)))

/-- A fragment's cells defer inside it, one past its end included, for the
matcher's reading of a successor as well as the closure's. -/
theorem frag_pikeTargets_le (re : Re) {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt re.code re.classes re.reps r0 a lo hi)
    (hrows : ∀ r, r < re.reps.size → RowOk re.code re.reps r) :
    ∀ pc, lo ≤ pc → pc < hi → ∀ t ∈ pikeTargets re pc, t ≤ hi := by
  intro pc h1 h2 t ht
  rcases mem_pikeTargets ht with rfl | hh | ⟨hop, rfl⟩
  · omega
  · exact (h.targets pc h1 h2 t hh).2
  · by_cases hr : (re.code[pc]!).arg < re.reps.size
    · have hrow := hrows _ hr
      have hafter : (re.reps[(re.code[pc]!).arg]!).after ≤ hi := by
        refine (h.targets pc h1 h2 _ ?_).2
        simp [hollowTargets, hop]
      have hbody := hrow.body
      have hroom := hrow.room
      omega
    · rw [getElem!_neg re.reps _ hr]
      exact Nat.zero_le _

/-- What `compile` leaves behind the root's own code, read as a length. -/
private theorem compile_code_size (p : Pat) :
    (compile p).code.size =
      if p.opts.endanchored then (compileNode p.root 0 rootSt).code.size + 2
      else (compileNode p.root 0 rootSt).code.size + 1 := by
  by_cases hend : p.opts.endanchored = true
  · rw [if_pos hend]
    have hcode : (compile p).code =
        ((compileNode p.root 0 rootSt).code.push ⟨.eod, 0, 0⟩).push
          ⟨.accept, 0, 0⟩ := by
      simp only [compile, hend]
      rfl
    rw [hcode]
    simp
  · rw [if_neg (by simpa using hend)]
    have hcode : (compile p).code =
        (compileNode p.root 0 rootSt).code.push ⟨.accept, 0, 0⟩ := by
      simp only [compile, eq_false_of_ne_true hend]
      rfl
    rw [hcode]
    simp

/-- `ReWf.targets` for a whole compiled pattern, and it costs no
hypothesis: wherever the lockstep matcher can move from a real
instruction, it moves to another real instruction. -/
theorem compile_targets {p : Pat} (hc : Covered p.root) :
    ∀ pc, pc < (compile p).code.size →
      ∀ t ∈ pikeTargets (compile p) pc, t < (compile p).code.size := by
  obtain ⟨hfrag, -, hopen, hanch⟩ := compile_shape hc
  have hsize := compile_code_size p
  intro pc hpc t ht
  rcases Nat.lt_or_ge pc (compileNode p.root 0 rootSt).code.size with hlt | hge
  · have hle := frag_pikeTargets_le (compile p) hfrag
      (fun r hr => compile_rows hc hr) pc (Nat.zero_le _) hlt t ht
    split at hsize <;> omega
  · by_cases hend : p.opts.endanchored = true
    · rw [if_pos hend] at hsize
      rcases Nat.lt_or_ge pc ((compileNode p.root 0 rootSt).code.size + 1)
        with h1 | h1
      · rw [show pc = (compileNode p.root 0 rootSt).code.size from by omega,
          pikeTargets, (hanch hend).1] at ht
        simp only [List.mem_singleton] at ht
        omega
      · rw [show pc = (compileNode p.root 0 rootSt).code.size + 1 from by omega,
          pikeTargets, (hanch hend).2] at ht
        simp at ht
    · rw [if_neg (by simpa using hend)] at hsize
      rw [show pc = (compileNode p.root 0 rootSt).code.size from by omega,
        pikeTargets, hopen (eq_false_of_ne_true hend)] at ht
      simp at ht

/-! ## The two maxima, and `ReWf` in one piece

`Ref.compile` is total on purpose, and `Compile.lean` says why: the
engine's `PatternTooLarge` checks during codegen are unreachable for
parser output, so restating them here would be restating a refusal that
never fires. The maxima are therefore facts about the pattern rather than
about the compiler, and `PatFits` is where they enter. -/

/-- The two pattern-level maxima, stated where the compiler can use them:
an arena inside MAX_NODES, and a capture count the ovector has room for.
Both mirror a refusal the engine's parser already makes — at MAX_NODES
nodes, and at MAX_GROUPS captures, which is 255, one below what an ovector
sized `2 * (MAX_GROUPS + 1)` still holds.

That parser output really satisfies the two is not proved here, and is not
this file's business: it is the parser link M10 closes, with the corpora
holding it in the meantime, like every other fact about parser output in
this development. -/
structure PatFits (p : Pat) : Prop where
  nodes : nodeCount p.root ≤ maxNodes
  groups : p.ncap < 256

/-- A compiled pattern is four cells per node of the tree it came from,
which is the inequality MAX_CODE was sized to make room for. -/
theorem compile_code_size_le {p : Pat} (hc : Covered p.root) :
    (compile p).code.size ≤ 4 * nodeCount p.root := by
  have hroot := compileNode_size (sizeOf p.root) (Nat.le_refl _) hc 0 rootSt
  have hempty : rootSt.code.size = 0 := rfl
  rw [compile_code_size]
  split <;> omega

/-- `ReWf` for compiler output. The first two clauses hold of every covered
tree: `compile` always closes with an `accept`, and the fragment relation
keeps every successor inside the program. The last two are the pattern's
own, and they arrive through `PatFits`. -/
theorem compile_reWf {p : Pat} (hc : Covered p.root) (hp : PatFits p) :
    ReWf (compile p) where
  sized := by
    rw [compile_code_size]
    split <;> omega
  targets := compile_targets hc
  coded := by
    have hsize := compile_code_size_le hc
    have hmax : maxCode = 4 * maxNodes + 16 := rfl
    have hnodes := hp.nodes
    omega
  slots := by
    have hslots : (compile p).novec = 2 * (p.ncap + 1) := rfl
    have hmax : maxOvec = 2 * (255 + 1) := rfl
    have hgroups := hp.groups
    omega

/-- The same against `Wf`, which is the shape hypothesis the refinement
theorems travel under, so that a caller carrying those does not have to
produce `Covered` a second time. The two maxima still come separately —
`Wf` says nothing about size. -/
theorem wf_compile_reWf {p : Pat} (hw : Wf p) (hp : PatFits p) :
    ReWf (compile p) :=
  compile_reWf hw.1.covered hp

/-! ## The lockstep bounds, with the hypothesis discharged

R-6, R-7, R-8 and S-10 for `CfgPike`, stated where a caller meets them: on
the program `Ref.compile` produced, against a certificate the checker
accepted. The proofs are the ones `PikeBounds.lean` gives; what is new is
that nothing is assumed about the program any more.

R-7 is free of even `PatFits` — no backtrack entry exists on this path, so
the stack claim is met whatever was compiled. -/

/-- R-7 for compiled patterns: the stack a lockstep run reports is inside
any bound a certificate names, and neither the tree nor its size has
anything to say about it. -/
theorem compile_pikeRun_stack_le (p : Pat) (s : ByteArray) (start : Nat)
    (mo : MOpts) (lim : Limits) (init : PikeSt) (cert : Cert) (v : Nat)
    (h : certBound cert .stack s.size = ⟨true, v⟩) :
    (pikeRun (compile p) s start mo lim init).usage.stack ≤ v :=
  pikeRun_stack_le _ _ _ _ _ _ _ _ h

/-- R-6 for compiled patterns: the cost of a run is inside what the
checker accepted. -/
theorem compile_pikeRun_cost_le_check {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hc : Covered p.root)
    (hp : PatFits p) (h : pikeCheck (compile p) cert = .crOk) :
    (pikeRun (compile p) s start mo lim {}).usage.cost ≤
      cert.cost.val s.size :=
  pikeRun_cost_le_check (compile_reWf hc hp) h

/-- R-8, the same way: the memory a run peaks at is inside the accepted
claim, and it does not move with the subject. -/
theorem compile_pikeRun_mem_le_check {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hc : Covered p.root)
    (hp : PatFits p) (h : pikeCheck (compile p) cert = .crOk) :
    (pikeRun (compile p) s start mo lim {}).usage.mem ≤ cert.mem.val s.size :=
  pikeRun_mem_le_check (compile_reWf hc hp) h

/-- S-10 for compiled patterns: a caller whose limits sit at or above what
an accepted certificate names never sees ResourceExceeded. -/
theorem compile_pikeRun_inBudget {p : Pat} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert} (hc : Covered p.root)
    (hp : PatFits p) (hstart : start ≤ s.size)
    (h : pikeCheck (compile p) cert = .crOk)
    (hcost : cert.cost.val s.size ≤ lim.cost)
    (hmem : cert.mem.val s.size ≤ lim.mem) :
    (pikeRun (compile p) s start mo lim {}).outcome ≠ .resourceExceeded :=
  pikeRun_inBudget (compile_reWf hc hp) hstart h hcost hmem

end Pcrevera.Refine
