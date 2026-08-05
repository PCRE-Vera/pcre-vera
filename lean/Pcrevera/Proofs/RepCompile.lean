import Pcrevera.Proofs.RepRun
import Pcrevera.Proofs.ReWfCompile

/-!
# `ReRules` read off the compiler (BOUNDS.md section 4.4)

`ReRules` is the list of things the backtracking bounds need of a program and
`certCheck` never asks about. Stated of an arbitrary `Re` they have to be
carried, because an arbitrary `Re` is whatever it is. Stated of what
`Ref.compile` emits they are facts, and this file proves them: five here and
`regs` back in `RepRun.lean`, gathered at the end into `compile_reRules`.

`accept` costs nothing at all — the compiler's last two emissions are the
optional `Eod` and the `Accept`, and `compile_code` already hands back both
spellings of that tail. `saves` is a corollary of `compile_cellsOk`, which
pins every cell a fragment covers and not just the interesting ones. `counts`
and `regions` are two new walks. The first reads a repetition's two declared
bounds off the `FragAt` derivation, where only the minimum costs a hypothesis:
the maximum is either the sentinel itself or a bound the derivation already
carries. The second counts region entries the way `ReWfCompile.lean` counts
code cells, and lands at two regions per node against a parser that stops at
`maxNodes`.

`ends` is the sixth and it is a walk of its own, over the region table rather
than over the code. `Grows`, the per-node invariant the refinement proof
carries, covers the code, the classes and the repetitions and says nothing
about regions, so the invariant is built here from the ground up.
-/

open private emit patch openRegion closeRegion dropEmptyRegion from
  Pcrevera.Ref.Compile
open private getBang_push_lt getBang_push_eq getBang_modify_ne getBang_modify_eq
  from Pcrevera.Proofs.Refine
open private rootSt compile_code attach_foldr_forall altSplitSt altBranchSt
  altMid altOut compileAlt_nil_eq compileAlt_cons_eq grpSt compileNode_grp_pos
  compileNode_grp_zero repOptSt compileNode_repOpt_eq repGenSt repGenOut
  compileNode_repGen_eq compileNode_assn from Pcrevera.Proofs.Refine

namespace Pcrevera.Refine

open Pcrevera Pcrevera.Ref

/-! ## The trailing `Accept` -/

/-- The program the compiler emits ends in an `Accept`, whether or not the
pattern was end-anchored. This one costs nothing: the tail is the last thing
`compile` writes, and the refinement proof already reads it back. -/
theorem compile_accept (p : Pat) :
    ((compile p).code[(compile p).code.size - 1]!).op = .accept := by
  obtain ⟨⟨hopen, hanch⟩, -, -⟩ := compile_code (p := p)
  by_cases hend : p.opts.endanchored = true
  · rw [hanch hend]
    simp [Array.getElem_push]
  · rw [hopen (by simpa using hend)]
    simp [Array.getElem_push]

/-! ## Where a `Save` writes -/

/-- A `Save` the compiler emits names a capture slot, never a counter. The
cell walk of the lockstep refinement pins this already, with a lower bound on
the slot besides, so nothing new is needed here. -/
theorem compile_saves {p : Pat} (hc : Covered p.root)
    (hcaps : CapsBelow (2 * (p.ncap + 1)) p.root) :
    ∀ q, q < (compile p).code.size → ((compile p).code[q]!).op = .save →
      ((compile p).code[q]!).arg < (compile p).novec :=
  fun q _ hq => ((compile_cellsOk hc hcaps).save q hq).2


/-! ## A repetition's two declared bounds

The quantifier bound the parser admits is `MAX_QUANT`, which is well under
what a counter register holds, and the maximum needs no bound at all: it is
either the sentinel or a number the fragment derivation already carries one
for. What the walk below needs of the tree is `WfAst` one node at a time, and
`WfAst` is written as a fold over an attached list, which does not decompose
by `rfl`.
-/

/-- `WfAst` of a concatenation, one kid at a time. -/
theorem wfAst_cat_cons {k : Ast} {kids : List Ast} :
    WfAst (.cat (k :: kids)) ↔ WfAst k ∧ WfAst (.cat kids) := by
  rw [WfAst, WfAst]
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map]

/-- And of an alternation. This one is an implication rather than an
equivalence, because an alternation with no arms is not well formed and the
converse would have to produce one. -/
theorem wfAst_alt_cons {a : Ast} {b : Ast} {arms : List Ast} :
    WfAst (.alt (a :: b :: arms)) → WfAst a ∧ WfAst (.alt (b :: arms)) := by
  intro h
  rw [WfAst] at h
  obtain ⟨-, h⟩ := h
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map] at h
  refine ⟨h.1, ?_⟩
  rw [WfAst]
  refine ⟨by simp, ?_⟩
  simp only [List.attach_cons, List.foldr_cons, List.foldr_map]
  exact h.2

/-- The last arm on its own. -/
theorem wfAst_alt_one {a : Ast} : WfAst (.alt [a]) → WfAst a := by
  intro h
  rw [WfAst] at h
  exact attach_foldr_forall h.2 a (by simp)

/-- Every row a fragment claims holds two numbers a counter register can
take. The minimum is the parser's own quantifier cap; the maximum is either
`none32` itself, for an unbounded repetition, or a value the derivation
carries a bound for. -/
theorem FragAt.repFits {code : Array Inst} {classes : Array UInt8}
    {reps : Array RepInfo} {r0 : Nat} {a : Ast} {lo hi : Nat}
    (h : FragAt code classes reps r0 a lo hi) :
    WfAst a → ∀ r, r0 ≤ r → r < r0 + repCount a →
      (reps[r]!).lo ≤ none32 ∧ (reps[r]!).hi ≤ none32 := by
  induction h with
  | nul | chr _ | chrCI _ | cls _ _ _ | any _ | anyNoNL _ | bsr _ =>
      intro _ r _ hlt
      rw [repCount] at hlt <;> first | omega | simp
  | assn ha _ =>
      intro _ r _ hlt
      rw [repCount_assn ha] at hlt
      omega
  | catNil =>
      intro _ r _ hlt
      rw [repCount_cat_nil] at hlt
      omega
  | @catCons k kids r0 lo mid hi _ _ ihk ihkids =>
      intro hw r hge hlt
      obtain ⟨hwk, hwkids⟩ := wfAst_cat_cons.mp hw
      rw [repCount_cat_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount k) with h1 | h1
      · exact ihk hwk r hge h1
      · exact ihkids hwkids r h1 (by omega)
  | @altOne a r0 lo hi _ iha =>
      intro hw r hge hlt
      rw [repCount_alt_cons, repCount_alt_nil] at hlt
      exact iha (wfAst_alt_one hw) r hge (by omega)
  | @altCons a b rest r0 lo j hi _ _ _ _ iha ihrest =>
      intro hw r hge hlt
      obtain ⟨hwa, hwrest⟩ := wfAst_alt_cons hw
      rw [repCount_alt_cons] at hlt
      rcases Nat.lt_or_ge r (r0 + repCount a) with h1 | h1
      · exact iha hwa r hge h1
      · exact ihrest hwrest r h1 (by omega)
  | grpZero _ ihbody =>
      intro hw r hge hlt
      rw [WfAst] at hw
      rw [repCount] at hlt
      exact ihbody hw r hge hlt
  | grpCap _ _ _ _ ihbody =>
      intro hw r hge hlt
      rw [WfAst] at hw
      rw [repCount] at hlt
      exact ihbody hw r hge hlt
  | repNone =>
      intro _ r _ hlt
      rw [repCount] at hlt
      omega
  | repOne _ ihbody =>
      intro hw r hge hlt
      rw [WfAst] at hw
      rw [repCount] at hlt
      exact ihbody hw.2 r hge hlt
  | repOpt _ _ _ ihbody =>
      intro hw r hge hlt
      rw [WfAst] at hw
      rw [repCount] at hlt
      exact ihbody hw.2 r hge hlt
  | @repGen lo' hi' greedy body r0 pc j _ _ _ _ _ hinfo
      hbound hnot0 hnot1 hbody ihbody =>
      intro hw r hge hlt
      rw [WfAst] at hw
      have hcount : repCount (.rep lo' hi' greedy body) = 1 + repCount body := by
        cases hi' with
        | none => rw [repCount] <;> simp
        | some v =>
            match v, hnot0, hnot1 with
            | 0, h, _ => exact absurd rfl h
            | 1, _, h => exact absurd rfl h
            | (_ + 2), _, _ => rw [repCount] <;> simp
      rw [hcount] at hlt
      rcases Nat.eq_or_lt_of_le hge with rfl | h1
      · rw [hinfo]
        refine ⟨?_, ?_⟩
        · show lo' ≤ none32
          have := hw.1.1
          have := maxQuant_lt_none32
          omega
        · show hiCode hi' ≤ none32
          cases hi' with
          | none => exact Nat.le_refl _
          | some v => exact Nat.le_of_lt (hbound v rfl)
      · exact ihbody hw.2 r h1 (by omega)

/-- Which is the whole repetition table of a compiled pattern. -/
theorem compile_counts {p : Pat} (hc : Covered p.root) (hw : WfAst p.root) :
    ∀ a : Nat, a < (compile p).reps.size →
      ((compile p).reps[a]!).lo ≤ none32 ∧
        ((compile p).reps[a]!).hi ≤ none32 := by
  obtain ⟨hfrag, hrsz, -, -⟩ := compile_shape hc
  intro a ha
  rw [hrsz] at ha
  exact hfrag.repFits hw a (Nat.zero_le _) (by omega)

/-! ## Counting the region table

`ReWfCompile.lean` bounds the code a node emits by walking the compiler with a
per-node count. What follows is that walk read on the region table instead,
and it needs the same eleven readings of the emitters — none of them says
anything but "this one leaves the table alone".
-/

private theorem emit_regs (st : CState) (i : Inst) :
    (emit st i).1.regions.size = st.regions.size := rfl

private theorem close_regs (st : CState) (at_ : Nat) :
    (closeRegion st at_).regions.size = st.regions.size := by
  show (st.regions.modify at_ _).size = _
  simp

private theorem patch_regs (st : CState) (pc : Nat) (f : Inst → Inst) :
    (patch st pc f).regions.size = st.regions.size := rfl

private theorem drop_regs (st : CState) (at_ : Nat) :
    (dropEmptyRegion st at_).regions.size ≤ st.regions.size := by
  rw [dropEmptyRegion]
  split
  · split
    · show st.regions.pop.size ≤ _
      simp
    · exact Nat.le_refl _
  · exact Nat.le_refl _

private theorem finish_regs (st : CState) (at_ : Nat) :
    (dropEmptyRegion (closeRegion st at_) at_).regions.size ≤ st.regions.size := by
  have h := drop_regs (closeRegion st at_) at_
  rw [close_regs] at h
  exact h

private theorem branch_regs (inside : Nat) (st : CState) :
    (altBranchSt inside st).regions.size = st.regions.size + 1 := by
  show (st.regions.push _).size = _
  simp

private theorem split_regs (st : CState) :
    (altSplitSt st).regions.size = st.regions.size := rfl

private theorem out_regs (arm : Ast) (inside : Nat) (st : CState) :
    (altOut arm inside st).regions.size = (altMid arm inside st).regions.size := by
  show ((altMid arm inside st).regions.modify _ _).size = _
  simp

private theorem grp_regs (here : Nat) (st : CState) :
    (grpSt here st).regions.size = st.regions.size + 1 := by
  show (st.regions.push _).size = _
  simp

private theorem repOpt_regs (here : Nat) (st : CState) :
    (repOptSt here st).regions.size = st.regions.size + 1 := by
  show (st.regions.push _).size = _
  simp

private theorem repGenSt_regs (lo' : Nat) (hi : Option Nat) (greedy : Bool)
    (here : Nat) (st : CState) :
    (repGenSt lo' hi greedy here st).regions.size = st.regions.size + 1 := by
  show (st.regions.push _).size = _
  simp

private theorem repGenOut_regs (r : Nat) (st : CState) :
    (repGenOut r st).regions.size = st.regions.size := rfl

private theorem patchAll_regs (stop : Nat) :
    ∀ (js : List Nat) (st : CState),
      (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
        st).regions = st.regions
  | [], _ => rfl
  | j :: js', st => by
      rw [List.foldl_cons, patchAll_regs stop js']
      rfl

private theorem compileAlt_regs {n : Nat}
    (ih : ∀ {a : Ast}, sizeOf a ≤ n → Covered a →
      ∀ (here : Nat) (st : CState),
        (compileNode a here st).regions.size + 1 ≤
          st.regions.size + 2 * nodeCount a) :
    ∀ (rest : List Ast) (arm : Ast), sizeOf arm ≤ n → Covered arm →
      (∀ x ∈ rest, sizeOf x ≤ n ∧ Covered x) →
      ∀ (inside : Nat) (jumps : Array Nat) (st : CState),
        (compileAlt arm rest inside jumps st).regions.size + 2 ≤
          st.regions.size + 2 * nodeCount (.alt (arm :: rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro arm hsz hc _ inside jumps st
      have hregs : (compileAlt arm [] inside jumps st).regions.size =
          (compileNode arm st.regions.size
            (altBranchSt inside st)).regions.size := by
        rw [compileAlt_nil_eq, close_regs, ← Array.foldl_toList,
          show ∀ s : CState, s.regions.size = s.regions.size from fun _ => rfl]
        rw [patchAll_regs]
      have harm := ih hsz hc st.regions.size (altBranchSt inside st)
      rw [branch_regs] at harm
      rw [hregs, nodeCount_alt_cons, nodeCount, nodeCountList]
      omega
  | cons next rest' ihrest =>
      intro arm hsz hc helems inside jumps st
      have hnext : sizeOf next ≤ n ∧ Covered next := helems next (by simp)
      have hrest' : ∀ x ∈ rest', sizeOf x ≤ n ∧ Covered x :=
        fun x hx => helems x (by simp [hx])
      have harm := ih hsz hc (altSplitSt st).regions.size
        (altBranchSt inside (altSplitSt st))
      rw [branch_regs] at harm
      have hmid : (compileNode arm (altSplitSt st).regions.size
          (altBranchSt inside (altSplitSt st))).regions.size =
          (altMid arm inside st).regions.size := rfl
      rw [hmid, split_regs] at harm
      have htail := ihrest next hnext.1 hnext.2 hrest' inside
        (jumps.push (altMid arm inside st).code.size) (altOut arm inside st)
      rw [out_regs] at htail
      rw [compileAlt_cons_eq, nodeCount_alt_cons arm (next :: rest')]
      omega

/-- A node opens at most two regions, and the count carries one cell of slack
so that an alternation's branch regions have somewhere to come from. Two with
no slack fails on a three-armed alternation, which is why the statement is
written with the `+ 1` on the left. -/
theorem compileNode_regs :
    ∀ (n : Nat) {a : Ast}, sizeOf a ≤ n → Covered a →
    ∀ (here : Nat) (st : CState),
      (compileNode a here st).regions.size + 1 ≤
        st.regions.size + 2 * nodeCount a := by
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
          rw [compileNode, emit_regs]
          omega
      | chrCI folded =>
          rw [compileNode, emit_regs]
          omega
      | cls bits =>
          rw [compileNode, emit_regs]
          show st.regions.size + 1 ≤ _
          omega
      | any =>
          rw [compileNode, emit_regs]
          omega
      | anyNoNL =>
          rw [compileNode, emit_regs]
          omega
      | bsr =>
          rw [compileNode, emit_regs]
          omega
      | assn ha =>
          rw [compileNode_assn ha, emit_regs]
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
          have hchain := compileAlt_regs (fun h hc => ih h hc) (b :: rest) a1
            hsza hca helems st.regions.size #[]
            { st with regions := (st.regions.push
                ⟨.alt, here, st.code.size, st.code.size⟩) }
          have hopen : ({ st with regions := (st.regions.push
              (⟨.alt, here, st.code.size, st.code.size⟩ : Region)) } :
              CState).regions.size = st.regions.size + 1 := by
            show (st.regions.push _).size = _
            simp
          rw [hopen] at hchain
          rw [hstep, close_regs]
          omega
      | @grp cap body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          by_cases hcap : (cap != 0) = true
          · rw [compileNode_grp_pos body here st hcap]
            have hfin := finish_regs
              (emit (compileNode body st.regions.size
                (emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1)
                ⟨.save, 2 * cap + 1, 0⟩).1 st.regions.size
            rw [emit_regs] at hfin
            have hbody := ih hszb hcbody st.regions.size
              (emit (grpSt here st) ⟨.save, 2 * cap, 0⟩).1
            rw [emit_regs, grp_regs] at hbody
            rw [nodeCount]
            omega
          · have hzero : cap = 0 := by
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hcap
              simpa using hcap
            subst hzero
            rw [compileNode_grp_zero body here st]
            have hfin := finish_regs
              (compileNode body st.regions.size (grpSt here st)) st.regions.size
            have hbody := ih hszb hcbody st.regions.size (grpSt here st)
            rw [grp_regs] at hbody
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
          rw [compileNode_repOpt_eq greedy body here st hlo', close_regs,
            patch_regs]
          have hbody := ih hszb hcbody st.regions.size (repOptSt here st)
          rw [repOpt_regs] at hbody
          rw [nodeCount]
          omega
      | @repGen lo hi greedy body hnot0 hnot1 hbound hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          rw [compileNode_repGen_eq greedy body here st hnot0 hnot1,
            close_regs, repGenOut_regs]
          have hbody := ih hszb hcbody st.regions.size
            (repGenSt lo hi greedy here st)
          rw [repGenSt_regs] at hbody
          rw [nodeCount]
          omega

/-! ## How many regions there are -/

/-- So a region index and the NONE sentinel are different numbers. The parser
stops at `maxNodes`, two regions per node is `16416`, and a sentinel is four
billion. -/
theorem compile_regions {p : Pat} (hc : Covered p.root) (hp : PatFits p) :
    (compile p).regions.size ≤ none32 := by
  have hroot := compileNode_regs (sizeOf p.root) (Nat.le_refl _) hc 0 rootSt
  have hstart : rootSt.regions.size = 1 := rfl
  have hfinal : (compile p).regions.size =
      (compileNode p.root 0 rootSt).regions.size := by
    by_cases hend : p.opts.endanchored = true
    · simp only [compile, hend, if_true]
      rw [close_regs, emit_regs, emit_regs]
      rfl
    · simp only [compile, eq_false_of_ne_true hend, Bool.false_eq_true,
        if_false]
      rw [close_regs, emit_regs]
      rfl
  have hnodes := hp.nodes
  have hmax : maxNodes = 2 * 4096 + 16 := rfl
  have hn32 : none32 = 0xFFFFFFFF := rfl
  omega


/-! ## Where an alternation and a repetition close

`ends` is the last of the six, and it is about the region table rather than
about the code. The walk below carries three things at once, because they hold
each other up: the table is never empty, its first entry is the root, and
every alternation and every repeat region in it closes at or before the code
emitted so far.

The third is the one wanted. The first two are what make the last step work:
`compile` closes the root *after* the trailing `Accept` has gone out, so the
root really does close at the very end of the code. It is spared by its kind
rather than by its range, and knowing which entry is the root is therefore
part of the invariant rather than a remark about it.

No case needs to know that the table only grows. `dropEmptyRegion` is the one
step that shortens it, and it shortens it only where it has already tested
that the index it was given is in range — which, for an index that is not the
root, leaves at least the root behind.
-/

private theorem getBang_pop_lt {α : Type _} [Inhabited α] (a : Array α)
    {i : Nat} (h : i < a.pop.size) : a.pop[i]! = a[i]! := by
  have hlt : i < a.size := by simp only [Array.size_pop] at h; omega
  rw [getElem!_pos a.pop i h, getElem!_pos a i hlt]
  simp

/-- The three clauses, on the state under construction. -/
private structure RegsInv (st : CState) : Prop where
  pos : 0 < st.regions.size
  root : (st.regions[0]!).kind = .root
  ends : ∀ j, j < st.regions.size →
    ((st.regions[j]!).kind = .alt ∨ (st.regions[j]!).kind = .«repeat») →
    (st.regions[j]!).hi ≤ st.code.size

/-- Emitting a cell, rewriting one, or filling either of the two tables the
invariant says nothing about. -/
private theorem regsInv_same {st u : CState} (h : RegsInv st)
    (hr : u.regions = st.regions) (hc : st.code.size ≤ u.code.size) :
    RegsInv u where
  pos := by rw [hr]; exact h.pos
  root := by rw [hr]; exact h.root
  ends := by
    rw [hr]
    exact fun j hj hk => Nat.le_trans (h.ends j hj hk) hc

/-- Opening a region. The new entry starts and ends where the code does, so it
is inside the bound whatever kind it is. -/
private theorem regsInv_push {st u : CState} (h : RegsInv st) {k : Rk}
    {par : Nat}
    (hr : u.regions = st.regions.push ⟨k, par, st.code.size, st.code.size⟩)
    (hc : st.code.size ≤ u.code.size) : RegsInv u := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, Array.size_push]
    omega
  · rw [hr, getBang_push_lt _ _ h.pos]
    exact h.root
  · intro j hj hk
    rw [hr, Array.size_push] at hj
    rw [hr] at hk ⊢
    rcases Nat.lt_or_ge j st.regions.size with hlt | hge
    · rw [getBang_push_lt _ _ hlt] at hk ⊢
      exact Nat.le_trans (h.ends j hlt hk) hc
    · have hj0 : j = st.regions.size := by omega
      subst hj0
      rw [getBang_push_eq]
      exact hc

/-- Closing one. It takes the end of the code as its own, and the index is
never the root's, so the root's entry comes through untouched. -/
private theorem regsInv_close {st : CState} (h : RegsInv st) {a : Nat}
    (ha : a ≠ 0) : RegsInv (closeRegion st a) := by
  have hreg : (closeRegion st a).regions =
      st.regions.modify a (fun r => { r with hi := st.code.size }) := rfl
  have hcode : (closeRegion st a).code.size = st.code.size := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hreg, Array.size_modify]
    exact h.pos
  · rw [hreg, getBang_modify_ne _ _ (Ne.symm ha)]
    exact h.root
  · intro j hj hk
    rw [hreg, Array.size_modify] at hj
    rw [hreg] at hk ⊢
    rw [hcode]
    by_cases hja : j = a
    · subst hja
      rw [getBang_modify_eq _ _ hj]
      exact Nat.le_refl _
    · rw [getBang_modify_ne _ _ hja] at hk ⊢
      exact h.ends j hj hk

/-- And taking one back off. The test the step has already made is what says
the root is not the entry going. -/
private theorem regsInv_drop {st : CState} (h : RegsInv st) {a : Nat}
    (ha : a ≠ 0) : RegsInv (dropEmptyRegion st a) := by
  rw [dropEmptyRegion]
  split
  · rename_i hlt
    split
    · refine ⟨?_, ?_, ?_⟩
      · show 0 < st.regions.pop.size
        rw [Array.size_pop]
        omega
      · show (st.regions.pop[0]!).kind = _
        rw [getBang_pop_lt _ (by rw [Array.size_pop]; omega)]
        exact h.root
      · intro j hj hk
        show (st.regions.pop[j]!).hi ≤ _
        rw [Array.size_pop] at hj
        rw [getBang_pop_lt _ (by rw [Array.size_pop]; omega)] at hk ⊢
        exact h.ends j (by omega) hk
    · exact h
  · exact h

/-! ### The walk -/

private theorem patchAll_code (stop : Nat) :
    ∀ (js : List Nat) (st : CState),
      (js.foldl (fun s pc => patch s pc fun i => { i with arg := stop })
        st).code.size = st.code.size
  | [], _ => rfl
  | j :: js', st => by
      rw [List.foldl_cons, patchAll_code stop js']
      show (st.code.modify j _).size = _
      simp

/-- One cell laid down. -/
private theorem regsInv_emit {st : CState} (h : RegsInv st) (i : Inst) :
    RegsInv (emit st i).1 :=
  regsInv_same h rfl (by show st.code.size ≤ (st.code.push i).size; simp)

private theorem compileAlt_inv {n : Nat}
    (ih : ∀ {a : Ast}, sizeOf a ≤ n → Covered a →
      ∀ (here : Nat) (st : CState), RegsInv st →
        RegsInv (compileNode a here st)) :
    ∀ (rest : List Ast) (arm : Ast), sizeOf arm ≤ n → Covered arm →
      (∀ x ∈ rest, sizeOf x ≤ n ∧ Covered x) →
      ∀ (inside : Nat) (jumps : Array Nat) (st : CState), RegsInv st →
        RegsInv (compileAlt arm rest inside jumps st) := by
  intro rest
  induction rest with
  | nil =>
      intro arm hsz hc _ inside jumps st hinv
      rw [compileAlt_nil_eq]
      have harm := ih hsz hc st.regions.size (altBranchSt inside st)
        (regsInv_push (u := altBranchSt inside st) hinv rfl (Nat.le_refl _))
      refine regsInv_close (regsInv_same harm ?_ ?_)
        (by have := hinv.pos; omega)
      · rw [← Array.foldl_toList]
        exact patchAll_regs _ _ _
      · rw [← Array.foldl_toList]
        exact Nat.le_of_eq (patchAll_code _ _ _).symm
  | cons next rest' ihrest =>
      intro arm hsz hc helems inside jumps st hinv
      have hnext : sizeOf next ≤ n ∧ Covered next := helems next (by simp)
      have hrest' : ∀ x ∈ rest', sizeOf x ≤ n ∧ Covered x :=
        fun x hx => helems x (by simp [hx])
      have hsplit : RegsInv (altSplitSt st) :=
        regsInv_same hinv rfl (by
          show st.code.size ≤ ((st.code.push _).modify _ _).size
          simp)
      have hmid := ih hsz hc (altSplitSt st).regions.size
        (altBranchSt inside (altSplitSt st))
        (regsInv_push (u := altBranchSt inside (altSplitSt st)) hsplit rfl
          (Nat.le_refl _))
      rw [compileAlt_cons_eq]
      refine ihrest next hnext.1 hnext.2 hrest' inside _ (altOut arm inside st) ?_
      refine regsInv_same (regsInv_close (a := st.regions.size) hmid
        (by have := hinv.pos; omega)) rfl ?_
      show (altMid arm inside st).code.size ≤
        (((altMid arm inside st).code.push _).modify _ _).size
      simp

/-- Compiling a node leaves the table with a root at its head and every
alternation and every repetition inside the code emitted so far. -/
private theorem compileNode_inv :
    ∀ (n : Nat) {a : Ast}, sizeOf a ≤ n → Covered a →
    ∀ (here : Nat) (st : CState), RegsInv st →
      RegsInv (compileNode a here st) := by
  intro n
  induction n with
  | zero =>
      intro a hsz hc
      exfalso
      cases hc with
      | assn ha => cases a <;> simp [assnOp] at ha ⊢ <;> simp_all
      | _ => simp_all
  | succ n ih =>
      intro a hsz hc here st hinv
      cases hc with
      | nul => rw [compileNode]; exact hinv
      | chr b => rw [compileNode]; exact regsInv_emit hinv _
      | chrCI folded => rw [compileNode]; exact regsInv_emit hinv _
      | cls bits =>
          rw [compileNode]
          exact regsInv_same hinv rfl (by
            show st.code.size ≤ ((st.code.push _)).size
            simp)
      | any => rw [compileNode]; exact regsInv_emit hinv _
      | anyNoNL => rw [compileNode]; exact regsInv_emit hinv _
      | bsr => rw [compileNode]; exact regsInv_emit hinv _
      | assn ha => rw [compileNode_assn ha]; exact regsInv_emit hinv _
      | catNil => rw [compileNode, compileCat]; exact hinv
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
          rw [hstep]
          exact ih hszk.2 hckids here _ (ih hszk.1 hck here st hinv)
      | @altOne a1 hca =>
          have hsza : sizeOf a1 ≤ n := by simp at hsz; omega
          have hstep : compileNode (.alt [a1]) here st =
              compileNode a1 here st := by
            rw [compileNode]
          rw [hstep]
          exact ih hsza hca here st hinv
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
          rw [hstep]
          exact regsInv_close
            (compileAlt_inv (fun h hc => ih h hc) (b :: rest) a1 hsza hca helems
              st.regions.size #[] _
              (regsInv_push (u := { st with regions := (st.regions.push
                  ⟨.alt, here, st.code.size, st.code.size⟩) }) hinv rfl
                (Nat.le_refl _)))
            (by have := hinv.pos; omega)
      | @grp cap body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          by_cases hcap : (cap != 0) = true
          · rw [compileNode_grp_pos body here st hcap]
            refine regsInv_drop (regsInv_close ?_ (by have := hinv.pos; omega))
              (by have := hinv.pos; omega)
            exact regsInv_emit (ih hszb hcbody st.regions.size _
              (regsInv_emit (regsInv_push (u := grpSt here st) hinv rfl
                (Nat.le_refl _)) _)) _
          · have hzero : cap = 0 := by
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hcap
              simpa using hcap
            subst hzero
            rw [compileNode_grp_zero body here st]
            refine regsInv_drop (regsInv_close ?_ (by have := hinv.pos; omega))
              (by have := hinv.pos; omega)
            exact ih hszb hcbody st.regions.size _
              (regsInv_push (u := grpSt here st) hinv rfl (Nat.le_refl _))
      | @repNone lo greedy body => rw [compileNode]; exact hinv
      | @repOne greedy body hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hstep : compileNode (.rep 1 (some 1) greedy body) here st =
              compileNode body here st := by
            rw [compileNode]
            simp
          rw [hstep]
          exact ih hszb hcbody here st hinv
      | @repOpt lo greedy body hlo hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          have hlo' : (lo == 1) = false := by simpa using hlo
          rw [compileNode_repOpt_eq greedy body here st hlo']
          refine regsInv_close ?_ (by have := hinv.pos; omega)
          refine regsInv_same (ih hszb hcbody st.regions.size (repOptSt here st)
            (regsInv_push (u := repOptSt here st) hinv rfl (by
              show st.code.size ≤ (st.code.push _).size
              simp))) rfl ?_
          show (compileNode body st.regions.size (repOptSt here st)).code.size ≤
            ((compileNode body st.regions.size (repOptSt here st)).code.modify
              _ _).size
          simp
      | @repGen lo hi greedy body hnot0 hnot1 hbound hcbody =>
          have hszb : sizeOf body ≤ n := by simp at hsz; omega
          rw [compileNode_repGen_eq greedy body here st hnot0 hnot1]
          refine regsInv_close ?_ (by have := hinv.pos; omega)
          refine regsInv_same (ih hszb hcbody st.regions.size
            (repGenSt lo hi greedy here st)
            (regsInv_push (u := repGenSt lo hi greedy here st) hinv rfl (by
              show st.code.size ≤ (((st.code.push _).push _).push _).size
              simp only [Array.size_push]
              omega))) rfl ?_
          show (compileNode body st.regions.size
              (repGenSt lo hi greedy here st)).code.size ≤
            ((compileNode body st.regions.size
              (repGenSt lo hi greedy here st)).code.push _).size
          simp


/-- Where `compile` starts: one region, the root, and no code. -/
private theorem regsInv_root : RegsInv rootSt where
  pos := by decide
  root := by decide
  ends := by decide

/-- So no alternation and no repeat region ends the program. The root does,
and it is the entry the invariant has been keeping track of: `compile` closes
it after the trailing `Accept` has gone out, which is why the bound is strict
for every other kind and an equality for that one. -/
theorem compile_ends {p : Pat} (hc : Covered p.root) :
    ∀ j, j < (compile p).regions.size →
      (((compile p).regions[j]!).kind = .alt ∨
        ((compile p).regions[j]!).kind = .«repeat») →
      ((compile p).regions[j]!).hi < (compile p).code.size := by
  have key : ∀ st : CState, RegsInv st →
      ∀ j, j < (closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).regions.size →
        (((closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).regions[j]!).kind = .alt ∨
          ((closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).regions[j]!).kind =
            .«repeat») →
        ((closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).regions[j]!).hi <
          (closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).code.size := by
    intro st h j hj hk
    have hcs : (emit st ⟨.accept, 0, 0⟩).1.code.size = st.code.size + 1 := by
      show (st.code.push _).size = _
      simp
    have hreg : (closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).regions =
        st.regions.modify 0
          (fun r => { r with hi := (emit st ⟨.accept, 0, 0⟩).1.code.size }) :=
      rfl
    have hcode : (closeRegion (emit st ⟨.accept, 0, 0⟩).1 0).code.size =
        st.code.size + 1 := hcs
    rw [hreg, Array.size_modify] at hj
    rw [hreg] at hk ⊢
    rw [hcode]
    by_cases hj0 : j = 0
    · subst hj0
      exfalso
      rw [getBang_modify_eq _ _ hj] at hk
      have hkind : ({ (st.regions[0]!) with
          hi := (emit st ⟨.accept, 0, 0⟩).1.code.size } : Region).kind =
          (st.regions[0]!).kind := rfl
      rw [hkind, h.root] at hk
      exact absurd hk (by decide)
    · rw [getBang_modify_ne _ _ hj0] at hk ⊢
      have hle := h.ends j hj hk
      omega
  have hbody : RegsInv (compileNode p.root 0 rootSt) :=
    compileNode_inv (sizeOf p.root) (Nat.le_refl _) hc 0 rootSt regsInv_root
  by_cases hend : p.opts.endanchored = true
  · simp only [compile, hend, if_true]
    exact key _ (regsInv_emit hbody ⟨.eod, 0, 0⟩)
  · simp only [compile, eq_false_of_ne_true hend, Bool.false_eq_true, if_false]
    exact key _ hbody


end Pcrevera.Refine

namespace Pcrevera.Ref

open Pcrevera Pcrevera.Refine
/-! ## The bundle, as far as the compiler settles it -/

/-- `ReRules` for a compiled pattern: all six fields, off the three
hypotheses the refinement theorems ask of a pattern already.

Which means the rules are not conditions a caller has to check but facts about
the compiler, and the resource bounds that read a program through them are
theorems about a source pattern. An `Re` that did not come from `Ref.compile`
is another matter, and the statements over an arbitrary one keep carrying the
bundle, because an arbitrary one has to. -/
theorem compile_reRules {p : Pat} (hw : Wf p) (hcov : Covered p.root)
    (hpat : PatFits p) : ReRules (compile p) where
  accept := compile_accept p
  ends := compile_ends hcov
  saves := compile_saves hcov hw.2
  counts := compile_counts hcov hw.1
  regs := compile_repRegs p
  regions := compile_regions hcov hpat

end Pcrevera.Ref
