import Pcrevera.Tir.Region

/-!
# Gate 4: `region_kids` simulates `R.regionKids` (I-4)

The first simulation lemma, and the template gate 5 follows. The function
under proof is `regionKidsFunc`, the transcription `Tir/Region.lean` holds to
the artifact; its layer R counterpart is `Ref.regionKids`.

The proof is two loop invariants and a walk down the body. The first loop
grows the two inout vectors from empty to `total` copies of the `none32`
sentinel, which is `Array.replicate` on the layer R side — the capacities the
pushes leave behind stay existential, because they are a fact about the
growth schedule and not about the answer. The second loop takes `i` from
`total` down to 2 and processes index `i - 1` each round, which is exactly
`Ref.regionKidsGo` consuming its fuel; the invariant carries the two arrays
through the store, and a descending induction does the rest.

Two premises keep every indexed access away from T-01. The parent-order one
— every region but the root names a parent that comes before it — is what
every caller (`cert_shape`, `cert_build`, `cert_check`) settles before
calling, and `certShape_facts` extracts it from any tree the checker
passed. The size one comes from the artifact's own
types: the region vector is declared at the mark arrays' width, a value
cannot outgrow its declared maximum, and T-05 is what enforces that on
every push. `RegionsAt` does not carry that bound itself, so a caller's
simulation threads `hsize` explicitly rather than deriving it here.

Every store fact below is one `store` call. That is the whole of what the
section 10 automation changed here: the reasoning is the same, and the
walking back past writes it used to be spelled in is gone.
-/

namespace Pcrevera.Tir

open Pcrevera.Ref (Region regionKids regionKidsGo none32)

/-! ## Array operations, read at the list level the store speaks -/

theorem getElem!_toList_map {α β : Type} [Inhabited α] [Inhabited β]
    {f : α → β} {A : Array α} {k : Nat} (h : k < A.size) :
    (A.toList.map f)[k]! = f A[k]! := by
  rw [getElem!_pos (A.toList.map f) k (by simpa using h), getElem!_pos A k h]
  simp

theorem toList_map_set! {α β : Type} {f : α → β} {A : Array α} {k : Nat}
    {x : α} : (A.set! k x).toList.map f = (A.toList.map f).set k (f x) := by
  simp

/-! ## What the body's expressions evaluate to -/

theorem typeOf_var {p : Program} {env : Env} {n : String} {t : Ty} {v : Value}
    (h : env.get n = some ⟨t, v⟩) : typeOf p env (.var n) = some t := by
  simp only [typeOf]
  rw [h]
  rfl

/-- The first loop's index bump. In range, `u32` addition is addition. -/
theorem evalExpr_addOne {p : Program} {env : Env} {n : String} {k : Nat}
    (hk : k < 4294967295) (h : env.get n = some ⟨.int .u32, .int (k : Nat)⟩) :
    evalExpr p env (.bin .add (.var n) (.litInt .u32 1))
      = .ok (.int (k + 1 : Nat)) := by
  rw [evalExpr_bin (evalExpr_var h) (evalExpr_lit (t := .u32) (v := 1)),
    typeOf_var h]
  show Res.ok (Value.int (IntTy.wrap .u32 ((k : Int) + 1))) = _
  rw [wrap_u32_eq (by omega) (by omega),
    show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega]

/-- The second loop's decrement, likewise. -/
theorem evalExpr_subOne {p : Program} {env : Env} {n : String} {k : Nat}
    (h0 : 0 < k) (hk : k < 4294967296)
    (h : env.get n = some ⟨.int .u32, .int (k : Nat)⟩) :
    evalExpr p env (.bin .sub (.var n) (.litInt .u32 1))
      = .ok (.int (k - 1 : Nat)) := by
  rw [evalExpr_bin (evalExpr_var h) (evalExpr_lit (t := .u32) (v := 1)),
    typeOf_var h]
  show Res.ok (Value.int (IntTy.wrap .u32 ((k : Int) - 1))) = _
  rw [wrap_u32_eq (by omega) (by omega),
    show ((k : Int) - 1) = ((k - 1 : Nat) : Int) by omega]

/-! ## The two loops, named so the lemmas can quote them -/

def initCond : Expr := .cmp .lt (.var "i") (.var "total")

def initBody : List Stmt :=
  [.push (.var "kids") (.litInt .u32 4294967295),
   .push (.var "sibs") (.litInt .u32 4294967295),
   .assign (.var "i") (.bin .add (.var "i") (.litInt .u32 1))]

def walkCond : Expr := .cmp .gt (.var "i") (.litInt .u32 1)

def walkBody : List Stmt :=
  [.assign (.var "i") (.bin .sub (.var "i") (.litInt .u32 1)),
   .letS "tmp1" (.int .u32)
     (some (.field (.index (.var "regions") (.var "i")) "parent")),
   .assign (.index (.var "sibs") (.var "i"))
     (.index (.var "kids") (.var "tmp1")),
   .assign (.index (.var "kids") (.var "tmp1")) (.var "i")]

theorem regionKidsFunc_body :
    regionKidsFunc.body =
      [.letS "total" (.int .u32) (some (.len (.var "regions"))),
       .letS "i" (.int .u32) (some (.litInt .u32 0)),
       .whileS initCond
         (.bin .sub (.cast (.int .counter) (.var "total"))
           (.cast (.int .counter) (.var "i"))) initBody,
       .assign (.var "i") (.var "total"),
       .whileS walkCond (.cast (.int .counter) (.var "i")) walkBody] := rfl

/-! ## The initialization loop

What the store looks like between rounds: `i` counts the pushes so far, both
vectors hold that many sentinels, and the rest of the frame stands still.
The slot types ride along because the width rules read them; the capacities
are existential on purpose. -/

structure InitSt (env : Env) (tr tk ts : Ty) (rv : Value) (k total : Nat) :
    Prop where
  i : env.get "i" = some ⟨.int .u32, .int (k : Nat)⟩
  tot : env.get "total" = some ⟨.int .u32, .int (total : Nat)⟩
  regions : env.get "regions" = some ⟨tr, rv⟩
  kids : ∃ ck, env.get "kids"
    = some ⟨tk, .seq marksMax (List.map markVal (List.replicate k none32)) ck⟩
  sibs : ∃ cs, env.get "sibs"
    = some ⟨ts, .seq marksMax (List.map markVal (List.replicate k none32)) cs⟩

/-- One round of the initialization loop: both vectors one sentinel longer,
`i` one higher. The budget is universal because the body holds no loop and
no call. -/
theorem initRound {p : Program} {env : Env} {tr tk ts : Ty} {rv : Value}
    {k total : Nat} (htm : total ≤ 8208) (hklt : k < total)
    (hst : InitSt env tr tk ts rv k total) :
    ∃ env', (∀ f, evalStmts f p initBody env = some (.ok (env', .normal))) ∧
      InitSt env' tr tk ts rv (k + 1) total := by
  obtain ⟨ck, hkids⟩ := hst.kids
  obtain ⟨cs, hsibs⟩ := hst.sibs
  generalize hL : List.map markVal (List.replicate k none32) = L at hkids hsibs
  have hlen : L.length = k := by rw [← hL]; simp
  have hroom : L.length < marksMax := by rw [hlen]; show k < 8208; omega
  have hgrow : L ++ [Value.int 4294967295]
      = List.map markVal (List.replicate (k + 1) none32) := by
    rw [← hL, List.replicate_succ', List.map_append]
    rfl
  obtain ⟨env', henv'⟩ : ∃ e : Env,
      (((env.set "kids" (.seq marksMax (L ++ [Value.int 4294967295])
              (if L.length = ck then grown marksMax ck else ck))).set "sibs"
            (.seq marksMax (L ++ [Value.int 4294967295])
              (if L.length = cs then grown marksMax cs else cs))).set "i"
          (.int (k + 1 : Nat))) = e := ⟨_, rfl⟩
  refine ⟨env', fun f => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold initBody
    rw [evalStmts_cons (evalStmt_push_var hkids
        (evalExpr_lit (t := .u32) (v := 4294967295)) hroom),
      evalStmts_cons (evalStmt_push_var (t := ts) (items := L) (c := cs)
        (by store [hsibs]) (evalExpr_lit (t := .u32) (v := 4294967295)) hroom),
      evalStmts_cons (evalStmt_assign_var (t := .int .u32)
        (cur := .int (k : Nat)) (by store [hst.i])
        (evalExpr_addOne (k := k) (by omega) (by store [hst.i]))),
      evalStmts_nil, henv']
  · store [← henv', hst.i]
  · store [← henv', hst.tot]
  · store [← henv', hst.regions]
  · exact ⟨if L.length = ck then grown marksMax ck else ck,
      by store [← henv', hkids, hgrow]⟩
  · exact ⟨if L.length = cs then grown marksMax cs else cs,
      by store [← henv', hsibs, hgrow]⟩

/-- The initialization loop, whole: from `k` sentinels to `total` of them,
by induction on what is left to push. -/
theorem initLoop {p : Program} {tr tk ts : Ty} {rv : Value} {total : Nat}
    (htm : total ≤ 8208) :
    ∀ (d k : Nat) (env : Env), k + d = total →
      InitSt env tr tk ts rv k total →
      ∃ n env', evalWhile n p initCond initBody env
          = some (.ok (env', .normal)) ∧
        InitSt env' tr tk ts rv total total := by
  intro d
  induction d with
  | zero =>
      intro k env hk hst
      have hkeq : k = total := by omega
      subst hkeq
      have hc : evalExpr p env initCond = .ok (.bool false) := by
        show evalExpr p env (.cmp .lt (.var "i") (.var "total")) = _
        rw [evalExpr_cmp (evalExpr_var hst.i) (evalExpr_var hst.tot)]
        show Res.ok (Value.bool (decide ((k : Int) < (k : Int)))) = _
        rw [decide_eq_false (by omega)]
      exact ⟨1, env, evalWhile_done hc, hst⟩
  | succ d ih =>
      intro k env hk hst
      obtain ⟨env1, hbody, hst1⟩ := initRound htm (by omega) hst
      obtain ⟨n, env', hrun, hst'⟩ := ih (k + 1) env1 (by omega) hst1
      have hc : evalExpr p env initCond = .ok (.bool true) := by
        show evalExpr p env (.cmp .lt (.var "i") (.var "total")) = _
        rw [evalExpr_cmp (evalExpr_var hst.i) (evalExpr_var hst.tot)]
        show Res.ok (Value.bool (decide ((k : Int) < (total : Int)))) = _
        rw [decide_eq_true (by omega)]
      exact ⟨n + 1, env', by rw [evalWhile_step hc (hbody n)]; exact hrun, hst'⟩

/-! ## The backward walk

Between rounds of the second loop: `i` holds the count of entries still to
process, and the two vectors hold the arrays the walk has built so far. The
capacities are fixed parameters here — an indexed write replaces an element
and touches nothing else. -/

structure WalkSt (env : Env) (tr tk ts : Ty) (regions : Array Region)
    (capR ck cs : Nat) (A B : Array Nat) (j : Nat) : Prop where
  i : env.get "i" = some ⟨.int .u32, .int (j : Nat)⟩
  regions_ : env.get "regions" = some ⟨tr,
    .frozen (.seq marksMax (regions.toList.map regionValue) capR)⟩
  kids : env.get "kids"
    = some ⟨tk, .seq marksMax (A.toList.map markVal) ck⟩
  sibs : env.get "sibs"
    = some ⟨ts, .seq marksMax (B.toList.map markVal) cs⟩

/-- One round of the walk, at `i = m + 2`: the entry at `m + 1` files itself
under its parent, which is one unfolding of `Ref.regionKidsGo`. The parent
premise is what keeps both accesses through `kids` in bounds. -/
theorem walkRound {p : Program} {env : Env} {tr tk ts : Ty}
    {regions : Array Region} {capR ck cs : Nat} {A B : Array Nat} {m : Nat}
    (hsz : regions.size ≤ 8208) (hj : m + 2 ≤ regions.size)
    (hA : A.size = regions.size) (hB : B.size = regions.size)
    (hpar : (regions[m + 1]!).parent < m + 1)
    (hst : WalkSt env tr tk ts regions capR ck cs A B (m + 2)) :
    ∃ env', (∀ f, evalStmts f p walkBody env = some (.ok (env', .normal))) ∧
      WalkSt env' tr tk ts regions capR ck cs
        (A.set! (regions[m + 1]!).parent (m + 1))
        (B.set! (m + 1) (A[(regions[m + 1]!).parent]!)) (m + 1) := by
  obtain ⟨env1, henv1⟩ : ∃ e : Env,
      env.set "i" (.int (m + 1 : Nat)) = e := ⟨_, rfl⟩
  obtain ⟨env2, henv2⟩ : ∃ e : Env, env1.declare "tmp1" (.int .u32)
      (.int (((regions[m + 1]!).parent : Nat) : Int)) = e := ⟨_, rfl⟩
  obtain ⟨env3, henv3⟩ : ∃ e : Env, env2.set "sibs"
      (.seq marksMax
        ((B.set! (m + 1) (A[(regions[m + 1]!).parent]!)).toList.map markVal)
        cs) = e := ⟨_, rfl⟩
  have hreg1 : env1.get "regions" = some ⟨tr,
      .frozen (.seq marksMax (regions.toList.map regionValue) capR)⟩ := by
    store [← henv1, hst.regions_]
  have hi1 : env1.get "i" = some ⟨.int .u32, .int (m + 1 : Nat)⟩ := by
    store [← henv1, hst.i]
  -- The parent of the entry this round files, off the frozen vector.
  have hfield : evalExpr p env1
      (.field (.index (.var "regions") (.var "i")) "parent")
      = .ok (.int (((regions[m + 1]!).parent : Nat) : Int)) := by
    have hidx := evalExpr_index_frozen (p := p) (evalExpr_var hreg1)
      (evalExpr_var hi1) (k := m + 1)
      (by simp only [List.length_map, Array.length_toList]; omega)
    rw [getElem!_toList_map (by omega)] at hidx
    simp only [regionValue] at hidx
    exact evalExpr_field hidx (by simp [getAssoc])
  have hi2 : env2.get "i" = some ⟨.int .u32, .int (m + 1 : Nat)⟩ := by
    store [← henv2, hi1]
  have hkids2 : env2.get "kids"
      = some ⟨tk, .seq marksMax (A.toList.map markVal) ck⟩ := by
    store [← henv2, ← henv1, hst.kids]
  have hsibs2 : env2.get "sibs"
      = some ⟨ts, .seq marksMax (B.toList.map markVal) cs⟩ := by
    store [← henv2, ← henv1, hst.sibs]
  have htmp2 : env2.get "tmp1"
      = some ⟨.int .u32, .int (((regions[m + 1]!).parent : Nat) : Int)⟩ := by
    store [← henv2]
  -- What the parent's slot in `kids` holds, which the sibling link takes.
  have hread : evalExpr p env2 (.index (.var "kids") (.var "tmp1"))
      = .ok (markVal (A[(regions[m + 1]!).parent]!)) := by
    have h := evalExpr_index (p := p) (evalExpr_var hkids2)
      (evalExpr_var htmp2) (k := (regions[m + 1]!).parent)
      (by simp only [List.length_map, Array.length_toList]; omega)
    rwa [getElem!_toList_map (by omega)] at h
  have hkids3 : env3.get "kids"
      = some ⟨tk, .seq marksMax (A.toList.map markVal) ck⟩ := by
    store [← henv3, hkids2]
  have htmp3 : env3.get "tmp1"
      = some ⟨.int .u32, .int (((regions[m + 1]!).parent : Nat) : Int)⟩ := by
    store [← henv3, htmp2]
  have hi3 : env3.get "i" = some ⟨.int .u32, markVal (m + 1)⟩ := by
    store [← henv3, hi2, markVal] <;> rfl
  refine ⟨env3.set "kids"
      (.seq marksMax
        ((A.set! (regions[m + 1]!).parent (m + 1)).toList.map markVal) ck),
    fun f => ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : evalExpr p env (.bin .sub (.var "i") (.litInt .u32 1))
        = .ok (.int (m + 1 : Nat)) := by
      rw [evalExpr_subOne (k := m + 2) (by omega) (by omega) hst.i,
        show (m + 2 - 1 : Nat) = m + 1 by omega]
    unfold walkBody
    rw [evalStmts_cons (evalStmt_assign_var hst.i hsub), henv1,
      evalStmts_cons (evalStmt_let hfield), henv2,
      evalStmts_cons (evalStmt_assign_index_var hsibs2 (evalExpr_var hi2)
        (by simp only [List.length_map, Array.length_toList]; omega) hread),
      ← toList_map_set!, henv3,
      evalStmts_cons (evalStmt_assign_index_var hkids3 (evalExpr_var htmp3)
        (by simp only [List.length_map, Array.length_toList]; omega)
        (evalExpr_var hi3)),
      ← toList_map_set!, evalStmts_nil]
  · store [hi3, markVal] <;> rfl
  · store [← henv3, ← henv2, hreg1]
  · store [hkids3]
  · store [← henv3, hsibs2]

/-- The walk, whole: from `i = j` the loop leaves behind exactly what
`Ref.regionKidsGo` computes from fuel `j - 1`. Descending induction, one
`walkRound` per unfolding of the fuel. -/
theorem walkLoop {p : Program} {tr tk ts : Ty} {regions : Array Region}
    {capR ck cs : Nat} (hsz : regions.size ≤ 8208)
    (hord : ∀ i, 1 ≤ i → i < regions.size → (regions[i]!).parent < i) :
    ∀ (j : Nat), j ≤ regions.size →
    ∀ (A B : Array Nat) (env : Env), A.size = regions.size →
      B.size = regions.size →
      WalkSt env tr tk ts regions capR ck cs A B j →
      ∃ n env', evalWhile n p walkCond walkBody env
          = some (.ok (env', .normal)) ∧
        env'.get "regions" = some ⟨tr,
          .frozen (.seq marksMax (regions.toList.map regionValue) capR)⟩ ∧
        env'.get "kids" = some ⟨tk, .seq marksMax
          ((regionKidsGo regions (j - 1) A B).1.toList.map markVal) ck⟩ ∧
        env'.get "sibs" = some ⟨ts, .seq marksMax
          ((regionKidsGo regions (j - 1) A B).2.toList.map markVal) cs⟩ := by
  intro j
  induction j with
  | zero =>
      intro hj A B env hA hB hst
      have hc : evalExpr p env walkCond = .ok (.bool false) := by
        show evalExpr p env (.cmp .gt (.var "i") (.litInt .u32 1)) = _
        rw [evalExpr_cmp (evalExpr_var hst.i) (evalExpr_lit (t := .u32) (v := 1))]
        show Res.ok (Value.bool (decide (((0 : Nat) : Int) > 1))) = _
        rw [decide_eq_false (by omega)]
      exact ⟨1, env, evalWhile_done hc, hst.regions_, hst.kids, hst.sibs⟩
  | succ m ih =>
      match m with
      | 0 =>
          intro hj A B env hA hB hst
          have hc : evalExpr p env walkCond = .ok (.bool false) := by
            show evalExpr p env (.cmp .gt (.var "i") (.litInt .u32 1)) = _
            rw [evalExpr_cmp (evalExpr_var hst.i)
              (evalExpr_lit (t := .u32) (v := 1))]
            show Res.ok (Value.bool (decide (((0 + 1 : Nat) : Int) > 1))) = _
            rw [decide_eq_false (by omega)]
          exact ⟨1, env, evalWhile_done hc, hst.regions_, hst.kids, hst.sibs⟩
      | m' + 1 =>
          intro hj A B env hA hB hst
          have hpar : (regions[m' + 1]!).parent < m' + 1 :=
            hord (m' + 1) (by omega) (by omega)
          obtain ⟨env4, hbody, hst4⟩ := walkRound (m := m') hsz (by omega) hA hB
            hpar hst
          obtain ⟨n, env', hrun, hregs, hkids, hsibs⟩ :=
            ih (by omega) _ _ env4 (by simp [hA]) (by simp [hB]) hst4
          have hc : evalExpr p env walkCond = .ok (.bool true) := by
            show evalExpr p env (.cmp .gt (.var "i") (.litInt .u32 1)) = _
            rw [evalExpr_cmp (evalExpr_var hst.i)
              (evalExpr_lit (t := .u32) (v := 1))]
            show Res.ok (Value.bool (decide (((m' + 1 + 1 : Nat) : Int) > 1))) = _
            rw [decide_eq_true (by omega)]
          have hstep : regionKidsGo regions (m' + 1) A B
              = regionKidsGo regions m'
                (A.set! (regions[m' + 1]!).parent (m' + 1))
                (B.set! (m' + 1) (A[(regions[m' + 1]!).parent]!)) := by
            simp only [regionKidsGo]
          refine ⟨n + 1, env',
            by rw [evalWhile_step hc (hbody n)]; exact hrun, hregs, ?_, ?_⟩
          · show env'.get "kids" = some ⟨tk, .seq marksMax
              ((regionKidsGo regions (m' + 1) A B).1.toList.map markVal) ck⟩
            rw [hstep]
            exact hkids
          · show env'.get "sibs" = some ⟨ts, .seq marksMax
              ((regionKidsGo regions (m' + 1) A B).2.toList.map markVal) cs⟩
            rw [hstep]
            exact hsibs

/-! ## The theorem: the decoded function, end to end (I-4) -/

/-- `region_kids` simulates `Ref.regionKids`: called on a related frozen
region vector and two empty mark vectors, it runs — no trap, no exhausted
budget — and leaves `kids` and `sibs` related to what layer R computes.

The program is any one whose `region_kids` is the guarded transcription,
which the artifact's is. The parent-order premise is spelled the way the
layer R proofs spell it, so `certShape_facts` discharges it on any checked
tree; the size premise restates the region vector's declared maximum, which
a caller carries rather than checks. -/
theorem region_kids_simulates {p : Program}
    (hf : p.func? "region_kids" = some regionKidsFunc)
    {regions : Array Region} {vr vk vs : Value}
    (hr : RegionsAt vr regions) (hk : MarksAt vk #[]) (hs : MarksAt vs #[])
    (hsize : regions.size ≤ marksMax)
    (hord : ∀ i, 1 ≤ i → i < regions.size → (regions[i]!).parent < i) :
    ∃ vk' vs',
      Runs p "region_kids" [vr, vk, vs] ([vr, vk', vs'], none) ∧
      MarksAt vk' (regionKids regions).1 ∧
      MarksAt vs' (regionKids regions).2 := by
  obtain ⟨capR, hvr⟩ := hr
  obtain ⟨ck0, hvk⟩ := hk
  obtain ⟨cs0, hvs⟩ := hs
  obtain ⟨env0, henv0⟩ : ∃ e : Env,
      bindParams regionKidsFunc.params [vr, vk, vs] = e := ⟨_, rfl⟩
  have hreg0 : env0.get "regions"
      = some ⟨.frozen (.vec (.struct "Region") marksMax),
        .frozen (.seq marksMax (regions.toList.map regionValue) capR)⟩ := by
    rw [← henv0, ← hvr]; rfl
  have hlen0 : evalExpr p env0 (.len (.var "regions"))
      = .ok (.int (regions.size : Nat)) := by
    rw [evalExpr_len_frozen (evalExpr_var hreg0)]
    simp
  -- The two `let`s at the top of the body.
  obtain ⟨env2, henv2⟩ : ∃ e : Env,
      (env0.declare "total" (.int .u32) (.int (regions.size : Nat))).declare
        "i" (.int .u32) (.int 0) = e := ⟨_, rfl⟩
  -- The initialization loop, from nothing pushed to all of it.
  have hst2 : InitSt env2 (.frozen (.vec (.struct "Region") marksMax))
      (.vec (.int .u32) marksMax) (.vec (.int .u32) marksMax) vr 0
      regions.size := by
    refine ⟨?_, ?_, ?_, ⟨ck0, ?_⟩, ⟨cs0, ?_⟩⟩
    · store [← henv2] <;> rfl
    · store [← henv2]
    · store [← henv2, ← henv0, hvr]
      rfl
    · store [← henv2, ← henv0, hvk]
      rfl
    · store [← henv2, ← henv0, hvs]
      rfl
  obtain ⟨n1, envA, hw1, hstA⟩ := initLoop hsize regions.size 0 env2
    (by omega) hst2
  -- `i := total`, between the loops, and the backward walk after it.
  obtain ⟨ckA, hkidsA⟩ := hstA.kids
  obtain ⟨csA, hsibsA⟩ := hstA.sibs
  have hstB : WalkSt (envA.set "i" (.int (regions.size : Nat)))
      (.frozen (.vec (.struct "Region") marksMax))
      (.vec (.int .u32) marksMax) (.vec (.int .u32) marksMax) regions capR
      ckA csA (Array.replicate regions.size none32)
      (Array.replicate regions.size none32) regions.size := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · store [hstA.i]
    · store [hstA.regions, hvr]
    · store [hkidsA, Array.toList_replicate]
    · store [hsibsA, Array.toList_replicate]
  obtain ⟨n2, envC, hw2, hregC, hkidsC, hsibsC⟩ := walkLoop hsize hord
    regions.size (Nat.le_refl _) _ _ _ (by simp) (by simp) hstB
  -- The whole body, under one budget.
  have hbody : evalStmts (max n1 n2) p regionKidsFunc.body env0
      = some (.ok (envC, .normal)) := by
    rw [regionKidsFunc_body,
      evalStmts_cons (evalStmt_let hlen0),
      evalStmts_cons (evalStmt_let (evalExpr_lit (t := .u32) (v := 0))),
      henv2,
      evalStmts_cons (by
        rw [evalStmt_while]
        exact evalWhile_mono hw1 (Nat.le_max_left _ _)),
      evalStmts_cons (evalStmt_assign_var hstA.i (evalExpr_var hstA.tot)),
      evalStmts_cons (by
        rw [evalStmt_while]
        exact evalWhile_mono hw2 (Nat.le_max_right _ _)),
      evalStmts_nil]
  have hcall := runs_of_body hf ⟨max n1 n2, by rw [henv0]; exact hbody⟩
  refine ⟨_, _, ?_, ⟨ckA, rfl⟩, ⟨csA, rfl⟩⟩
  have houts : outsOf regionKidsFunc.params envC
      = [vr,
         .seq marksMax ((regionKids regions).1.toList.map markVal) ckA,
         .seq marksMax ((regionKids regions).2.toList.map markVal) csA] := by
    store [outsOf, regionKidsFunc, List.map_cons, List.map_nil,
      hregC, hkidsC, hsibsC, ← hvr] <;> rfl
  rw [← houts]
  exact hcall

end Pcrevera.Tir
