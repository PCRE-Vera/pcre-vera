import Pcrevera.Tir.Exec

/-!
# The interpreter is stable in fuel, and `Runs` is a function (I-1)

Step indexing buys totality, and it would charge for it in every simulation
lemma if the lemmas had to quote a budget. They do not, because of these two
theorems.

Stability: a budget that answered keeps answering the same, however much more
it is given. The proof walks the same mutual recursion the evaluator does, and
the only case with anything in it is the loop, where the round that ran under
the smaller budget runs identically under the larger one.

Determinism follows, and it is what makes `Runs` a judgment rather than a
relation: two runs of the same call agree, because `max` of their budgets
answers for both.
-/

namespace Pcrevera.Tir

mutual

theorem evalStmts_mono {n m : Nat} {p : Program} {body : List Stmt} {env : Env}
    {r : Res (Env × Flow)} (h : evalStmts n p body env = some r) (hle : n ≤ m) :
    evalStmts m p body env = some r := by
  match body with
  | [] =>
      rw [evalStmts.eq_def] at h ⊢
      exact h
  | s :: rest =>
      rw [evalStmts.eq_def] at h ⊢
      simp only [] at h ⊢
      cases hs : evalStmt n p s env with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some res =>
          rw [hs] at h
          rw [evalStmt_mono hs hle]
          match res with
          | .trap _ => exact h
          | .bug _ => exact h
          | .ok (env', flow) =>
              match flow with
              | .normal =>
                  simp only [] at h ⊢
                  exact evalStmts_mono h hle
              | .brk => exact h
              | .cont => exact h
              | .ret _ => exact h
termination_by (n, sizeOf body)

theorem evalStmt_mono {n m : Nat} {p : Program} {s : Stmt} {env : Env}
    {r : Res (Env × Flow)} (h : evalStmt n p s env = some r) (hle : n ≤ m) :
    evalStmt m p s env = some r := by
  match s with
  | .letS .. | .assign .. | .take .. | .swap .. | .copy .. | .freeze ..
  | .push .. | .pop .. | .truncate .. | .reserve .. | .breakS | .continueS
  | .returnS .. =>
      rw [evalStmt.eq_def] at h ⊢
      exact h
  | .ifS cond thenB elseB =>
      rw [evalStmt.eq_def] at h ⊢
      simp only [] at h ⊢
      match hc : evalExpr p env cond with
      | .trap _ =>
          first
            | (rw [hc] at h ⊢; simp only [] at h ⊢; exact h)
            | (rw [hc] at h; simp only [] at h ⊢; exact h)
      | .bug _ =>
          first
            | (rw [hc] at h ⊢; simp only [] at h ⊢; exact h)
            | (rw [hc] at h; simp only [] at h ⊢; exact h)
      | .ok v =>
          rw [hc] at h
          match v with
          | .bool true => exact evalStmts_mono h hle
          | .bool false => exact evalStmts_mono h hle
          | .int _ | .seq .. | .frozen _ | .tag .. | .struct .. => exact h
  | .whileS cond _ body =>
      rw [evalStmt.eq_def] at h ⊢
      exact evalWhile_mono h hle
  | .switchS value arms dflt =>
      rw [evalStmt.eq_def] at h ⊢
      simp only [] at h ⊢
      match hv : evalExpr p env value with
      | .trap _ =>
          first
            | (rw [hv] at h ⊢; simp only [] at h ⊢; exact h)
            | (rw [hv] at h; simp only [] at h ⊢; exact h)
      | .bug _ =>
          first
            | (rw [hv] at h ⊢; simp only [] at h ⊢; exact h)
            | (rw [hv] at h; simp only [] at h ⊢; exact h)
      | .ok v =>
          rw [hv] at h
          match v with
          | .tag _ variant => exact evalArms_mono h hle
          | .bool _ | .int _ | .seq .. | .frozen _ | .struct .. => exact h
  | .call fn args dest =>
      match n with
      | 0 => rw [evalStmt.eq_def] at h; exact absurd h (by simp)
      | n + 1 =>
          match m with
          | 0 => exact absurd hle (by omega)
          | m + 1 =>
              have hle' : n ≤ m := by omega
              rw [evalStmt.eq_def] at h ⊢
              simp only [] at h ⊢
              match hf : p.func? fn with
              | none =>
                  first
                    | (rw [hf] at h ⊢; simp only [] at h ⊢; exact h)
                    | (rw [hf] at h; simp only [] at h ⊢; exact h)
              | some callee =>
                  rw [hf] at h
                  simp only [] at h
                  cases ha : evalArgs p env callee.params args with
                  | trap c => simp only [ha] at h ⊢; exact h
                  | bug w => simp only [ha] at h ⊢; exact h
                  | ok vals =>
                      simp only [ha] at h ⊢
                      cases hb : evalStmts n p callee.body
                        (bindParams callee.params vals) with
                      | none => rw [hb] at h; exact absurd h (by simp)
                      | some inner =>
                          rw [hb] at h
                          rw [evalStmts_mono hb hle']
                          exact h
termination_by (n, sizeOf s)

theorem evalWhile_mono {n m : Nat} {p : Program} {cond : Expr}
    {body : List Stmt} {env : Env} {r : Res (Env × Flow)}
    (h : evalWhile n p cond body env = some r) (hle : n ≤ m) :
    evalWhile m p cond body env = some r := by
  match n with
  | 0 => rw [evalWhile.eq_def] at h; exact absurd h (by simp)
  | n + 1 =>
      match m with
      | 0 => exact absurd hle (by omega)
      | m + 1 =>
          have hle' : n ≤ m := by omega
          rw [evalWhile.eq_def] at h ⊢
          simp only [] at h ⊢
          match hc : evalExpr p env cond with
          | .trap _ =>
              first
                | (rw [hc] at h ⊢; simp only [] at h ⊢; exact h)
                | (rw [hc] at h; simp only [] at h ⊢; exact h)
          | .bug _ =>
              first
                | (rw [hc] at h ⊢; simp only [] at h ⊢; exact h)
                | (rw [hc] at h; simp only [] at h ⊢; exact h)
          | .ok v =>
              rw [hc] at h
              match v with
              | .bool false => exact h
              | .bool true =>
                  simp only [] at h ⊢
                  cases hb : evalStmts n p body env with
                  | none => rw [hb] at h; exact absurd h (by simp)
                  | some res =>
                      rw [hb] at h
                      rw [evalStmts_mono hb hle']
                      match res with
                      | .trap _ => exact h
                      | .bug _ => exact h
                      | .ok (env', flow) =>
                          match flow with
                          | .brk => exact h
                          | .ret _ => exact h
                          | .normal =>
                              simp only [] at h ⊢
                              exact evalWhile_mono h hle'
                          | .cont =>
                              simp only [] at h ⊢
                              exact evalWhile_mono h hle'
              | .int _ | .seq .. | .frozen _ | .tag .. | .struct .. => exact h
termination_by (n, sizeOf body)

theorem evalArms_mono {n m : Nat} {p : Program} {variant : String}
    {arms : List (String × List Stmt)} {dflt : Option (List Stmt)} {env : Env}
    {r : Res (Env × Flow)} (h : evalArms n p variant arms dflt env = some r)
    (hle : n ≤ m) : evalArms m p variant arms dflt env = some r := by
  match arms with
  | [] =>
      rw [evalArms.eq_def] at h ⊢
      simp only [] at h ⊢
      match hd : dflt with
      | none => exact h
      | some b => exact evalStmts_mono h hle
  | (name, b) :: rest =>
      rw [evalArms.eq_def] at h ⊢
      simp only [] at h ⊢
      split at h <;> rename_i hname
      · rw [if_pos hname]
        exact evalStmts_mono h hle
      · rw [if_neg hname]
        exact evalArms_mono h hle
termination_by (n, sizeOf arms + sizeOf dflt)
decreasing_by
  all_goals
    first
      | (simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega)
      | (subst hd; simp only [Option.some.sizeOf_spec]; omega)
      | omega

end

/-- A call answers the same under any larger budget. -/
theorem callFunc_mono {n m : Nat} {p : Program} {fn : String}
    {args : List Value} {r : Res (List Value × Option Value)}
    (h : callFunc n p fn args = some r) (hle : n ≤ m) :
    callFunc m p fn args = some r := by
  match n with
  | 0 => rw [callFunc.eq_def] at h; exact absurd h (by simp)
  | n + 1 =>
      match m with
      | 0 => exact absurd hle (by omega)
      | m + 1 =>
          have hle' : n ≤ m := by omega
          rw [callFunc.eq_def] at h ⊢
          simp only [] at h ⊢
          match hf : p.func? fn with
          | none =>
              first
                | (rw [hf] at h ⊢; simp only [] at h ⊢; exact h)
                | (rw [hf] at h; simp only [] at h ⊢; exact h)
          | some callee =>
              rw [hf] at h
              simp only [] at h ⊢
              cases hb : evalStmts n p callee.body (bindParams callee.params args) with
              | none => rw [hb] at h; exact absurd h (by simp)
              | some inner =>
                  rw [hb] at h
                  rw [evalStmts_mono hb hle']
                  exact h

/-- I-1's first half of the contract: a call that runs has a budget past
which the answer never changes again. -/
theorem runs_stable {p : Program} {fn : String} {args : List Value}
    {out : List Value × Option Value} (h : Runs p fn args out) :
    ∃ N, ∀ n, N ≤ n → callFunc n p fn args = some (.ok out) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun n hn => callFunc_mono hk hn⟩

/-- I-1's second half: `Runs` relates a call to at most one outcome, which is
what lets a caller's lemma compose with a callee's. -/
theorem runs_unique {p : Program} {fn : String} {args : List Value}
    {a b : List Value × Option Value} (ha : Runs p fn args a)
    (hb : Runs p fn args b) : a = b := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  have h1 := callFunc_mono hn (Nat.le_max_left n m)
  have h2 := callFunc_mono hm (Nat.le_max_right n m)
  rw [h1] at h2
  simpa using h2

end Pcrevera.Tir
