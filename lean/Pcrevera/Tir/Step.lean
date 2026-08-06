import Pcrevera.Tir.Stable

/-!
# Stepping a body, one statement at a time

The automation gate 4 exists to build and gate 5 spends. A simulation lemma
is an argument about what a function does to a store, and the evaluator is a
tree of matches on a statement — so the first thing every such proof needs is
to stop looking at the tree. These lemmas say what one statement does, so a
proof can rewrite through a body the way a reader walks it.

The three shapes worth naming, because they are what a body is:

* a body runs its statements in order and stops at the first that leaves,
  which `evalStmts_cons` and `evalStmts_cons_abrupt` split;
* a statement that only touches the store answers under any budget, which is
  what makes all but the loop and the call lemmas fuel-free;
* a loop is a round and then the rest of the loop, which `evalWhile_step` is.

Nothing here is deep. It is the difference between a proof that reads and one
that is a wall of `simp only []`.
-/

namespace Pcrevera.Tir

/-- Sequencing after a value that is already there. The one rewrite every
expression lemma below needs before it can look at the operation. -/
@[simp] theorem Res.ok_bind {α β : Type} {a : α} {f : α → Res β} :
    (Res.ok a) >>= f = f a := rfl

variable {fuel : Nat} {p : Program} {env : Env}

@[simp] theorem evalStmts_nil :
    evalStmts fuel p [] env = some (.ok (env, .normal)) := by
  rw [evalStmts.eq_def]

/-- A statement that fell through: the body carries on from the store it
left. -/
theorem evalStmts_cons {s : Stmt} {rest : List Stmt} {env' : Env}
    (h : evalStmt fuel p s env = some (.ok (env', .normal))) :
    evalStmts fuel p (s :: rest) env = evalStmts fuel p rest env' := by
  rw [evalStmts.eq_def]
  simp only []
  rw [h]

/-- A statement that left: the body is done, and says so. -/
theorem evalStmts_cons_abrupt {s : Stmt} {rest : List Stmt} {env' : Env}
    {f : Flow} (hf : f ≠ .normal)
    (h : evalStmt fuel p s env = some (.ok (env', f))) :
    evalStmts fuel p (s :: rest) env = some (.ok (env', f)) := by
  rw [evalStmts.eq_def]
  simp only []
  rw [h]
  cases f with
  | normal => exact absurd rfl hf
  | brk => rfl
  | cont => rfl
  | ret _ => rfl

theorem evalStmts_cons_trap {s : Stmt} {rest : List Stmt} {c : String}
    (h : evalStmt fuel p s env = some (.trap c)) :
    evalStmts fuel p (s :: rest) env = some (.trap c) := by
  rw [evalStmts.eq_def]
  simp only []
  rw [h]

/-! ## The statements that only touch the store

Each of these is the evaluator's own clause, read back. They carry no budget,
which is what lets a proof about a straight-line body forget fuel entirely
until it meets a loop or a call. -/

/-- The destination is resolved first, which section 13 pins and which is
therefore part of what this says rather than a detail it could hide. -/
@[simp] theorem evalStmt_assign {pl : Place} {v : Expr} :
    evalStmt fuel p (.assign pl v) env =
      some (do
        let _ ← resolvePlace p env pl
        let x ← evalExpr p env v
        let env' ← writePlace p env pl x
        .ok (env', .normal)) := by
  rw [evalStmt.eq_def]

/-- The common case, where the destination resolves: an assignment is the
value and the store, in that order. -/
theorem evalStmt_assign_ok {pl : Place} {v : Expr} {cur : Value}
    (h : readPlace p env pl = .ok cur) :
    evalStmt fuel p (.assign pl v) env =
      some (do
        let x ← evalExpr p env v
        let env' ← writePlace p env pl x
        .ok (env', .normal)) := by
  rw [evalStmt_assign, resolvePlace, h]
  rfl

@[simp] theorem evalStmt_break :
    evalStmt fuel p .breakS env = some (.ok (env, .brk)) := by
  rw [evalStmt.eq_def]

@[simp] theorem evalStmt_continue :
    evalStmt fuel p .continueS env = some (.ok (env, .cont)) := by
  rw [evalStmt.eq_def]

@[simp] theorem evalStmt_return_none :
    evalStmt fuel p (.returnS none) env = some (.ok (env, .ret none)) := by
  rw [evalStmt.eq_def]

theorem evalStmt_return_some {e : Expr} {v : Value}
    (h : evalExpr p env e = .ok v) :
    evalStmt fuel p (.returnS (some e)) env = some (.ok (env, .ret (some v))) := by
  rw [evalStmt.eq_def]
  simp only []
  rw [h]

theorem evalStmt_let {n : String} {t : Ty} {e : Expr} {v : Value}
    (h : evalExpr p env e = .ok v) :
    evalStmt fuel p (.letS n t (some e)) env =
      some (.ok (env.declare n t v, .normal)) := by
  rw [evalStmt.eq_def]
  simp only []
  rw [h]

theorem evalStmt_let_zero {n : String} {t : Ty} {v : Value}
    (h : zero p t = some v) :
    evalStmt fuel p (.letS n t none) env =
      some (.ok (env.declare n t v, .normal)) := by
  rw [evalStmt.eq_def]
  simp only []
  rw [h]

/-! ## Control -/

theorem evalStmt_if_true {c : Expr} {t e : List Stmt}
    (h : evalExpr p env c = .ok (.bool true)) :
    evalStmt fuel p (.ifS c t e) env = evalStmts fuel p t env := by
  rw [evalStmt.eq_def]
  simp only []
  rw [h]

theorem evalStmt_if_false {c : Expr} {t e : List Stmt}
    (h : evalExpr p env c = .ok (.bool false)) :
    evalStmt fuel p (.ifS c t e) env = evalStmts fuel p e env := by
  rw [evalStmt.eq_def]
  simp only []
  rw [h]

@[simp] theorem evalStmt_while {c v : Expr} {body : List Stmt} :
    evalStmt fuel p (.whileS c v body) env = evalWhile fuel p c body env := by
  rw [evalStmt.eq_def]

/-- The loop's condition said no, and the store is where the loop left it. -/
theorem evalWhile_done {c : Expr} {body : List Stmt}
    (h : evalExpr p env c = .ok (.bool false)) :
    evalWhile (fuel + 1) p c body env = some (.ok (env, .normal)) := by
  rw [evalWhile.eq_def]
  simp only []
  rw [h]

/-- One round, then the rest of the loop. The budget falls by one, which is
the only place a straight-line proof has to think about it. -/
theorem evalWhile_step {c : Expr} {body : List Stmt} {env' : Env}
    (hc : evalExpr p env c = .ok (.bool true))
    (hb : evalStmts fuel p body env = some (.ok (env', .normal))) :
    evalWhile (fuel + 1) p c body env = evalWhile fuel p c body env' := by
  rw [evalWhile.eq_def]
  simp only []
  rw [hc]
  simp only []
  rw [hb]

/-- A `break` inside the round leaves the loop, normally. -/
theorem evalWhile_break {c : Expr} {body : List Stmt} {env' : Env}
    (hc : evalExpr p env c = .ok (.bool true))
    (hb : evalStmts fuel p body env = some (.ok (env', .brk))) :
    evalWhile (fuel + 1) p c body env = some (.ok (env', .normal)) := by
  rw [evalWhile.eq_def]
  simp only []
  rw [hc]
  simp only []
  rw [hb]

/-- A `return` inside the round climbs out of it. -/
theorem evalWhile_return {c : Expr} {body : List Stmt} {env' : Env}
    {v : Option Value} (hc : evalExpr p env c = .ok (.bool true))
    (hb : evalStmts fuel p body env = some (.ok (env', .ret v))) :
    evalWhile (fuel + 1) p c body env = some (.ok (env', .ret v)) := by
  rw [evalWhile.eq_def]
  simp only []
  rw [hc]
  simp only []
  rw [hb]

/-! ## The store itself

A local read after a local write, which is the algebra every loop invariant
is carried in. Writing keeps the slot's declared type, because the width
rules read it and nothing may change it. -/

theorem Env.get_set_self {n : String} {v : Value} {s : Slot}
    (h : env.get n = some s) :
    (env.set n v).get n = some { s with value := v } := by
  rw [Env.set, h]
  simp only []
  induction env with
  | nil => simp [Env.get, getAssoc] at h
  | cons e rest ih =>
      obtain ⟨k, slot⟩ := e
      simp only [Env.get, getAssoc] at h ⊢
      rw [setAssoc]
      split at h <;> rename_i hk
      · subst hk
        simp only [Option.some.injEq] at h
        subst h
        simp [getAssoc]
      · simp only [if_neg hk, getAssoc]
        exact ih h

private theorem getAssoc_setAssoc_other {α : Type} {n m : String} {v : α}
    (hne : m ≠ n) : ∀ l : List (String × α),
      getAssoc m (setAssoc n v l) = getAssoc m l
  | [] => rfl
  | (k, x) :: rest => by
      rw [setAssoc]
      split <;> rename_i hk
      · subst hk
        simp only [getAssoc, if_neg (Ne.symm hne)]
      · simp only [getAssoc]
        split
        · rfl
        · exact getAssoc_setAssoc_other hne rest

theorem Env.get_set_other {n m : String} {v : Value} (hne : m ≠ n) :
    (env.set n v).get m = env.get m := by
  rw [Env.set]
  cases env.get n with
  | none => rfl
  | some s => exact getAssoc_setAssoc_other hne env

theorem readPlace_var {n : String} {t : Ty} {v : Value}
    (h : env.get n = some ⟨t, v⟩) : readPlace p env (.var n) = .ok v := by
  rw [readPlace, h]

theorem writePlace_var {n : String} {v : Value} {s : Slot}
    (h : env.get n = some s) :
    writePlace p env (.var n) v = .ok (env.set n v) := by
  rw [writePlace, h]

/-- A local written and then read back, which is one round of any loop
invariant: the value is the one written and the declared type is the one the
slot always had. -/
theorem get_set_read {n : String} {t : Ty} {v w : Value}
    (h : env.get n = some ⟨t, v⟩) :
    readPlace p (env.set n w) (.var n) = .ok w :=
  readPlace_var (Env.get_set_self h)

/-! ## Growing a sequence

The one statement whose answer is not only the value it was handed: a push
appends, and grows the room if the room ran out. Whether it grew is not a
fact about what the program computed, which is why a sequence is *related* to
an array rather than computed from one. -/

theorem evalStmt_push {pl : Place} {e : Expr} {m : Nat}
    {items : List Value} {c : Nat} {v : Value}
    (ht : readPlace p env pl = .ok (.seq m items c))
    (hv : evalExpr p env e = .ok v) (hroom : items.length < m) :
    evalStmt fuel p (.push pl e) env =
      some (do
        let env' ← writePlace p env pl
          (.seq m (items ++ [v]) (if items.length = c then grown m c else c))
        .ok (env', .normal)) := by
  rw [evalStmt.eq_def]
  simp only []
  rw [ht]
  simp only [Res.ok_bind]
  rw [hv]
  simp only [Res.ok_bind]
  split <;> rename_i hfull
  · exact absurd hfull (by omega)
  · rfl

/-! ## Reading the store

The other half of what a simulation proof spends: an expression is a read
and an operator, and these say which. They are the evaluator's own clauses,
stated so that a proof can name the value rather than the match. -/

theorem evalExpr_var {n : String} {t : Ty} {v : Value}
    (h : env.get n = some ⟨t, v⟩) : evalExpr p env (.var n) = .ok v := by
  rw [evalExpr.eq_def]
  simp only []
  rw [h]

theorem evalExpr_lit {t : IntTy} {v : Int} :
    evalExpr p env (.litInt t v) = .ok (.int v) := by rw [evalExpr.eq_def]

theorem evalExpr_litBool {b : Bool} :
    evalExpr p env (.litBool b) = .ok (.bool b) := by rw [evalExpr.eq_def]

theorem evalExpr_len {e : Expr} {m : Nat} {items : List Value} {c : Nat}
    (h : evalExpr p env e = .ok (.seq m items c)) :
    evalExpr p env (.len e) = .ok (.int items.length) := by
  rw [evalExpr.eq_def]
  simp only []
  rw [h]
  rfl

theorem evalExpr_cmp {op : CmpOp} {l r : Expr} {a b : Value}
    (hl : evalExpr p env l = .ok a) (hr : evalExpr p env r = .ok b) :
    evalExpr p env (.cmp op l r) = compare op a b := by
  rw [evalExpr.eq_def]
  simp only []
  rw [hl]
  simp only [Res.ok_bind]
  rw [hr]
  rfl

theorem evalExpr_bin {op : BinOp} {l r : Expr} {a b : Value}
    (hl : evalExpr p env l = .ok a) (hr : evalExpr p env r = .ok b) :
    evalExpr p env (.bin op l r)
      = binary op ((typeOf p env l).bind Ty.intTy?) a b := by
  rw [evalExpr.eq_def]
  simp only []
  rw [hl]
  simp only [Res.ok_bind]
  rw [hr]
  rfl

/-- An index that is in range reads the element; one that is not is T-01, and
which of the two happens is the whole of what a bounds proof has to show. -/
theorem evalExpr_index {b i : Expr} {m : Nat} {items : List Value} {c : Nat}
    {k : Nat} (hb : evalExpr p env b = .ok (.seq m items c))
    (hi : evalExpr p env i = .ok (.int k)) (hk : k < items.length) :
    evalExpr p env (.index b i) = .ok (items[k]!) := by
  rw [evalExpr.eq_def]
  simp only []
  rw [hb, hi]
  simp only [Res.ok_bind, asSeq]
  rw [if_pos ⟨Int.natCast_nonneg k, by simpa using hk⟩]
  simp

theorem evalExpr_field {b : Expr} {t : String} {fs : List (String × Value)}
    {name : String} {v : Value} (hb : evalExpr p env b = .ok (.struct t fs))
    (hv : getAssoc name fs = some v) :
    evalExpr p env (.field b name) = .ok v := by
  rw [evalExpr.eq_def]
  simp only []
  rw [hb]
  simp only [Res.ok_bind]
  rw [hv]

/-! ## Calls, and the judgment they compose in -/

/-- What a call to `fn` does, in the judgment gate 5 states everything in.
The budget on the left is existential, so a caller never has to know how much
its callee wanted. -/
def outsOf (params : List Param) (inner : Env) : List Value :=
  params.map fun par =>
    match inner.get par.name with
    | some s => s.value
    | none => Value.bool false

def returned : Flow → Option Value
  | .ret v => v
  | _ => none

theorem runs_of_body {fn : String} {args : List Value} {callee : Func}
    {inner : Env} {flow : Flow} (hf : p.func? fn = some callee)
    (h : ∃ n, evalStmts n p callee.body (bindParams callee.params args)
      = some (.ok (inner, flow))) :
    Runs p fn args (outsOf callee.params inner, returned flow) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [callFunc.eq_def]
  simp only []
  rw [hf]
  simp only []
  rw [hn]
  simp only [outsOf, returned]
  cases flow <;> rfl

end Pcrevera.Tir
