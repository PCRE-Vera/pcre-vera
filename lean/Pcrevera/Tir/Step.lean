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

/-- A `let` puts its local in front, so the new name reads back what it was
given... -/
theorem Env.get_declare_self {n : String} {t : Ty} {v : Value} :
    (env.declare n t v).get n = some ⟨t, v⟩ := by
  simp [Env.declare, Env.get, getAssoc]

/-- ...and every other name reads past it. A body that declares in a loop
shadows the previous round's local rather than replacing it, which is why an
invariant is stated over what `get` answers and not over the store's shape. -/
theorem Env.get_declare_other {n m : String} {t : Ty} {v : Value}
    (hne : m ≠ n) : (env.declare n t v).get m = env.get m := by
  simp [Env.declare, Env.get, getAssoc, Ne.symm hne]

/-- Reading through an index into a sequence held by a local: in bounds, it
is the element. -/
theorem readPlace_index_var {s : String} {e : Expr} {t : Ty} {m : Nat}
    {items : List Value} {c : Nat} {k : Nat}
    (hs : env.get s = some ⟨t, .seq m items c⟩)
    (he : evalExpr p env e = .ok (.int k)) (hk : k < items.length) :
    readPlace p env (.index (.var s) e) = .ok (items[k]!) := by
  rw [readPlace]
  rw [readPlace_var hs, Res.ok_bind, he]
  simp only [Res.ok_bind, asSeq]
  rw [if_pos ⟨Int.natCast_nonneg k, by simpa using hk⟩]
  simp

/-- Writing through one: in bounds, the local holds the sequence with that
element replaced, and nothing else in the store moves. -/
theorem writePlace_index_var {s : String} {e : Expr} {t : Ty} {m : Nat}
    {items : List Value} {c : Nat} {k : Nat} {v : Value}
    (hs : env.get s = some ⟨t, .seq m items c⟩)
    (he : evalExpr p env e = .ok (.int k)) (hk : k < items.length) :
    writePlace p env (.index (.var s) e) v
      = .ok (env.set s (.seq m (items.set k v) c)) := by
  rw [writePlace]
  rw [readPlace_var hs, Res.ok_bind, he]
  simp only [Res.ok_bind]
  rw [if_pos ⟨Int.natCast_nonneg k, by simpa using hk⟩]
  rw [writePlace_var hs]
  simp

/-- `u32` arithmetic that stays in range is arithmetic: the wrap does
nothing. Every index bump in the artifact leans on this. -/
theorem wrap_u32_eq {v : Int} (h0 : 0 ≤ v) (hlt : v < 4294967296) :
    IntTy.wrap .u32 v = v := by
  have hp : (2 : Int) ^ 32 = 4294967296 := by decide
  simp only [IntTy.wrap, IntTy.width, IntTy.signed, hp,
    Int.emod_eq_of_lt h0 hlt, Bool.false_and]
  rw [if_neg (by simp), if_neg (by omega : ¬v < 0)]

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

/-- A push into a sequence held by a local, all in one motion: the common
case every write-heavy body is made of. -/
theorem evalStmt_push_var {s : String} {t : Ty} {m : Nat} {items : List Value}
    {c : Nat} {v : Value} {e : Expr}
    (hs : env.get s = some ⟨t, .seq m items c⟩)
    (hv : evalExpr p env e = .ok v) (hroom : items.length < m) :
    evalStmt fuel p (.push (.var s) e) env
      = some (.ok (env.set s (.seq m (items ++ [v])
          (if items.length = c then grown m c else c)), .normal)) := by
  rw [evalStmt_push (readPlace_var hs) hv hroom, writePlace_var hs]
  rfl

/-- An assignment to a local, likewise. -/
theorem evalStmt_assign_var {s : String} {t : Ty} {cur v : Value} {e : Expr}
    (hs : env.get s = some ⟨t, cur⟩) (hv : evalExpr p env e = .ok v) :
    evalStmt fuel p (.assign (.var s) e) env
      = some (.ok (env.set s v, .normal)) := by
  rw [evalStmt_assign_ok (readPlace_var hs), hv, Res.ok_bind, writePlace_var hs]
  rfl

/-- An assignment through an index into a sequence held by a local: the
destination resolves first, section 13's order, and in bounds the local ends
up holding the sequence with one element replaced. -/
theorem evalStmt_assign_index_var {s : String} {e ve : Expr} {t : Ty} {m : Nat}
    {items : List Value} {c : Nat} {k : Nat} {val : Value}
    (hs : env.get s = some ⟨t, .seq m items c⟩)
    (he : evalExpr p env e = .ok (.int k)) (hk : k < items.length)
    (hv : evalExpr p env ve = .ok val) :
    evalStmt fuel p (.assign (.index (.var s) e) ve) env
      = some (.ok (env.set s (.seq m (items.set k val) c), .normal)) := by
  rw [evalStmt_assign, resolvePlace, readPlace_index_var hs he hk]
  simp only [Res.bind, Res.ok_bind]
  rw [hv]
  simp only [Res.ok_bind]
  rw [writePlace_index_var hs he hk]
  rfl

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

/-- The same, through a freeze: `len` looks inside, because `asSeq` does. -/
theorem evalExpr_len_frozen {e : Expr} {m : Nat} {items : List Value} {c : Nat}
    (h : evalExpr p env e = .ok (.frozen (.seq m items c))) :
    evalExpr p env (.len e) = .ok (.int items.length) := by
  rw [evalExpr.eq_def]
  simp only []
  rw [h]
  rfl

/-- `cap` reads the room a sequence was given, which the reservation
discipline makes part of the state a simulation tracks. -/
theorem evalExpr_cap {e : Expr} {m : Nat} {items : List Value} {c : Nat}
    (h : evalExpr p env e = .ok (.seq m items c)) :
    evalExpr p env (.cap e) = .ok (.int c) := by
  rw [evalExpr.eq_def]
  simp only []
  rw [h]
  rfl

/-- Boolean negation never needs the operand's type, so neither does the
lemma. -/
theorem evalExpr_not {e : Expr} {b : Bool}
    (h : evalExpr p env e = .ok (.bool b)) :
    evalExpr p env (.un .not e) = .ok (.bool !b) := by
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

/-- Indexing a frozen sequence reads the element as it is stored: the freeze
is on the container, and what wraps the element is decided at the read that
follows, not here. -/
theorem evalExpr_index_frozen {b i : Expr} {m : Nat} {items : List Value}
    {c : Nat} {k : Nat} (hb : evalExpr p env b = .ok (.frozen (.seq m items c)))
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

/-- A pop from a sequence held by one local into another: the last element
out, the sequence one shorter, its capacity kept. -/
theorem evalStmt_pop_var {s d : String} {t td : Ty} {m : Nat}
    {items : List Value} {c : Nat} {last cur : Value} (hne : d ≠ s)
    (hs : env.get s = some ⟨t, .seq m items c⟩)
    (hd : env.get d = some ⟨td, cur⟩)
    (hlast : items.getLast? = some last) :
    evalStmt fuel p (.pop (.var s) (.var d)) env
      = some (.ok ((env.set s (.seq m items.dropLast c)).set d last,
          .normal)) := by
  rw [evalStmt.eq_def]
  simp only []
  rw [readPlace_var hs]
  simp only [Res.ok_bind]
  rw [resolvePlace, readPlace_var hd]
  simp only [Res.bind, Res.ok_bind]
  rw [hlast]
  simp only [Res.ok_bind]
  rw [writePlace_var hs]
  simp only [Res.ok_bind]
  rw [writePlace_var (show (env.set s _).get d = some ⟨td, cur⟩ by
    rw [Env.get_set_other hne]; exact hd)]
  rfl

/-! ## Normalising a chain of writes

The two samples spent most of their lines here, one rewrite per write, and
the shape was always the same: a body writes a few locals, and every later
fact about the store has to walk back past those writes to the one that
answers. So say what a write answers *unconditionally* — an `if` on the two
names rather than a lemma per case — and the walk becomes a `simp only`,
because both names are string literals and the condition decides itself.

`store` is that call, with the base facts of the frame passed in. It is not
deep: it is the difference between forty lines and one. -/

/-- Reading a local after a write to one, whichever it was. -/
theorem Env.get_set {n m : String} {v : Value} :
    (env.set n v).get m =
      if m = n then (env.get n).map (fun s => ⟨s.ty, v⟩) else env.get m := by
  split <;> rename_i h
  · subst h
    cases hg : env.get m with
    | none => rw [Env.set, hg]; simp [hg]
    | some s => rw [Env.get_set_self hg]; simp
  · exact Env.get_set_other h

/-- The same for a declaration, which shadows rather than replaces. -/
theorem Env.get_declare {n m : String} {t : Ty} {v : Value} :
    (env.declare n t v).get m = if m = n then some ⟨t, v⟩ else env.get m := by
  simp only [Env.declare, Env.get, getAssoc]
  split <;> rename_i h
  · rw [if_pos h.symm]
  · rw [if_neg (fun hh => h hh.symm)]

/-- Reading through a local place, without knowing yet that the local is
there: the answer is whatever the store says, and normalising the store
decides it. -/
theorem readPlace_var_eq {n : String} :
    readPlace p env (.var n)
      = match env.get n with
        | some s => .ok s.value
        | none => .bug s!"no local named {n}" := by
  rw [readPlace.eq_def]
  simp only []
  cases env.get n <;> rfl

theorem evalExpr_var_eq {n : String} :
    evalExpr p env (.var n)
      = match env.get n with
        | some s => .ok s.value
        | none => .bug s!"no local named {n}" := by
  rw [evalExpr.eq_def]
  simp only []
  cases env.get n <;> rfl

/-- Writing to a local that is there. Stated on `isSome` rather than on the
slot so that normalising the store discharges it. -/
theorem writePlace_var_isSome {n : String} {v : Value}
    (h : (env.get n).isSome = true) :
    writePlace p env (.var n) v = .ok (env.set n v) := by
  cases hg : env.get n with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some s => exact writePlace_var hg

/-- Answer `Env.get` through a chain of writes, and the reads and writes that
walk it. The bracket takes whatever the frame's base facts are — the
parameter bindings, or the previous round's invariant — and the names of the
intermediate stores, spelled `← henv3` when a proof has named them. -/
syntax "store" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| store) =>
      `(tactic| simp only [Env.get_set, Env.get_declare, Option.map_some,
          Option.isSome_some, String.reduceEq, reduceIte, writePlace_var_isSome,
          readPlace_var_eq, evalExpr_var_eq, Res.ok_bind])
  | `(tactic| store $loc:location) =>
      `(tactic| simp only [Env.get_set, Env.get_declare, Option.map_some,
          Option.isSome_some, String.reduceEq, reduceIte, writePlace_var_isSome,
          readPlace_var_eq, evalExpr_var_eq, Res.ok_bind] $loc)
  | `(tactic| store [$xs,*]) =>
      `(tactic| simp only [Env.get_set, Env.get_declare, Option.map_some,
          Option.isSome_some, String.reduceEq, reduceIte, writePlace_var_isSome,
          readPlace_var_eq, evalExpr_var_eq, Res.ok_bind, $xs,*])
  | `(tactic| store [$xs,*] $loc:location) =>
      `(tactic| simp only [Env.get_set, Env.get_declare, Option.map_some,
          Option.isSome_some, String.reduceEq, reduceIte, writePlace_var_isSome,
          readPlace_var_eq, evalExpr_var_eq, Res.ok_bind, $xs,*] $loc)

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

/-- The other direction, which a caller's proof steps with: a callee whose
contract is known in `Runs` makes its `call` statement a store update. The
callee's frame is abstracted into the outs it left — some frame produced
them, and the write-back below reads nothing else out of it. The budget is
existential, so no caller quotes the callee's. -/
theorem evalStmt_call_runs {fn : String} {callee : Func} {args : List Arg}
    {dest : Option Place} {argVals outs : List Value} {ret : Option Value}
    (hf : p.func? fn = some callee)
    (hargs : evalArgs p env callee.params args = .ok argVals)
    (hr : Runs p fn argVals (outs, ret)) :
    ∃ n inner, outsOf callee.params inner = outs ∧
      evalStmt n p (.call fn args dest) env
        = some (do
            let env' ← writeBack p inner callee.params args env
            match dest, ret with
            | none, _ => .ok (env', .normal)
            | some d, some v => do
                let env'' ← writePlace p env' d v
                .ok (env'', .normal)
            | some _, none =>
                .bug s!"{fn} returned nothing into a destination") := by
  obtain ⟨n, hn⟩ := hr
  match n with
  | 0 => rw [callFunc.eq_def] at hn; exact absurd hn (by simp)
  | k + 1 =>
      rw [callFunc.eq_def] at hn
      simp only [] at hn
      rw [hf] at hn
      simp only [] at hn
      cases hb : evalStmts k p callee.body (bindParams callee.params argVals) with
      | none => rw [hb] at hn; exact absurd hn (by simp)
      | some res =>
          rw [hb] at hn
          match res with
          | .trap c => exact absurd hn (by simp)
          | .bug w => exact absurd hn (by simp)
          | .ok (inner, flow) =>
              simp only [Option.some.injEq, Res.ok.injEq, Prod.mk.injEq] at hn
              obtain ⟨houts, hret⟩ := hn
              refine ⟨k + 1, inner, houts, ?_⟩
              rw [evalStmt.eq_def]
              simp only []
              rw [hf]
              simp only []
              rw [hargs]
              simp only []
              rw [hb]
              cases flow <;> (subst hret; rfl)

/-- Where a call leaves the caller's store, said in terms of the values the
callee left rather than the frame it left them in: each `inout` argument's
place takes the matching out, in declaration order. Same recursion as
`writeBack`, and the point of it is that a caller's proof can normalise this
with `store` while `writeBack` keeps a frame it knows nothing about. -/
def writeOuts (p : Program) :
    List Param → List Arg → List Value → Env → Res Env
  | [], [], _, env => .ok env
  | par :: ps, a :: as, v :: vs, env =>
      match par.inout, a with
      | true, .inoutArg pl => do
          let env' ← writePlace p env pl v
          writeOuts p ps as vs env'
      | _, _ => writeOuts p ps as vs env
  | _, _, _, _ => .bug "a call was given the wrong number of arguments"

/-- The one thing an out list does not say by itself. `outsOf` answers
`false` both for a parameter the callee left holding `false` and for one the
callee somehow lost, and `writeBack` treats those two differently. Nothing
in TIR loses a name, but proving that is a walk over the whole interpreter,
so the caller carries this instead.

Read this as the non-`false` fast path rather than as a presence witness.
It is free exactly when the values landing in `inout` position cannot be
`false` — integers, which is what every meter and every size is — and it is
*unavailable* for a callee that legitimately writes `false` back through a
boolean `inout` parameter. Fourteen of the eighty functions the gate 5
ledger owes have one, `sat_add`, `charge_call` and `cert_install` among
them, so the general case wants either the name-preservation theorem or a
call step stated over the callee's frame rather than over its outs. -/
def OutsPresent : List Param → List Value → Prop
  | [], _ => True
  | par :: ps, v :: vs =>
      (par.inout = true → v ≠ .bool false) ∧ OutsPresent ps vs
  | _ :: _, [] => False

theorem writeBack_eq_writeOuts {inner : Env} :
    ∀ (params : List Param) (args : List Arg) (env : Env),
      OutsPresent params (outsOf params inner) →
      writeBack p inner params args env
        = writeOuts p params args (outsOf params inner) env := by
  intro params
  induction params with
  | nil => intro args env _; cases args <;> rfl
  | cons par ps ih =>
      obtain ⟨pname, pty, pinout⟩ := par
      intro args env hp
      match args with
      | [] => rfl
      | a :: as =>
          have houts : outsOf (⟨pname, pty, pinout⟩ :: ps) inner
              = (match inner.get pname with
                 | some s => s.value
                 | none => Value.bool false) :: outsOf ps inner := rfl
          rw [houts] at hp ⊢
          simp only [OutsPresent] at hp
          obtain ⟨hp1, hp2⟩ := hp
          match pinout, a with
          | false, .inArg _ => exact ih as env hp2
          | false, .inoutArg _ => exact ih as env hp2
          | true, .inArg _ => exact ih as env hp2
          | true, .inoutArg pl =>
              show (match inner.get pname with
                    | none => Res.bug s!"the callee lost {pname}"
                    | some s => do
                        let e ← writePlace p env pl s.value
                        writeBack p inner ps as e)
                 = (do
                     let e ← writePlace p env pl
                       (match inner.get pname with
                        | some s => s.value
                        | none => Value.bool false)
                     writeOuts p ps as (outsOf ps inner) e)
              cases hg : inner.get pname with
              | none =>
                  exact absurd (show (match inner.get pname with
                    | some s => s.value
                    | none => Value.bool false) = Value.bool false by rw [hg])
                    (hp1 rfl)
              | some s =>
                  simp only []
                  cases hw : writePlace p env pl s.value with
                  | ok e => simp only [Res.ok_bind]; exact ih as e hp2
                  | trap c => rfl
                  | bug w => rfl

/-- A call, stepped. Given the callee's contract in `Runs`, the statement is
the write-back of the outs and then the destination — and nothing of the
callee's frame survives into the conclusion, which is what lets the caller's
proof stay inside the store algebra `store` normalises. -/
theorem evalStmt_call_outs {fn : String} {callee : Func} {args : List Arg}
    {dest : Option Place} {argVals outs : List Value} {ret : Option Value}
    (hf : p.func? fn = some callee)
    (hargs : evalArgs p env callee.params args = .ok argVals)
    (hr : Runs p fn argVals (outs, ret))
    (hpres : OutsPresent callee.params outs) :
    ∃ n, evalStmt n p (.call fn args dest) env
      = some (do
          let env' ← writeOuts p callee.params args outs env
          match dest, ret with
          | none, _ => .ok (env', .normal)
          | some d, some v => do
              let env'' ← writePlace p env' d v
              .ok (env'', .normal)
          | some _, none =>
              .bug s!"{fn} returned nothing into a destination") := by
  obtain ⟨n, inner, houts, hcall⟩ := evalStmt_call_runs hf hargs hr
  refine ⟨n, ?_⟩
  rw [hcall, writeBack_eq_writeOuts (inner := inner) callee.params args env
    (by rw [houts]; exact hpres), houts]

end Pcrevera.Tir
