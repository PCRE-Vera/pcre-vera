import Pcrevera.Tir.Interp

/-!
# Statements, calls, and the judgment gate 5 is stated in

Expressions need no budget: they recurse into their own subterms and stop.
Statements do, because a `while` runs until its condition says otherwise and a
call runs another function's body, and neither is a fact about the syntax.

So the evaluator takes fuel and answers `none` when it runs out. That would
leak into every simulation lemma if the lemmas quoted it, so they do not:
`Runs` is the judgment, an existential over budgets, and two theorems make it
behave like the evaluation everyone actually wants. `runs_stable` says a
larger budget answers the same, and `runs_unique` says `Runs` relates a call
to at most one outcome. A caller's lemma then composes with a callee's by
transitivity rather than by adding budgets.

The loop variants are not the termination argument here, and they are not
ignored either: they are what a run-time check reads in `tir/interp.py`, and
what a future proof would use to bound the fuel a particular loop needs.
-/

namespace Pcrevera.Tir

/-- Where a statement left control, TIR-SPEC.md section 9. -/
inductive Flow where
  | normal
  | brk
  | cont
  | ret (value : Option Value)
deriving Repr, Inhabited

/-- The arguments of one call, evaluated left to right: an `in` argument is
its expression's value, an `inout` one is what its place holds now. -/
def evalArgs (p : Program) (env : Env) :
    List Param → List Arg → Res (List Value)
  | [], [] => .ok []
  | par :: ps, a :: as => do
      let v ←
        match par.inout, a with
        | false, .inArg e => evalExpr p env e
        | true, .inoutArg pl => readPlace p env pl
        | _, _ => .bug s!"the argument for {par.name} does not match its mode"
      let vs ← evalArgs p env ps as
      .ok (v :: vs)
  | _, _ => .bug "a call was given the wrong number of arguments"

/-- The callee's frame: one slot per parameter, in declaration order. -/
def bindParams : List Param → List Value → Env
  | [], _ => []
  | par :: ps, v :: vs => (par.name, ⟨par.ty, v⟩) :: bindParams ps vs
  | par :: ps, [] => (par.name, ⟨par.ty, .bool false⟩) :: bindParams ps []

/-- Copying out: every `inout` argument's place takes what the callee left in
the matching parameter. Sound because V-022 forbids one argument's writable
footprint from overlapping another's reachable one, so writing them back one
at a time cannot be told from having written through references. -/
def writeBack (p : Program) (callee : Env) :
    List Param → List Arg → Env → Res Env
  | [], [], env => .ok env
  | par :: ps, a :: as, env =>
      match par.inout, a with
      | true, .inoutArg pl =>
          match callee.get par.name with
          | none => .bug s!"the callee lost {par.name}"
          | some s => do
              let env' ← writePlace p env pl s.value
              writeBack p callee ps as env'
      | _, _ => writeBack p callee ps as env
  | _, _, _ => .bug "a call was given the wrong number of arguments"

/-- What a push grows a sequence to, section 11.2: four, then doubling, never
past the declared maximum. -/
def grown (max capacity : Nat) : Nat := min max (Nat.max 4 (2 * capacity))

/-- Resolving a place without reading through it: the index expressions left
to right, each bounds-checked as it is resolved.

Section 13 pins the order a statement resolves its parts in, and it puts the
*destination* first — so a statement whose destination is out of bounds
answers T-01 even when its source would have trapped too. Resolution is
reading with the value thrown away, because reading a place traps in exactly
the places resolving it does. -/
def resolvePlace (p : Program) (env : Env) (pl : Place) : Res Unit :=
  (readPlace p env pl).bind fun _ => .ok ()

mutual

/-- A body, statement by statement, stopping at the first that leaves. -/
def evalStmts (fuel : Nat) (p : Program) (body : List Stmt) (env : Env) :
    Option (Res (Env × Flow)) :=
  match body with
  | [] => some (.ok (env, .normal))
  | s :: rest =>
      match evalStmt fuel p s env with
      | none => none
      | some (.trap c) => some (.trap c)
      | some (.bug w) => some (.bug w)
      | some (.ok (env', .normal)) => evalStmts fuel p rest env'
      | some (.ok (env', f)) => some (.ok (env', f))
termination_by (fuel, sizeOf body)

def evalStmt (fuel : Nat) (p : Program) (s : Stmt) (env : Env) :
    Option (Res (Env × Flow)) :=
  match s with
  | .letS name t init =>
      match init with
      | none =>
          match zero p t with
          | none => some (.bug "a local whose type has no zero value")
          | some v => some (.ok (env.declare name t v, .normal))
      | some e =>
          match evalExpr p env e with
          | .ok v => some (.ok (env.declare name t v, .normal))
          | .trap c => some (.trap c)
          | .bug w => some (.bug w)
  | .assign place value =>
      some (do
        let _ ← resolvePlace p env place
        let v ← evalExpr p env value
        let env' ← writePlace p env place v
        .ok (env', .normal))
  | .take dest src =>
      some (do
        let _ ← resolvePlace p env dest
        let moved ← readPlace p env src
        match placeTy p env src with
        | none => .bug "a take from a place with no type"
        | some t =>
            match zero p t with
            | none => .bug "a take from a place with no zero value"
            | some z => do
                let env' ← writePlace p env src z
                let env'' ← writePlace p env' dest moved
                .ok (env'', .normal))
  | .swap a b =>
      some (do
        let x ← readPlace p env a
        let y ← readPlace p env b
        let env' ← writePlace p env a y
        let env'' ← writePlace p env' b x
        .ok (env'', .normal))
  | .copy dest src =>
      some (do
        let _ ← resolvePlace p env dest
        let v ← evalExpr p env src
        let source := match v with | .frozen inner => inner | _ => v
        let env' ← writePlace p env dest (deepCopy source)
        .ok (env', .normal))
  | .freeze dest src =>
      some (do
        let _ ← resolvePlace p env dest
        let moved ← readPlace p env src
        match placeTy p env src with
        | none => .bug "a freeze of a place with no type"
        | some t =>
            match zero p t with
            | none => .bug "a freeze of a place with no zero value"
            | some z => do
                let env' ← writePlace p env src z
                let env'' ← writePlace p env' dest (.frozen moved)
                .ok (env'', .normal))
  | .push seq value =>
      some (do
        let target ← readPlace p env seq
        let v ← evalExpr p env value
        match target with
        | .seq m items c =>
            if items.length ≥ m then .trap "T-05"
            else
              let c := if items.length = c then grown m c else c
              do
                let env' ← writePlace p env seq (.seq m (items ++ [v]) c)
                .ok (env', .normal)
        | _ => .bug "a push met a value that is not a sequence")
  | .pop seq dest =>
      some (do
        let target ← readPlace p env seq
        let _ ← resolvePlace p env dest
        match target with
        | .seq m items c =>
            match items.getLast? with
            | none => .trap "T-02"
            | some last => do
                let env' ← writePlace p env seq (.seq m (items.dropLast) c)
                let env'' ← writePlace p env' dest last
                .ok (env'', .normal)
        | _ => .bug "a pop met a value that is not a sequence")
  | .truncate seq length =>
      some (do
        let target ← readPlace p env seq
        let n ← evalExpr p env length
        match target, n with
        | .seq m items c, .int wanted =>
            if wanted < 0 ∨ (items.length : Int) < wanted then .trap "T-03"
            else do
              let env' ← writePlace p env seq (.seq m (items.take wanted.toNat) c)
              .ok (env', .normal)
        | _, _ => .bug "a truncate met the wrong shape")
  | .reserve seq capacity =>
      some (do
        let target ← readPlace p env seq
        let n ← evalExpr p env capacity
        match target, n with
        | .seq m items c, .int wanted =>
            if (m : Int) < wanted then .trap "T-04"
            else do
              let env' ← writePlace p env seq
                (.seq m items (Nat.max c wanted.toNat))
              .ok (env', .normal)
        | _, _ => .bug "a reserve met the wrong shape")
  | .ifS cond thenB elseB =>
      match evalExpr p env cond with
      | .trap c => some (.trap c)
      | .bug w => some (.bug w)
      | .ok (.bool true) => evalStmts fuel p thenB env
      | .ok (.bool false) => evalStmts fuel p elseB env
      | .ok _ => some (.bug "an if met a condition that is not a boolean")
  | .whileS cond _ body => evalWhile fuel p cond body env
  | .switchS value arms dflt =>
      match evalExpr p env value with
      | .trap c => some (.trap c)
      | .bug w => some (.bug w)
      | .ok (.tag _ variant) => evalArms fuel p variant arms dflt env
      | .ok _ => some (.bug "a switch met a value that is not an enum")
  | .breakS => some (.ok (env, .brk))
  | .continueS => some (.ok (env, .cont))
  | .returnS value =>
      match value with
      | none => some (.ok (env, .ret none))
      | some e =>
          match evalExpr p env e with
          | .ok v => some (.ok (env, .ret (some v)))
          | .trap c => some (.trap c)
          | .bug w => some (.bug w)
  | .call fn args dest =>
      match fuel with
      | 0 => none
      | f + 1 =>
          match p.func? fn with
          | none => some (.bug s!"no function named {fn}")
          | some callee =>
              match evalArgs p env callee.params args with
              | .trap c => some (.trap c)
              | .bug w => some (.bug w)
              | .ok vals =>
                  match evalStmts f p callee.body (bindParams callee.params vals) with
                  | none => none
                  | some (.trap c) => some (.trap c)
                  | some (.bug w) => some (.bug w)
                  | some (.ok (inner, flow)) =>
                      let result := match flow with | .ret v => v | _ => none
                      some (do
                        let env' ← writeBack p inner callee.params args env
                        match dest, result with
                        | none, _ => .ok (env', .normal)
                        | some d, some v => do
                            let env'' ← writePlace p env' d v
                            .ok (env'', .normal)
                        | some _, none =>
                            .bug s!"{fn} returned nothing into a destination")
termination_by (fuel, sizeOf s)

/-- One loop, one round of fuel. A `break` leaves normally, a `continue` goes
round again, a `return` climbs out. -/
def evalWhile (fuel : Nat) (p : Program) (cond : Expr) (body : List Stmt)
    (env : Env) : Option (Res (Env × Flow)) :=
  match fuel with
  | 0 => none
  | f + 1 =>
      match evalExpr p env cond with
      | .trap c => some (.trap c)
      | .bug w => some (.bug w)
      | .ok (.bool false) => some (.ok (env, .normal))
      | .ok (.bool true) =>
          match evalStmts f p body env with
          | none => none
          | some (.trap c) => some (.trap c)
          | some (.bug w) => some (.bug w)
          | some (.ok (env', .brk)) => some (.ok (env', .normal))
          | some (.ok (env', .ret v)) => some (.ok (env', .ret v))
          | some (.ok (env', _)) => evalWhile f p cond body env'
      | .ok _ => some (.bug "a while met a condition that is not a boolean")
termination_by (fuel, sizeOf body)

/-- The arms in order, then the default. A validated switch covers every
variant, so a missing default is a program the validator refused. -/
def evalArms (fuel : Nat) (p : Program) (variant : String)
    (arms : List (String × List Stmt)) (dflt : Option (List Stmt)) (env : Env) :
    Option (Res (Env × Flow)) :=
  match arms with
  | [] =>
      match dflt with
      | none => some (.bug s!"no arm for {variant} and no default")
      | some body => evalStmts fuel p body env
  | (name, body) :: rest =>
      if name = variant then evalStmts fuel p body env
      else evalArms fuel p variant rest dflt env
termination_by (fuel, sizeOf arms + sizeOf dflt)

end

/-- One call, from outside: the argument values in parameter order, and what
comes back — every parameter's final value, so a caller can read its `inout`
ones, and the returned value if there is one. -/
def callFunc (fuel : Nat) (p : Program) (fn : String) (args : List Value) :
    Option (Res (List Value × Option Value)) :=
  match fuel with
  | 0 => none
  | f + 1 =>
      match p.func? fn with
      | none => some (.bug s!"no function named {fn}")
      | some callee =>
          match evalStmts f p callee.body (bindParams callee.params args) with
          | none => none
          | some (.trap c) => some (.trap c)
          | some (.bug w) => some (.bug w)
          | some (.ok (inner, flow)) =>
              let outs := callee.params.map fun par =>
                match inner.get par.name with
                | some s => s.value
                | none => Value.bool false
              some (.ok (outs, match flow with | .ret v => v | _ => none))

/-! ## The judgment

Everything gate 5 proves is stated in `Runs`, so that no lemma quotes a fuel
bound and no composition has to add two together. -/

def Runs (p : Program) (fn : String) (args : List Value)
    (out : List Value × Option Value) : Prop :=
  ∃ n, callFunc n p fn args = some (.ok out)

end Pcrevera.Tir
