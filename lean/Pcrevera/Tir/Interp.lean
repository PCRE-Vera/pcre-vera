import Pcrevera.Tir.Syntax

/-!
# The definitional interpreter (I-1, second half)

TIR-SPEC.md read as a function rather than as prose. It follows the
specification literally rather than efficiently, the way `tir/interp.py` does:
saturation is written as the pre-check section 6.7 states, evaluation is left
to right because the spec says which trap wins, and a checked operation
answers with the trap code section 12 names.

Two modelling decisions are worth stating, because the rest of layer I is
built on them.

**Totality is earned through fuel.** TIR carries a variant on every `while`,
so evaluation could in principle be well-founded. But a variant is an
expression over the mutable store, and its descent is a fact about the loop's
invariant rather than about the syntax — so defining the interpreter that way
would make it wait on one hand proof per loop, and a single unproved variant
would leave the whole artifact uninterpretable. Fuel instead: the interpreter
is total by construction, `none` means the budget ran out, and `Runs` hides
the budget again behind an existential that is stable and deterministic.

**A call copies in and copies out.** The Python interpreter passes an `inout`
argument by reference; here the caller reads the argument places, the callee
runs on a frame of its own, and the caller writes the results back. The two
agree exactly because V-022 forbids one argument's writable footprint from
overlapping another's reachable one — which is what the whole linearity
discipline is for, and the reason this is a simplification rather than a
change.
-/

namespace Pcrevera.Tir

/-- The saturation point of the `counter` type, TIR-SPEC.md section 3.1. -/
def cap : Int := 2 ^ 53 - 1

/-- The portable allocation ceiling, section 11.1. -/
def ceiling : Nat := 2 ^ 31 - 1

/-- A runtime value. Sequences carry the maximum their type declares, because
a push past it is a trap and nothing else remembers the number. -/
inductive Value where
  | bool (b : Bool)
  | int (v : Int)
  | seq (max : Nat) (items : List Value) (capacity : Nat)
  | frozen (inner : Value)
  | tag (enum variant : String)
  | struct (ty : String) (fields : List (String × Value))
deriving Repr, Inhabited, BEq

/-- What a checked operation answers with, section 12. `bug` is not a TIR
outcome: it is what a program the validator would have refused evaluates to,
kept apart from a real trap so that no proof can confuse the two. -/
inductive Res (α : Type) where
  | ok (a : α)
  | trap (code : String)
  | bug (why : String)
deriving Repr, BEq

def Res.bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .trap c, _ => .trap c
  | .bug w, _ => .bug w

instance : Monad Res where
  pure := Res.ok
  bind := Res.bind

/-- A local: its declared type, which the width rules read, and its value. -/
structure Slot where
  ty : Ty
  value : Value
deriving Repr, Inhabited, BEq

abbrev Env := List (String × Slot)

def Env.get (env : Env) (name : String) : Option Slot := getAssoc name env

def Env.set (env : Env) (name : String) (v : Value) : Env :=
  match env.get name with
  | some s => setAssoc name { s with value := v } env
  | none => env

def Env.declare (env : Env) (name : String) (t : Ty) (v : Value) : Env :=
  (name, ⟨t, v⟩) :: env

/-! ## Types, and the two questions asked of one -/

def Ty.unfrozen : Ty → Ty
  | .frozen t => t
  | t => t

def Ty.intTy? : Ty → Option IntTy
  | .int t => some t
  | _ => none

def Ty.elem? : Ty → Option Ty
  | .bytes => some (.int .u8)
  | .vec e _ => some e
  | .frozen .bytes => some (.int .u8)
  | .frozen (.vec e _) => some e
  | _ => none

/-- Is this type heap-backed, so that it moves rather than copies? Section
3.3. The fuel is the struct nesting depth; the validator refuses a recursive
struct, so `p.structs.length` is always enough. -/
def isLinearGo : Nat → Program → Ty → Bool
  | 0, _, _ => false
  | _ + 1, _, .bytes => true
  | _ + 1, _, .vec _ _ => true
  | n + 1, p, .struct name =>
      match p.struct? name with
      | none => false
      | some d => d.fields.any fun f => isLinearGo n p f.ty
  | _ + 1, _, _ => false

def isLinear (p : Program) (t : Ty) : Bool := isLinearGo (p.structs.length + 1) p t

def IntTy.width : IntTy → Nat
  | .u8 => 8
  | .i32 => 32
  | .u32 => 32
  | .counter => 0

def IntTy.signed : IntTy → Bool
  | .i32 => true
  | _ => false

/-- Reduce mod 2^w and read the result back in the type, section 6.6.
`counter` never wraps — saturation is a different rule — so it is left alone
here and handled where the operators are. -/
def IntTy.wrap (t : IntTy) (v : Int) : Int :=
  match t with
  | .counter => v
  | _ =>
      let w := t.width
      let m : Int := 2 ^ w
      let r := v % m
      let r := if r < 0 then r + m else r
      if t.signed && r ≥ 2 ^ (w - 1) then r - m else r

/-- The unsigned representative of a value in its type: the bit pattern the
bitwise operators work on. -/
def IntTy.urep (t : IntTy) (v : Int) : Nat :=
  match t with
  | .counter => v.toNat
  | _ => ((v % (2 ^ t.width) + 2 ^ t.width) % (2 ^ t.width)).toNat

/-! ## Zero values, section 4.1

The fuel is the struct nesting depth. A recursive struct has no zero value at
all, which is why the validator refuses one, and why `p.structs.length + 1` is
always enough for a program that passed. -/

mutual

def zeroVal (n : Nat) (p : Program) (t : Ty) : Option Value :=
  match t with
  | .bool => some (.bool false)
  | .int _ => some (.int 0)
  | .bytes => some (.seq ceiling [] 0)
  | .vec _ m => some (.seq m [] 0)
  | .frozen inner =>
      match n with
      | 0 => none
      | n + 1 => (zeroVal n p inner).map .frozen
  | .enum name =>
      match p.enum? name with
      | some ⟨_, v :: _⟩ => some (.tag name v)
      | _ => none
  | .struct name =>
      match n with
      | 0 => none
      | n + 1 =>
          match p.struct? name with
          | none => none
          | some d => (zeroFields n p d.fields).map (Value.struct name)
termination_by (n, 0)

def zeroFields (n : Nat) (p : Program) (fields : List Field) :
    Option (List (String × Value)) :=
  match fields with
  | [] => some []
  | f :: rest => do
      let v ← zeroVal n p f.ty
      let vs ← zeroFields n p rest
      some ((f.name, v) :: vs)
termination_by (n, fields.length + 1)

end

/-- The zero value at the depth the program's own struct table allows. -/
def zero (p : Program) (t : Ty) : Option Value := zeroVal (p.structs.length + 1) p t

/-! ## Copies

A copy is deep, and every mutable sequence it reaches comes out with its
capacity equal to its length. A frozen value is shared rather than
duplicated, which is what freezing bought and what keeps `cap` on it the same
number afterwards. -/

mutual

def deepCopy : Value → Value
  | .seq m items _ => let cs := deepList items; .seq m cs cs.length
  | .struct t fields => .struct t (deepFields fields)
  | v => v

def deepList : List Value → List Value
  | [] => []
  | v :: rest => deepCopy v :: deepList rest

def deepFields : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: rest => (k, deepCopy v) :: deepFields rest

end

/-! ## Constant values

The recursion here follows the value, not the type, except through `frozen`
where the type shrinks and the value does not — which is why the measure is
the pair. Looking a field up in a struct constant reaches a strictly smaller
value, and `getAssoc_lt` is the lemma that says so. -/

theorem getAssoc_lt {α : Type} [SizeOf α] {k : String} :
    ∀ {l : List (String × α)} {v : α}, getAssoc k l = some v → sizeOf v < sizeOf l := by
  intro l
  induction l with
  | nil => intro v h; rw [getAssoc] at h; exact absurd h (by simp)
  | cons e rest ih =>
      intro v h
      obtain ⟨key, val⟩ := e
      rw [getAssoc] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega
      · have := ih h
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega

mutual

def constValue (p : Program) (t : Ty) (v : ConstValue) : Option Value :=
  match t, v with
  | .frozen inner, v => (constValue p inner v).map .frozen
  | _, .int n => some (.int n)
  | _, .bool b => some (.bool b)
  | .enum name, .variant w => some (.tag name w)
  | _, .bytes data =>
      let items := data.map fun b => Value.int b.toNat
      some (.seq ceiling items items.length)
  | .vec e m, .elems items => do
      let vs ← constList p e items
      some (.seq m vs vs.length)
  | .struct name, .fields entries => do
      let d ← p.struct? name
      let vs ← constFields p d.fields entries
      some (.struct name vs)
  | _, _ => none
termination_by (sizeOf v, sizeOf t)

def constList (p : Program) (t : Ty) (items : List ConstValue) :
    Option (List Value) :=
  match items with
  | [] => some []
  | v :: rest => do
      let x ← constValue p t v
      let xs ← constList p t rest
      some (x :: xs)
termination_by (sizeOf items, 0)

def constFields (p : Program) (fields : List Field)
    (given : List (String × ConstValue)) : Option (List (String × Value)) :=
  match fields with
  | [] => some []
  | f :: rest =>
      match hraw : getAssoc f.name given with
      | none => none
      | some raw => do
          let v ← constValue p f.ty raw
          let vs ← constFields p rest given
          some ((f.name, v) :: vs)
termination_by (sizeOf given, fields.length)
decreasing_by
  · have := getAssoc_lt hraw
    exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by simp)

end

/-! ## The static types the width rules need -/

def fieldTy (p : Program) (base : Ty) (name : String) : Option Ty := do
  match base.unfrozen with
  | .struct s => do
      let d ← p.struct? s
      let f ← d.field? name
      some f.ty
  | _ => none

def typeOf (p : Program) (env : Env) : Expr → Option Ty
  | .litInt t _ => some (.int t)
  | .litBool _ => some .bool
  | .len _ | .cap _ => some (.int .u32)
  | .cmp _ _ _ | .logical _ _ _ => some .bool
  | .un op arg => if op = .not then some .bool else typeOf p env arg
  | .shift _ arg _ => typeOf p env arg
  | .bin _ left _ => typeOf p env left
  | .divrem _ left _ _ => typeOf p env left
  | .cast t _ => some t
  | .var name => (env.get name).map Slot.ty
  | .constRef name => (p.const? name).map ConstDecl.ty
  | .field base name => do fieldTy p (← typeOf p env base) name
  | .index base _ => do (← typeOf p env base).elem?
  | .structVal t _ => some (.struct t)
  | .enumVal t _ => some (.enum t)

/-! ## Expressions -/

def asSeq : Value → Option (Nat × List Value × Nat)
  | .seq m items c => some (m, items, c)
  | .frozen (.seq m items c) => some (m, items, c)
  | _ => none

def unary (op : UnOp) (t : Option IntTy) (v : Value) : Res Value :=
  match op, v with
  | .not, .bool b => .ok (.bool !b)
  | .neg, .int x => match t with
      | some ty => .ok (.int (ty.wrap (-x)))
      | none => .bug "neg on a value with no integer type"
  | .bnot, .int x => match t with
      | some ty => .ok (.int (ty.wrap (-x - 1)))
      | none => .bug "bnot on a value with no integer type"
  | _, _ => .bug "a unary operator met the wrong shape"

/-- Section 6.7: `counter` saturates, and the check comes before the
operation rather than after it, so nothing ever forms a number it could not
hold. -/
def satBin (op : BinOp) (a b : Int) : Res Value :=
  match op with
  | .add => .ok (.int (if a > cap - b then cap else a + b))
  | .sub => .ok (.int (if a < b then 0 else a - b))
  | .mul =>
      if a = 0 || b = 0 then .ok (.int 0)
      else .ok (.int (if a > cap / b then cap else a * b))
  | _ => .bug "counter has no bitwise operator"

def binary (op : BinOp) (t : Option IntTy) (a b : Value) : Res Value :=
  match a, b with
  | .int x, .int y =>
      match t with
      | none => .bug "a binary operator met a value with no integer type"
      | some .counter => satBin op x y
      | some ty =>
          match op with
          | .add => .ok (.int (ty.wrap (x + y)))
          | .sub => .ok (.int (ty.wrap (x - y)))
          | .mul => .ok (.int (ty.wrap (x * y)))
          -- Bitwise operations run on the two's-complement patterns, which
          -- is what the unsigned representative of each operand carries.
          | .and => .ok (.int (ty.wrap (ty.urep x &&& ty.urep y : Nat)))
          | .or => .ok (.int (ty.wrap (ty.urep x ||| ty.urep y : Nat)))
          | .xor => .ok (.int (ty.wrap (ty.urep x ^^^ ty.urep y : Nat)))
  | _, _ => .bug "a binary operator met the wrong shape"

def compare (op : CmpOp) (a b : Value) : Res Value :=
  match a, b with
  | .tag _ v, .tag _ w =>
      match op with
      | .eq => .ok (.bool (v = w))
      | .ne => .ok (.bool (v ≠ w))
      | _ => .bug "enum values are only compared for equality"
  | .bool x, .bool y =>
      match op with
      | .eq => .ok (.bool (x = y))
      | .ne => .ok (.bool (x ≠ y))
      | _ => .bug "booleans are only compared for equality"
  | .int x, .int y =>
      .ok (.bool (match op with
        | .eq => x = y | .ne => x ≠ y | .lt => x < y
        | .le => x ≤ y | .gt => x > y | .ge => x ≥ y))
  | _, _ => .bug "a comparison met the wrong shape"

def divrem (op : DivOp) (t : Option IntTy) (a b fallback : Value) : Res Value :=
  match a, b with
  | .int x, .int y =>
      if y = 0 then .ok fallback
      else
        let q := (x.natAbs / y.natAbs : Nat)
        let q : Int := if (x < 0) != (y < 0) then -(q : Int) else (q : Int)
        match op with
        | .rem => .ok (.int (x - y * q))
        | .div =>
            match t with
            | some .counter => .ok (.int q)
            | some ty => .ok (.int (ty.wrap q))
            | none => .bug "a division met a value with no integer type"
  | _, _ => .bug "a division met the wrong shape"

def shiftOp (op : ShiftOp) (t : Option IntTy) (v : Value) (n : Nat) : Res Value :=
  match v with
  | .int x =>
      match op with
      | .shl =>
          match t with
          | some ty => .ok (.int (ty.wrap (x * 2 ^ n)))
          | none => .bug "a shift met a value with no integer type"
      -- `shr` is offered only on unsigned types and `sar` only on i32, so an
      -- arithmetic shift is right in both cases.
      | .shr | .sar => .ok (.int (x >>> n))
  | _ => .bug "a shift met the wrong shape"

def castTo (t : Ty) (v : Value) : Res Value :=
  let asInt : Option Int := match v with
    | .int x => some x
    | .bool b => some (if b then 1 else 0)
    | _ => none
  match asInt, t with
  | some x, .int .counter => .ok (.int (max 0 x))
  | some x, .int ty => .ok (.int (ty.wrap x))
  | _, _ => .bug "a cast met the wrong shape"

mutual

def evalExpr (p : Program) (env : Env) : Expr → Res Value
  | .litInt _ v => .ok (.int v)
  | .litBool b => .ok (.bool b)
  | .var name =>
      match env.get name with
      | some s => .ok s.value
      | none => .bug s!"no local named {name}"
  | .constRef name =>
      match p.const? name with
      | none => .bug s!"no constant named {name}"
      | some d =>
          match constValue p d.ty d.value with
          | some v => .ok v
          | none => .bug s!"the constant {name} does not match its type"
  | .field base name => do
      let container ← evalExpr p env base
      match container with
      | .frozen (.struct t fields) =>
          match getAssoc name fields, fieldTy p (.struct t) name with
          | some v, some declared =>
              -- Section 3.4: a field of a frozen struct comes out frozen only
              -- where it would otherwise be linear; a copyable one comes out
              -- as an ordinary value, or a write to it would reach inside.
              .ok (if isLinear p declared then .frozen v else v)
          | _, _ => .bug s!"no field named {name}"
      | .struct _ fields =>
          match getAssoc name fields with
          | some v => .ok v
          | none => .bug s!"no field named {name}"
      | _ => .bug "a field read met a value that is not a struct"
  | .index base idx => do
      let container ← evalExpr p env base
      let position ← evalExpr p env idx
      match asSeq container, position with
      | some (_, items, _), .int i =>
          if 0 ≤ i ∧ i.toNat < items.length then
            .ok (items[i.toNat]!)
          else .trap "T-01"
      | _, _ => .bug "an index met the wrong shape"
  | .len arg => do
      let v ← evalExpr p env arg
      match asSeq v with
      | some (_, items, _) => .ok (.int items.length)
      | none => .bug "len met a value that is not a sequence"
  | .cap arg => do
      let v ← evalExpr p env arg
      match asSeq v with
      | some (_, _, c) => .ok (.int c)
      | none => .bug "cap met a value that is not a sequence"
  | .un op arg => do
      let v ← evalExpr p env arg
      unary op ((typeOf p env arg).bind Ty.intTy?) v
  | .bin op left right => do
      let a ← evalExpr p env left
      let b ← evalExpr p env right
      binary op ((typeOf p env left).bind Ty.intTy?) a b
  | .cmp op left right => do
      let a ← evalExpr p env left
      let b ← evalExpr p env right
      compare op a b
  | .divrem op left right fallback => do
      let a ← evalExpr p env left
      let b ← evalExpr p env right
      let f ← evalExpr p env fallback
      divrem op ((typeOf p env left).bind Ty.intTy?) a b f
  | .shift op arg n => do
      let v ← evalExpr p env arg
      shiftOp op ((typeOf p env arg).bind Ty.intTy?) v n
  | .cast t arg => do
      let v ← evalExpr p env arg
      castTo t v
  | .logical op left right => do
      let a ← evalExpr p env left
      match op, a with
      | .and, .bool false => .ok (.bool false)
      | .or, .bool true => .ok (.bool true)
      | _, .bool _ => evalExpr p env right
      | _, _ => .bug "a boolean operator met the wrong shape"
  | .enumVal t v => .ok (.tag t v)
  | .structVal t fields =>
      match p.struct? t with
      | none => .bug s!"no struct named {t}"
      | some d => do
          -- In the struct's declared order, which is what section 13 pins.
          let vs ← evalFields p env d.fields fields
          .ok (.struct t vs)
termination_by e => (sizeOf e, 0)

def evalFields (p : Program) (env : Env) (fields : List Field)
    (given : List (String × Expr)) : Res (List (String × Value)) :=
  match fields with
  | [] => .ok []
  | f :: rest =>
      match hgiven : getAssoc f.name given with
      | none => .bug s!"a struct value is missing {f.name}"
      | some e => do
          let v ← evalExpr p env e
          let vs ← evalFields p env rest given
          .ok ((f.name, v) :: vs)
termination_by (sizeOf given, fields.length)
decreasing_by
  · have := getAssoc_lt hgiven
    exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by simp)

end

/-! ## Places -/

def placeTy (p : Program) (env : Env) : Place → Option Ty
  | .var name => (env.get name).map Slot.ty
  | .field base name => do fieldTy p (← placeTy p env base) name
  | .index base _ => do (← placeTy p env base).elem?

def readPlace (p : Program) (env : Env) : Place → Res Value
  | .var name =>
      match env.get name with
      | some s => .ok s.value
      | none => .bug s!"no local named {name}"
  | .field base name => do
      let container ← readPlace p env base
      match container with
      | .struct _ fields =>
          match getAssoc name fields with
          | some v => .ok v
          | none => .bug s!"no field named {name}"
      | _ => .bug "a field place met a value that is not a struct"
  | .index base idx => do
      let container ← readPlace p env base
      let position ← evalExpr p env idx
      match asSeq container, position with
      | some (_, items, _), .int i =>
          if 0 ≤ i ∧ i.toNat < items.length then
            .ok (items[i.toNat]!)
          else .trap "T-01"
      | _, _ => .bug "an index place met the wrong shape"

def writePlace (p : Program) (env : Env) : Place → Value → Res Env
  | .var name, v =>
      match env.get name with
      | some _ => .ok (env.set name v)
      | none => .bug s!"no local named {name}"
  | .field base name, v => do
      let container ← readPlace p env base
      match container with
      | .struct t fields =>
          if (getAssoc name fields).isSome then
            writePlace p env base (.struct t (setAssoc name v fields))
          else .bug s!"no field named {name}"
      | _ => .bug "a field place met a value that is not a struct"
  | .index base idx, v => do
      let container ← readPlace p env base
      let position ← evalExpr p env idx
      match container, position with
      | .seq m items c, .int i =>
          if 0 ≤ i ∧ i.toNat < items.length then
            writePlace p env base (.seq m (items.set i.toNat v) c)
          else .trap "T-01"
      | _, _ => .bug "an index place met the wrong shape"

end Pcrevera.Tir
