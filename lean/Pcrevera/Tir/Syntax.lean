/-!
# TIR, as an inductive type (I-1, first half)

The deep embedding of layer I. One constructor per node of TIR-SPEC.md
sections 5 to 9, in the order the specification lists them, and nothing else:
this file is syntax, and every question about whether a tree makes sense
belongs to the validator, not here.

The constructor families are the schema's, name for name, so that the decoder
of gate 2 reads as a transcription and can be audited as one. The shapes are
not everywhere the same, and the differences are worth writing down because
the decoder is where they get enforced.

Narrower than the JSON, on purpose, because a type that cannot spell a bad
program is worth more than a rule saying not to: a literal carries an `IntTy`
rather than a `Ty`, since `{"bytes": 3}` is not a literal the schema admits;
a vec's maximum and a shift's count are `Nat`, where the reader would accept
a negative integer that V-007 and V-015 then refuse; and a switch arm is a
pair rather than a structure, so the interpreter's recursion over arms is the
recursion over a list.

Wider than the JSON, and left so: a name is any `String`, where the reader
requires an identifier of at most 64 bytes, and a struct's fields are a list
where JSON has an object, so this type can hold a duplicate key that no
artifact can. Both are decoder obligations rather than syntax ones — the
first because a `String` refined by a predicate would carry a proof through
every constructor, the second because the field *order* is what the printer
has to reproduce and a map would lose it. Lookup takes the first match, so
the extra values have a meaning here; they simply never arrive.
-/

namespace Pcrevera.Tir

/-- The integer types: the four an arithmetic rule can be written for. -/
inductive IntTy where
  | u8 | i32 | u32 | counter
deriving DecidableEq, Repr, Inhabited

/-- The types of TIR-SPEC.md section 3. -/
inductive Ty where
  | bool
  | int (t : IntTy)
  | bytes
  | enum (name : String)
  | struct (name : String)
  | vec (elem : Ty) (max : Nat)
  | frozen (inner : Ty)
deriving DecidableEq, Repr, Inhabited

instance : Coe IntTy Ty := ⟨Ty.int⟩

inductive UnOp where
  | not | neg | bnot
deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | and | or | xor
deriving DecidableEq, Repr, Inhabited

inductive CmpOp where
  | eq | ne | lt | le | gt | ge
deriving DecidableEq, Repr, Inhabited

inductive DivOp where
  | div | rem
deriving DecidableEq, Repr, Inhabited

inductive ShiftOp where
  | shl | shr | sar
deriving DecidableEq, Repr, Inhabited

inductive LogOp where
  | and | or
deriving DecidableEq, Repr, Inhabited

/-- Expressions, TIR-SPEC.md section 6. -/
inductive Expr where
  | litInt (t : IntTy) (value : Int)
  | litBool (b : Bool)
  | var (name : String)
  | constRef (name : String)
  | field (base : Expr) (name : String)
  | index (base : Expr) (idx : Expr)
  | len (arg : Expr)
  | cap (arg : Expr)
  | un (op : UnOp) (arg : Expr)
  | bin (op : BinOp) (left right : Expr)
  | cmp (op : CmpOp) (left right : Expr)
  | divrem (op : DivOp) (left right fallback : Expr)
  | shift (op : ShiftOp) (arg : Expr) (count : Nat)
  | cast (t : Ty) (arg : Expr)
  | logical (op : LogOp) (left right : Expr)
  | enumVal (t : String) (variant : String)
  | structVal (t : String) (fields : List (String × Expr))
deriving Repr, Inhabited, BEq

/-- Places, TIR-SPEC.md section 7. A place's base is another place, which is
why they are not expressions: a constant reference can never be written to,
and that is a difference the type carries rather than a rule somebody has to
remember. -/
inductive Place where
  | var (name : String)
  | field (base : Place) (name : String)
  | index (base : Place) (idx : Expr)
deriving Repr, Inhabited, BEq

inductive Arg where
  | inArg (e : Expr)
  | inoutArg (p : Place)
deriving Repr, Inhabited, BEq

/-- Statements, TIR-SPEC.md sections 8 and 9. -/
inductive Stmt where
  | letS (name : String) (t : Ty) (init : Option Expr)
  | assign (place : Place) (value : Expr)
  | take (dest src : Place)
  | swap (a b : Place)
  | copy (dest : Place) (src : Expr)
  | freeze (dest src : Place)
  | push (seq : Place) (value : Expr)
  | pop (seq dest : Place)
  | truncate (seq : Place) (length : Expr)
  | reserve (seq : Place) (capacity : Expr)
  | ifS (cond : Expr) (thenB elseB : List Stmt)
  | whileS (cond variant : Expr) (body : List Stmt)
  | switchS (value : Expr) (arms : List (String × List Stmt))
      (dflt : Option (List Stmt))
  | breakS
  | continueS
  | returnS (value : Option Expr)
  | call (fn : String) (args : List Arg) (dest : Option Place)
deriving Repr, Inhabited, BEq

/-- Constant values, TIR-SPEC.md section 5. -/
inductive ConstValue where
  | int (v : Int)
  | bool (b : Bool)
  | variant (name : String)
  | fields (entries : List (String × ConstValue))
  | bytes (data : List UInt8)
  | elems (items : List ConstValue)
deriving Repr, Inhabited, BEq

structure Field where
  name : String
  ty : Ty
deriving DecidableEq, Repr, Inhabited

structure EnumDecl where
  name : String
  variants : List String
deriving DecidableEq, Repr, Inhabited

structure StructDecl where
  name : String
  fields : List Field
deriving DecidableEq, Repr, Inhabited

structure ConstDecl where
  name : String
  ty : Ty
  value : ConstValue
deriving Repr, Inhabited, BEq

structure Param where
  name : String
  ty : Ty
  inout : Bool
deriving DecidableEq, Repr, Inhabited

structure Func where
  name : String
  params : List Param
  ret : Option Ty
  body : List Stmt
deriving Repr, Inhabited, BEq

/-- A whole artifact. Declaration order carries no meaning and the canonical
encoding sorts by name, so nothing here may depend on it. -/
structure Program where
  enums : List EnumDecl
  structs : List StructDecl
  consts : List ConstDecl
  funcs : List Func
deriving Repr, Inhabited, BEq

/-! ## Looking declarations up

Association lists rather than a map, because the artifact is read once and
every proof about it wants an equation it can rewrite with. -/

def findBy {α : Type} (name : String) (key : α → String) : List α → Option α
  | [] => none
  | d :: rest => if key d = name then some d else findBy name key rest

def Program.enum? (p : Program) (name : String) : Option EnumDecl :=
  findBy name EnumDecl.name p.enums

def Program.struct? (p : Program) (name : String) : Option StructDecl :=
  findBy name StructDecl.name p.structs

def Program.const? (p : Program) (name : String) : Option ConstDecl :=
  findBy name ConstDecl.name p.consts

def Program.func? (p : Program) (name : String) : Option Func :=
  findBy name Func.name p.funcs

def StructDecl.field? (d : StructDecl) (name : String) : Option Field :=
  findBy name Field.name d.fields

/-- Assignment into an association list, leaving the order alone. -/
def setAssoc {α : Type} (name : String) (value : α) :
    List (String × α) → List (String × α)
  | [] => []
  | (k, v) :: rest =>
      if k = name then (name, value) :: rest else (k, v) :: setAssoc name value rest

def getAssoc {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (k, v) :: rest => if k = name then some v else getAssoc name rest

end Pcrevera.Tir
