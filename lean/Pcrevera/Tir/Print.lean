import Pcrevera.Tir.Syntax

/-!
# The canonical printer (I-2, first half)

TIR-SPEC.md section 14 fixes the artifact's encoding down to the byte,
because its SHA-256 is the identity that ties the Lean proofs, the backends
and CI together: a writer that sorted keys differently on another machine
would move that hash without changing the program. So this is not "a JSON
writer" — it is *the* one, and every choice it makes is the specification's.

Two-space indent per level, one element or member per line, `[]` and `{}` for
the empty ones, object members in code-point order of their keys, and a
trailing newline at the very end. Strings escape the two JSON must escape,
use the five short escapes, pass printable ASCII through, and spell anything
else `\uxxxx` — above the BMP as a surrogate pair, which is the only thing
JSON has.

Declaration order carries no meaning, so the printer sorts the four
declaration lists by name rather than trusting them to arrive sorted. That
makes `print` a function of the program and not of how it was built, which is
what the round trip of gate 2 needs.
-/

namespace Pcrevera.Tir

/-- What the printer walks. Not `Lean.Json`: its objects are a tree keyed by
`String`, and the thing that has to be got exactly right here is the order
members come out in, which is easier to see when it is a list the renderer
sorts than when it is an invariant of somebody else's data structure. -/
inductive JVal where
  | null
  | bool (b : Bool)
  | int (v : Int)
  | str (s : String)
  | arr (items : List JVal)
  | obj (fields : List (String × JVal))
deriving Repr, Inhabited

/-- One lowercase hex digit. Public because the round trip of gate 2 is
about it, not only about the string it ends up in. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + (n - 10))

private def hex4 (n : Nat) : String :=
  [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16),
    hexDigit (n / 16 % 16), hexDigit (n % 16)]  |> String.ofList

def hex2 (n : Nat) : String :=
  [hexDigit (n / 16 % 16), hexDigit (n % 16)]  |> String.ofList

/-- One character, as the canonical encoding spells it. -/
def escapeChar (c : Char) : String :=
  let n := c.toNat
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if n = 0x08 then "\\b"
  else if n = 0x09 then "\\t"
  else if n = 0x0A then "\\n"
  else if n = 0x0C then "\\f"
  else if n = 0x0D then "\\r"
  else if 0x20 ≤ n && n ≤ 0x7E then String.singleton c
  else if n ≤ 0xFFFF then "\\u" ++ hex4 n
  else
    -- Above the BMP, as the surrogate pair JSON has and Lean's `Char` does
    -- not.
    let m := n - 0x10000
    "\\u" ++ hex4 (0xD800 + m / 1024) ++ "\\u" ++ hex4 (0xDC00 + m % 1024)

def escape (s : String) : String :=
  "\"" ++ (s.toList.map escapeChar).foldl (· ++ ·) "" ++ "\""

/-- The inverse of `hexBytes`, which the decoder needs and which belongs
beside it: even length, lowercase, two digits a byte. -/
def hexValue (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n && n ≤ 0x66 then some (n - 0x61 + 10)
  else none

def hexToBytes : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
      let hi ← hexValue a
      let lo ← hexValue b
      let more ← hexToBytes rest
      some (UInt8.ofNat (16 * hi + lo) :: more)

/-- The bytes of a constant, lowercase and two digits each. -/
def hexBytes (data : List UInt8) : String :=
  (data.map fun b => hex2 b.toNat).foldl (· ++ ·) ""

private def pad (depth : Nat) : String := "".pushn ' ' (2 * depth)

private def joinWith (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ joinWith sep rest

/-- Members in code-point order of their keys, which is what `sorted()` gives
the Python writer and what the hash depends on.

Sorting happens here, where an object is built, rather than where one is
rendered: the renderer then walks the list it was handed, which is both the
honest reading of "the members come out sorted" and the reason its recursion
is structural. Nothing else in this file constructs a `.obj` directly. -/
def jobj (fields : List (String × JVal)) : JVal :=
  .obj (fields.mergeSort fun a b => a.1 ≤ b.1)

mutual

def renderJ (v : JVal) (depth : Nat) : String :=
  match v with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int n => toString n
  | .str s => escape s
  | .arr [] => "[]"
  | .arr items =>
      "[\n" ++ joinWith ",\n" (renderItems items (depth + 1))
        ++ "\n" ++ pad depth ++ "]"
  | .obj [] => "{}"
  | .obj fields =>
      "{\n" ++ joinWith ",\n" (renderMembers fields (depth + 1))
        ++ "\n" ++ pad depth ++ "}"

def renderItems (items : List JVal) (depth : Nat) : List String :=
  match items with
  | [] => []
  | x :: rest => (pad depth ++ renderJ x depth) :: renderItems rest depth

def renderMembers (fields : List (String × JVal)) (depth : Nat) : List String :=
  match fields with
  | [] => []
  | (k, v) :: rest =>
      (pad depth ++ escape k ++ ": " ++ renderJ v depth)
        :: renderMembers rest depth

end

/-! ## The program as a tree -/

def IntTy.name : IntTy → String
  | .u8 => "u8" | .i32 => "i32" | .u32 => "u32" | .counter => "counter"

def UnOp.name : UnOp → String
  | .not => "not" | .neg => "neg" | .bnot => "bnot"

def BinOp.name : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .and => "and" | .or => "or" | .xor => "xor"

def CmpOp.name : CmpOp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

def DivOp.name : DivOp → String
  | .div => "div" | .rem => "rem"

def ShiftOp.name : ShiftOp → String
  | .shl => "shl" | .shr => "shr" | .sar => "sar"

def LogOp.name : LogOp → String
  | .and => "and" | .or => "or"

def tyJ : Ty → JVal
  | .bool => .str "bool"
  | .int t => .str t.name
  | .bytes => .str "bytes"
  | .enum n => jobj [("enum", .str n)]
  | .struct n => jobj [("struct", .str n)]
  | .vec e m => jobj [("vec", jobj [("elem", tyJ e), ("max", .int m)])]
  | .frozen t => jobj [("frozen", tyJ t)]

mutual

def constJ : ConstValue → JVal
  | .int v => .int v
  | .bool b => .bool b
  | .variant v => jobj [("variant", .str v)]
  | .bytes data => jobj [("bytes", .str (hexBytes data))]
  | .elems items => jobj [("elems", .arr (constItemsJ items))]
  | .fields entries => jobj [("fields", jobj (constEntries entries))]

def constItemsJ : List ConstValue → List JVal
  | [] => []
  | v :: rest => constJ v :: constItemsJ rest

def constEntries : List (String × ConstValue) → List (String × JVal)
  | [] => []
  | (k, v) :: rest => (k, constJ v) :: constEntries rest

end

mutual

def exprJ : Expr → JVal
  | .litInt t v => jobj [(t.name, .int v)]
  | .litBool b => jobj [("bool", .bool b)]
  | .var n => jobj [("var", .str n)]
  | .constRef n => jobj [("constref", .str n)]
  | .field base n =>
      jobj [("field", jobj [("base", exprJ base), ("name", .str n)])]
  | .index base i =>
      jobj [("index", jobj [("base", exprJ base), ("index", exprJ i)])]
  | .len a => jobj [("len", exprJ a)]
  | .cap a => jobj [("cap", exprJ a)]
  | .un op a => jobj [("un", jobj [("op", .str op.name), ("arg", exprJ a)])]
  | .bin op l r =>
      jobj [("bin", jobj [("op", .str op.name), ("left", exprJ l),
        ("right", exprJ r)])]
  | .cmp op l r =>
      jobj [("cmp", jobj [("op", .str op.name), ("left", exprJ l),
        ("right", exprJ r)])]
  | .divrem op l r f =>
      jobj [(op.name, jobj [("left", exprJ l), ("right", exprJ r),
        ("fallback", exprJ f)])]
  | .shift op a n =>
      jobj [("shift", jobj [("op", .str op.name), ("arg", exprJ a),
        ("count", .int n)])]
  | .cast t a => jobj [("cast", jobj [("type", tyJ t), ("arg", exprJ a)])]
  | .logical op l r =>
      jobj [(op.name, jobj [("left", exprJ l), ("right", exprJ r)])]
  | .enumVal t v =>
      jobj [("enumval", jobj [("type", .str t), ("variant", .str v)])]
  | .structVal t fields =>
      jobj [("structval", jobj [("type", .str t),
        ("fields", jobj (exprEntries fields))])]

def exprEntries : List (String × Expr) → List (String × JVal)
  | [] => []
  | (k, e) :: rest => (k, exprJ e) :: exprEntries rest

end

def placeJ : Place → JVal
  | .var n => jobj [("var", .str n)]
  | .field base n =>
      jobj [("field", jobj [("base", placeJ base), ("name", .str n)])]
  | .index base i =>
      jobj [("index", jobj [("base", placeJ base), ("index", exprJ i)])]

def argJ : Arg → JVal
  | .inArg e => jobj [("in", exprJ e)]
  | .inoutArg p => jobj [("inout", placeJ p)]

def optExprJ : Option Expr → JVal
  | none => .null
  | some e => exprJ e

def optPlaceJ : Option Place → JVal
  | none => .null
  | some p => placeJ p

def optTyJ : Option Ty → JVal
  | none => .null
  | some t => tyJ t

def argsJ : List Arg → List JVal
  | [] => []
  | a :: rest => argJ a :: argsJ rest

mutual

def stmtJ : Stmt → JVal
  | .letS n t init =>
      jobj [("let", jobj [("name", .str n), ("type", tyJ t),
        ("init", optExprJ init)])]
  | .assign p v =>
      jobj [("assign", jobj [("place", placeJ p), ("value", exprJ v)])]
  | .take d s =>
      jobj [("take", jobj [("dest", placeJ d), ("src", placeJ s)])]
  | .swap a b => jobj [("swap", jobj [("a", placeJ a), ("b", placeJ b)])]
  | .copy d s => jobj [("copy", jobj [("dest", placeJ d), ("src", exprJ s)])]
  | .freeze d s =>
      jobj [("freeze", jobj [("dest", placeJ d), ("src", placeJ s)])]
  | .push s v =>
      jobj [("push", jobj [("seq", placeJ s), ("value", exprJ v)])]
  | .pop s d => jobj [("pop", jobj [("seq", placeJ s), ("dest", placeJ d)])]
  | .truncate s l =>
      jobj [("truncate", jobj [("seq", placeJ s), ("len", exprJ l)])]
  | .reserve s c =>
      jobj [("reserve", jobj [("seq", placeJ s), ("cap", exprJ c)])]
  | .ifS c t e =>
      jobj [("if", jobj [("cond", exprJ c), ("then", .arr (bodyJ t)),
        ("else", .arr (bodyJ e))])]
  | .whileS c v b =>
      jobj [("while", jobj [("cond", exprJ c), ("variant", exprJ v),
        ("body", .arr (bodyJ b))])]
  | .switchS v arms dflt =>
      jobj [("switch", jobj [("value", exprJ v), ("arms", .arr (armsJ arms)),
        ("default", match dflt with
          | none => .null
          | some b => .arr (bodyJ b))])]
  | .breakS => jobj [("break", jobj [])]
  | .continueS => jobj [("continue", jobj [])]
  | .returnS v => jobj [("return", jobj [("value", optExprJ v)])]
  | .call fn args dest =>
      jobj [("call", jobj [("fn", .str fn), ("args", .arr (argsJ args)),
        ("dest", optPlaceJ dest)])]

def bodyJ : List Stmt → List JVal
  | [] => []
  | s :: rest => stmtJ s :: bodyJ rest

def armsJ : List (String × List Stmt) → List JVal
  | [] => []
  | (v, b) :: rest =>
      jobj [("variant", .str v), ("body", .arr (bodyJ b))] :: armsJ rest

end

def enumJ (d : EnumDecl) : JVal :=
  jobj [("name", .str d.name), ("variants", .arr (d.variants.map JVal.str))]

def structJ (d : StructDecl) : JVal :=
  jobj [("name", .str d.name),
    ("fields", .arr (d.fields.map fun f =>
      jobj [("name", .str f.name), ("type", tyJ f.ty)]))]

def constDeclJ (d : ConstDecl) : JVal :=
  jobj [("name", .str d.name), ("type", tyJ d.ty), ("value", constJ d.value)]

def funcJ (d : Func) : JVal :=
  jobj [("name", .str d.name),
    ("params", .arr (d.params.map fun p =>
      jobj [("name", .str p.name), ("type", tyJ p.ty),
        ("mode", .str (if p.inout then "inout" else "in"))])),
    ("ret", optTyJ d.ret),
    ("body", .arr (bodyJ d.body))]

private def sortBy {α : Type} (key : α → String) (l : List α) : List α :=
  l.mergeSort fun a b => key a ≤ key b

/-- The schema number of TIR-SPEC.md section 14. -/
def schema : Int := 1

def programJ (p : Program) : JVal :=
  jobj [("tir", .int schema),
    ("enums", .arr ((sortBy EnumDecl.name p.enums).map enumJ)),
    ("structs", .arr ((sortBy StructDecl.name p.structs).map structJ)),
    ("consts", .arr ((sortBy ConstDecl.name p.consts).map constDeclJ)),
    ("funcs", .arr ((sortBy Func.name p.funcs).map funcJ))]

/-- The canonical text of a program, ending in exactly one newline. -/
def print (p : Program) : String := renderJ (programJ p) 0 ++ "\n"

end Pcrevera.Tir
