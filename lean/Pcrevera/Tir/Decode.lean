import Lean.Data.Json
import Pcrevera.Tir.Print

/-!
# The decoder (I-2, second half)

The audited item. DESIGN.md section 6 says the trusted base grows by exactly
one thing in M7, and this is it: the constructor-per-constructor mapping from
the artifact's schema to the deep embedding. Nothing proves it right, so it is
written to be read against TIR-SPEC.md section 14 and against
`tir/serialize.py`'s reader, one clause at a time, in the same order.

Strict in the same spirit as the writer is exact. Every object has a closed,
typed set of keys, so a misspelled field is an error and not a silently
dropped one; every tagged form is a one-key object; every name is checked
against the identifier rule and the sixty-four byte limit. Whitespace is
whatever the JSON parser accepts, because a parser has no business caring —
whether a file is *byte* canonical is what gate 3 asks, by printing what it
decoded and comparing.

Two places where this is less strict than the Python reader, both harmless
here and both worth naming rather than discovering. Lean's JSON parser keeps
one of a duplicated key where the reader refuses the document outright; and it
normalizes `1e0` to the same number as `1`, so a float that happens to be
integral and to cancel its own exponent is indistinguishable here where the
reader refuses every float at the parse. Anything else fractional is refused
by `jInt`. Neither gap can reach a canonical file, since the printer emits
neither, and gate 3's round trip is over printed text.

Recursion is bounded by the length of the input, which no well-formed
document can exhaust — every level of nesting costs at least one character —
and which turns a pathologically deep one into a decoding failure rather than
a stack overflow. `serialize.py` says the same thing by catching
`RecursionError`.
-/

namespace Pcrevera.Tir

open Lean (Json)

abbrev D (α : Type) := Except String α

private def fail {α : Type} (msg : String) : D α := .error msg

/-- A field the schema spells `null` when it is absent. -/
def optD {α : Type} (j : Json) (f : Json → D α) : D (Option α) :=
  if j.isNull then .ok none else do let v ← f j; .ok (some v)

/-- The members of an object, or nothing if it is not one. -/
def jFields (j : Json) : Option (List (String × Json)) :=
  match j with
  | .obj m => some m.toList
  | _ => none

private def lookupJ (fs : List (String × Json)) (k : String) : Option Json :=
  getAssoc k fs

private def allIn (keys : List String) : List (String × Json) → Bool
  | [] => true
  | (k, _) :: rest => keys.contains k && allIn keys rest

private def allPresent (fs : List (String × Json)) : List String → Bool
  | [] => true
  | k :: rest => (lookupJ fs k).isSome && allPresent fs rest

/-- An object with a closed set of keys, and nothing else. -/
def closed (j : Json) (what : String) (keys : List String) :
    D (List (String × Json)) :=
  match jFields j with
  | none => fail s!"{what} must be an object"
  | some fs =>
      if !allPresent fs keys then fail s!"{what} is missing a field"
      else if !allIn keys fs then fail s!"{what} has fields nothing reads"
      else .ok fs

def need (fs : List (String × Json)) (what k : String) : D Json :=
  match lookupJ fs k with
  | some v => .ok v
  | none => fail s!"{what} is missing {k}"

/-- A one-key object: the tagged forms of types, values, expressions, places,
statements and call arguments. -/
def tagged (j : Json) (what : String) : D (String × Json) :=
  match jFields j with
  | some [(k, v)] => .ok (k, v)
  | _ => fail s!"{what} is a one-key object"

def jStr (j : Json) (what : String) : D String :=
  match j.getStr? with
  | .ok s => .ok s
  | .error _ => fail s!"{what} must be a string"

/-- An integer, and nothing a float could be written as.

The reader refuses every float at the parse, because the artifact holds none;
this refuses every number whose decimal form is not an integer. The two agree
except on a number written with an exponent that cancels, `1e0` for `1`, which
Lean's parser normalizes away before anything here can see it. No canonical
file can hold either, and gate 3's round trip is over printed text, so the gap
is one of strictness on hand-written input rather than of meaning. -/
def jInt (j : Json) (what : String) : D Int :=
  match j with
  | .num n => if n.exponent = 0 then .ok n.mantissa
      else fail s!"{what} must be an integer"
  | _ => fail s!"{what} must be an integer"

def jNat (j : Json) (what : String) : D Nat := do
  let v ← jInt j what
  if v < 0 then fail s!"{what} must not be negative" else .ok v.toNat

def jBool (j : Json) (what : String) : D Bool :=
  match j.getBool? with
  | .ok b => .ok b
  | .error _ => fail s!"{what} must be a boolean"

def jArr (j : Json) (what : String) : D (List Json) :=
  match j.getArr? with
  | .ok a => .ok a.toList
  | .error _ => fail s!"{what} must be a list"

private def identStart (c : Char) : Bool :=
  c.isAlpha || c = '_'

private def identRest (c : Char) : Bool :=
  c.isAlphanum || c = '_'

/-- The identifier rule of TIR-SPEC.md section 2, and its length cap. -/
def isIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => identStart c && rest.all identRest && s.length ≤ 64

def jName (j : Json) (what : String) : D String := do
  let s ← jStr j what
  if isIdentifier s then .ok s else fail s!"{what} is not an identifier: {s}"

/-! ## Types -/

def primTy : String → Option Ty
  | "bool" => some .bool
  | "u8" => some (.int .u8)
  | "i32" => some (.int .i32)
  | "u32" => some (.int .u32)
  | "counter" => some (.int .counter)
  | "bytes" => some .bytes
  | _ => none

def decodeTy : Nat → Json → D Ty
  | 0, _ => fail "the artifact nests deeper than it can be read"
  | n + 1, j =>
      match j.getStr? with
      | .ok s =>
          match primTy s with
          | some t => .ok t
          | none => fail s!"unknown type {s}"
      | .error _ => do
          let (tag, payload) ← tagged j "a type"
          match tag with
          | "enum" => return .enum (← jName payload "an enum type name")
          | "struct" => return .struct (← jName payload "a struct type name")
          | "frozen" => return .frozen (← decodeTy n payload)
          | "vec" => do
              let fs ← closed payload "a vec type" ["elem", "max"]
              let elem ← decodeTy n (← need fs "a vec type" "elem")
              let max ← jNat (← need fs "a vec type" "max") "a vec maximum"
              return .vec elem max
          | _ => fail s!"unknown type form {tag}"

/-! ## Constant values -/

mutual

def decodeConst (fuel : Nat) (j : Json) : D ConstValue :=
  match fuel with
  | 0 => fail "the artifact nests deeper than it can be read"
  | n + 1 =>
      match j.getBool? with
      | .ok b => .ok (.bool b)
      | .error _ =>
          match j.getInt? with
          | .ok v => .ok (.int v)
          | .error _ => do
              let (tag, payload) ← tagged j "a constant value"
              match tag with
              | "variant" => return .variant (← jName payload "a variant")
              | "bytes" => do
                  let s ← jStr payload "a byte string"
                  match hexToBytes s.toList with
                  | some data => return .bytes data
                  | none => fail "a byte string is even-length lowercase hex"
              | "elems" => do
                  let items ← jArr payload "the elements of a constant"
                  return .elems (← decodeConstList n items)
              | "fields" => do
                  match jFields payload with
                  | none => fail "the fields of a constant must be an object"
                  | some fs => return .fields (← decodeConstFields n fs)
              | _ => fail s!"unknown constant form {tag}"
termination_by (fuel, 0)

def decodeConstList (n : Nat) (items : List Json) : D (List ConstValue) :=
  match items with
  | [] => .ok []
  | j :: rest => do
      let v ← decodeConst n j
      let vs ← decodeConstList n rest
      .ok (v :: vs)
termination_by (n, items.length + 1)

def decodeConstFields (n : Nat) (fs : List (String × Json)) :
    D (List (String × ConstValue)) :=
  match fs with
  | [] => .ok []
  | (k, j) :: rest => do
      let key ← if isIdentifier k then .ok k else fail s!"{k} is not a field name"
      let v ← decodeConst n j
      let vs ← decodeConstFields n rest
      .ok ((key, v) :: vs)
termination_by (n, fs.length + 1)

end

/-! ## Expressions and places -/

def unOp : String → Option UnOp
  | "not" => some .not | "neg" => some .neg | "bnot" => some .bnot | _ => none

def binOp : String → Option BinOp
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul
  | "and" => some .and | "or" => some .or | "xor" => some .xor | _ => none

def cmpOp : String → Option CmpOp
  | "eq" => some .eq | "ne" => some .ne | "lt" => some .lt
  | "le" => some .le | "gt" => some .gt | "ge" => some .ge | _ => none

def shiftOpOf : String → Option ShiftOp
  | "shl" => some .shl | "shr" => some .shr | "sar" => some .sar | _ => none

def litTy : String → Option IntTy
  | "u8" => some .u8 | "i32" => some .i32
  | "u32" => some .u32 | "counter" => some .counter | _ => none

mutual

def decodeExpr (fuel : Nat) (j : Json) : D Expr :=
  match fuel with
  | 0 => fail "the artifact nests deeper than it can be read"
  | n + 1 => do
      let (tag, payload) ← tagged j "an expression"
      if tag = "bool" then
        return .litBool (← jBool payload "a bool literal")
      else match litTy tag with
      | some t => return .litInt t (← jInt payload s!"a {tag} literal")
      | none =>
          match tag with
          | "var" => return .var (← jName payload "a variable")
          | "constref" => return .constRef (← jName payload "a constant reference")
          | "field" => do
              let fs ← closed payload "a field read" ["base", "name"]
              return .field (← decodeExpr n (← need fs "a field read" "base"))
                (← jName (← need fs "a field read" "name") "a field name")
          | "index" => do
              let fs ← closed payload "an index" ["base", "index"]
              return .index (← decodeExpr n (← need fs "an index" "base"))
                (← decodeExpr n (← need fs "an index" "index"))
          | "len" => return .len (← decodeExpr n payload)
          | "cap" => return .cap (← decodeExpr n payload)
          | "un" => do
              let fs ← closed payload "a unary operation" ["op", "arg"]
              let o ← jStr (← need fs "a unary operation" "op") "an operator"
              match unOp o with
              | none => fail s!"unknown operator {o}"
              | some op => return .un op (← decodeExpr n (← need fs "a unary operation" "arg"))
          | "bin" => do
              let fs ← closed payload "a binary operation" ["op", "left", "right"]
              let o ← jStr (← need fs "a binary operation" "op") "an operator"
              match binOp o with
              | none => fail s!"unknown operator {o}"
              | some op =>
                  return .bin op (← decodeExpr n (← need fs "a binary operation" "left"))
                    (← decodeExpr n (← need fs "a binary operation" "right"))
          | "cmp" => do
              let fs ← closed payload "a comparison" ["op", "left", "right"]
              let o ← jStr (← need fs "a comparison" "op") "an operator"
              match cmpOp o with
              | none => fail s!"unknown operator {o}"
              | some op =>
                  return .cmp op (← decodeExpr n (← need fs "a comparison" "left"))
                    (← decodeExpr n (← need fs "a comparison" "right"))
          | "div" | "rem" => do
              let fs ← closed payload s!"a {tag}" ["left", "right", "fallback"]
              let op := if tag = "div" then DivOp.div else DivOp.rem
              return .divrem op (← decodeExpr n (← need fs "a division" "left"))
                (← decodeExpr n (← need fs "a division" "right"))
                (← decodeExpr n (← need fs "a division" "fallback"))
          | "shift" => do
              let fs ← closed payload "a shift" ["op", "arg", "count"]
              let o ← jStr (← need fs "a shift" "op") "an operator"
              match shiftOpOf o with
              | none => fail s!"unknown operator {o}"
              | some op =>
                  return .shift op (← decodeExpr n (← need fs "a shift" "arg"))
                    (← jNat (← need fs "a shift" "count") "a shift count")
          | "cast" => do
              let fs ← closed payload "a cast" ["type", "arg"]
              return .cast (← decodeTy n (← need fs "a cast" "type"))
                (← decodeExpr n (← need fs "a cast" "arg"))
          | "and" | "or" => do
              let fs ← closed payload s!"a boolean {tag}" ["left", "right"]
              let op := if tag = "and" then LogOp.and else LogOp.or
              return .logical op (← decodeExpr n (← need fs "a boolean operator" "left"))
                (← decodeExpr n (← need fs "a boolean operator" "right"))
          | "enumval" => do
              let fs ← closed payload "an enum value" ["type", "variant"]
              return .enumVal (← jName (← need fs "an enum value" "type") "an enum name")
                (← jName (← need fs "an enum value" "variant") "a variant name")
          | "structval" => do
              let fs ← closed payload "a struct value" ["type", "fields"]
              let t ← jName (← need fs "a struct value" "type") "a struct name"
              match jFields (← need fs "a struct value" "fields") with
              | none => fail "struct value fields must be an object"
              | some entries => return .structVal t (← decodeExprFields n entries)
          | _ => fail s!"unknown expression form {tag}"
termination_by (fuel, 0)

def decodeExprFields (n : Nat) (fs : List (String × Json)) :
    D (List (String × Expr)) :=
  match fs with
  | [] => .ok []
  | (k, j) :: rest => do
      let key ← if isIdentifier k then .ok k else fail s!"{k} is not a field name"
      let v ← decodeExpr n j
      let vs ← decodeExprFields n rest
      .ok ((key, v) :: vs)
termination_by (n, fs.length + 1)

end

def decodePlace : Nat → Json → D Place
  | 0, _ => fail "the artifact nests deeper than it can be read"
  | n + 1, j => do
      let (tag, payload) ← tagged j "a place"
      match tag with
      | "var" => return .var (← jName payload "a variable")
      | "field" => do
          let fs ← closed payload "a field place" ["base", "name"]
          return .field (← decodePlace n (← need fs "a field place" "base"))
            (← jName (← need fs "a field place" "name") "a field name")
      | "index" => do
          let fs ← closed payload "an index place" ["base", "index"]
          return .index (← decodePlace n (← need fs "an index place" "base"))
            (← decodeExpr n (← need fs "an index place" "index"))
      | _ => fail s!"a place is a variable, a field, or an index, got {tag}"

/-! ## Statements -/

def decodeArg (n : Nat) (j : Json) : D Arg := do
  let (mode, payload) ← tagged j "a call argument"
  match mode with
  | "in" => return .inArg (← decodeExpr n payload)
  | "inout" => return .inoutArg (← decodePlace n payload)
  | _ => fail s!"a call argument is 'in' or 'inout', got {mode}"

def decodeArgs (n : Nat) : List Json → D (List Arg)
  | [] => .ok []
  | j :: rest => do
      let a ← decodeArg n j
      let as ← decodeArgs n rest
      .ok (a :: as)

mutual

def decodeStmt (fuel : Nat) (j : Json) : D Stmt :=
  match fuel with
  | 0 => fail "the artifact nests deeper than it can be read"
  | n + 1 => do
      let (tag, payload) ← tagged j "a statement"
      match tag with
      | "let" => do
          let fs ← closed payload "a let" ["name", "type", "init"]
          let init ← optD (← need fs "a let" "init") (decodeExpr n)
          return .letS (← jName (← need fs "a let" "name") "a local name")
            (← decodeTy n (← need fs "a let" "type")) init
      | "assign" => do
          let fs ← closed payload "an assignment" ["place", "value"]
          return .assign (← decodePlace n (← need fs "an assignment" "place"))
            (← decodeExpr n (← need fs "an assignment" "value"))
      | "take" => do
          let fs ← closed payload "a take" ["dest", "src"]
          return .take (← decodePlace n (← need fs "a take" "dest"))
            (← decodePlace n (← need fs "a take" "src"))
      | "swap" => do
          let fs ← closed payload "a swap" ["a", "b"]
          return .swap (← decodePlace n (← need fs "a swap" "a"))
            (← decodePlace n (← need fs "a swap" "b"))
      | "copy" => do
          let fs ← closed payload "a copy" ["dest", "src"]
          return .copy (← decodePlace n (← need fs "a copy" "dest"))
            (← decodeExpr n (← need fs "a copy" "src"))
      | "freeze" => do
          let fs ← closed payload "a freeze" ["dest", "src"]
          return .freeze (← decodePlace n (← need fs "a freeze" "dest"))
            (← decodePlace n (← need fs "a freeze" "src"))
      | "push" => do
          let fs ← closed payload "a push" ["seq", "value"]
          return .push (← decodePlace n (← need fs "a push" "seq"))
            (← decodeExpr n (← need fs "a push" "value"))
      | "pop" => do
          let fs ← closed payload "a pop" ["seq", "dest"]
          return .pop (← decodePlace n (← need fs "a pop" "seq"))
            (← decodePlace n (← need fs "a pop" "dest"))
      | "truncate" => do
          let fs ← closed payload "a truncate" ["seq", "len"]
          return .truncate (← decodePlace n (← need fs "a truncate" "seq"))
            (← decodeExpr n (← need fs "a truncate" "len"))
      | "reserve" => do
          let fs ← closed payload "a reserve" ["seq", "cap"]
          return .reserve (← decodePlace n (← need fs "a reserve" "seq"))
            (← decodeExpr n (← need fs "a reserve" "cap"))
      | "if" => do
          let fs ← closed payload "an if" ["cond", "then", "else"]
          return .ifS (← decodeExpr n (← need fs "an if" "cond"))
            (← decodeBody n (← jArr (← need fs "an if" "then") "an if body"))
            (← decodeBody n (← jArr (← need fs "an if" "else") "an if body"))
      | "while" => do
          let fs ← closed payload "a while" ["cond", "variant", "body"]
          return .whileS (← decodeExpr n (← need fs "a while" "cond"))
            (← decodeExpr n (← need fs "a while" "variant"))
            (← decodeBody n (← jArr (← need fs "a while" "body") "a while body"))
      | "switch" => do
          let fs ← closed payload "a switch" ["value", "arms", "default"]
          let dflt ← optD (← need fs "a switch" "default") fun d => do
            decodeBody n (← jArr d "a switch default")
          return .switchS (← decodeExpr n (← need fs "a switch" "value"))
            (← decodeArms n (← jArr (← need fs "a switch" "arms") "switch arms"))
            dflt
      | "break" => do let _ ← closed payload "a break" []; return .breakS
      | "continue" => do let _ ← closed payload "a continue" []; return .continueS
      | "return" => do
          let fs ← closed payload "a return" ["value"]
          let v ← optD (← need fs "a return" "value") (decodeExpr n)
          return .returnS v
      | "call" => do
          let fs ← closed payload "a call" ["fn", "args", "dest"]
          let dest ← optD (← need fs "a call" "dest") (decodePlace n)
          return .call (← jName (← need fs "a call" "fn") "a function name")
            (← decodeArgs n (← jArr (← need fs "a call" "args") "call arguments"))
            dest
      | _ => fail s!"unknown statement form {tag}"
termination_by (fuel, 0, 0)

def decodeBody (n : Nat) (body : List Json) : D (List Stmt) :=
  match body with
  | [] => .ok []
  | j :: rest => do
      let s ← decodeStmt n j
      let ss ← decodeBody n rest
      .ok (s :: ss)
termination_by (n, 1, body.length)

def decodeArms (n : Nat) (arms : List Json) : D (List (String × List Stmt)) :=
  match arms with
  | [] => .ok []
  | j :: rest => do
      let fs ← closed j "a switch arm" ["variant", "body"]
      let v ← jName (← need fs "a switch arm" "variant") "a variant name"
      let b ← decodeBody n (← jArr (← need fs "a switch arm" "body") "a switch arm")
      let more ← decodeArms n rest
      .ok ((v, b) :: more)
termination_by (n, 2, arms.length)

end

/-! ## Declarations -/

def decodeEnum (j : Json) : D EnumDecl := do
  let fs ← closed j "an enum" ["name", "variants"]
  let name ← jName (← need fs "an enum" "name") "an enum name"
  let raw ← jArr (← need fs "an enum" "variants") "the variants of an enum"
  let rec go : List Json → D (List String)
    | [] => .ok []
    | v :: rest => do
        let x ← jName v "a variant"
        let xs ← go rest
        .ok (x :: xs)
  return ⟨name, ← go raw⟩

def decodeStruct (n : Nat) (j : Json) : D StructDecl := do
  let fs ← closed j "a struct" ["name", "fields"]
  let name ← jName (← need fs "a struct" "name") "a struct name"
  let raw ← jArr (← need fs "a struct" "fields") "the fields of a struct"
  let rec go : List Json → D (List Field)
    | [] => .ok []
    | v :: rest => do
        let g ← closed v "a field" ["name", "type"]
        let fname ← jName (← need g "a field" "name") "a field name"
        let ty ← decodeTy n (← need g "a field" "type")
        let xs ← go rest
        .ok (⟨fname, ty⟩ :: xs)
  return ⟨name, ← go raw⟩

def decodeConstDecl (n : Nat) (j : Json) : D ConstDecl := do
  let fs ← closed j "a constant" ["name", "type", "value"]
  return ⟨← jName (← need fs "a constant" "name") "a constant name",
    ← decodeTy n (← need fs "a constant" "type"),
    ← decodeConst n (← need fs "a constant" "value")⟩

def decodeFunc (n : Nat) (j : Json) : D Func := do
  let fs ← closed j "a function" ["name", "params", "ret", "body"]
  let name ← jName (← need fs "a function" "name") "a function name"
  let raw ← jArr (← need fs "a function" "params") "the parameters of a function"
  let rec go : List Json → D (List Param)
    | [] => .ok []
    | v :: rest => do
        let g ← closed v "a parameter" ["name", "type", "mode"]
        let pname ← jName (← need g "a parameter" "name") "a parameter name"
        let ty ← decodeTy n (← need g "a parameter" "type")
        let mode ← jStr (← need g "a parameter" "mode") "a parameter mode"
        let inout ←
          if mode = "in" then .ok false
          else if mode = "inout" then .ok true
          else fail s!"a parameter mode is 'in' or 'inout', got {mode}"
        let xs ← go rest
        .ok (⟨pname, ty, inout⟩ :: xs)
  let ret ← optD (← need fs "a function" "ret") (decodeTy n)
  return ⟨name, ← go raw, ret,
    ← decodeBody n (← jArr (← need fs "a function" "body") "a function body")⟩

def mapD {α β : Type} (f : α → D β) : List α → D (List β)
  | [] => .ok []
  | x :: rest => do
      let y ← f x
      let ys ← mapD f rest
      .ok (y :: ys)

def decodeProgram (n : Nat) (j : Json) : D Program := do
  let fs ← closed j "a TIR program" ["tir", "enums", "structs", "consts", "funcs"]
  let version ← jInt (← need fs "a TIR program" "tir") "the schema number"
  if version ≠ schema then fail s!"tir schema {version} is not {schema}"
  else
    return ⟨← mapD decodeEnum (← jArr (← need fs "a TIR program" "enums") "enums"),
      ← mapD (decodeStruct n) (← jArr (← need fs "a TIR program" "structs") "structs"),
      ← mapD (decodeConstDecl n) (← jArr (← need fs "a TIR program" "consts") "consts"),
      ← mapD (decodeFunc n) (← jArr (← need fs "a TIR program" "funcs") "funcs")⟩

/-- Decode an artifact. The budget is the input's length, which no
well-formed document can exhaust and which turns a pathologically deep one
into a decoding failure. -/
def decode (text : String) : D Program := do
  match Json.parse text with
  | .error e => fail s!"not JSON: {e}"
  | .ok j => decodeProgram text.length j

end Pcrevera.Tir
