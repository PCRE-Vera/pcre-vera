import Lean.Data.Json
import Pcrevera.Ref.Pike

/-!
# Decoding the corpora and the AST bridge

The Lean reference engine replays `conformance/corpus.json` and
`conformance/sweep.json`, with `gen/lean/bridge.json` supplying what the
parser would: the spec AST of every compiled case and the engine's own
compiled tables to hold `R.compile` to. This module is the JSON reading,
nothing else; a field that does not decode is an error worth stopping on,
never a default, because a runner that shrugged at a malformed record would
be reporting cases as replayed that never ran.
-/

namespace Pcrevera.Corpus

open Lean (Json)
open Pcrevera Pcrevera.Ref

abbrev D (α : Type) := Except String α

def field (j : Json) (name : String) : D Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error e => .error s!"{name}: {e}"

def fieldOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok v => if v.isNull then none else some v
  | .error _ => none

def asNat (j : Json) : D Nat :=
  match j.getNat? with
  | .ok v => .ok v
  | .error e => .error e

def natField (j : Json) (name : String) : D Nat := do
  asNat (← field j name)

def natFieldD (j : Json) (name : String) (dflt : Nat) : D Nat :=
  match fieldOpt j name with
  | some v => asNat v
  | none => .ok dflt

def intField (j : Json) (name : String) : D Int := do
  match (← field j name).getInt? with
  | .ok v => .ok v
  | .error e => .error e

def strField (j : Json) (name : String) : D String := do
  match (← field j name).getStr? with
  | .ok v => .ok v
  | .error e => .error e

def boolField (j : Json) (name : String) : D Bool := do
  match (← field j name).getBool? with
  | .ok v => .ok v
  | .error e => .error e

def arrField (j : Json) (name : String) : D (Array Json) := do
  match (← field j name).getArr? with
  | .ok v => .ok v
  | .error e => .error e

def hexNibble (c : Char) : D Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
  else .error s!"{c} is not a hex digit"

def hexBytes (text : String) : D ByteArray := do
  let chars := text.toList.toArray
  if chars.size % 2 != 0 then .error "odd hex length"
  else
    let mut out := ByteArray.empty
    for i in [0 : chars.size / 2] do
      let hi ← hexNibble chars[2 * i]!
      let lo ← hexNibble chars[2 * i + 1]!
      out := out.push (UInt8.ofNat (hi * 16 + lo))
    .ok out

def nlOf (n : Nat) : D NlType :=
  match n with
  | 0 => .ok .lf | 1 => .ok .cr | 2 => .ok .crlf
  | 3 => .ok .anycrlf | 4 => .ok .any
  | _ => .error s!"{n} names no newline convention"

def bsrOf (n : Nat) : D BsrType :=
  match n with
  | 0 => .ok .unicode | 1 => .ok .anycrlf
  | _ => .error s!"{n} names no BSR convention"

/-- The compile-option bits that survive to match time (spec.py). -/
def patOptsOf (flags : Nat) : PatOpts :=
  { anchored := flags &&& 32 != 0, endanchored := flags &&& 64 != 0 }

/-- The match-option bits (spec.py's MATCH_OPTIONS). -/
def moptsOf (bits : Nat) : MOpts :=
  { notbol := bits &&& 1 != 0
    noteol := bits &&& 2 != 0
    notempty := bits &&& 4 != 0
    notemptyAtStart := bits &&& 8 != 0
    anchored := bits &&& 16 != 0 }

/-- One bridge AST node, the exporter's constructor-per-node encoding.

Fuel bounds the nesting the decoder follows, and the parser's own depth
limit is far below it, so running out is a malformed bridge rather than a
deep pattern. -/
def astOf (fuel : Nat) (j : Json) : D Ast := do
  match fuel with
  | 0 => .error "the bridged tree nests deeper than the parser admits"
  | fuel + 1 => do
    let parts ← match j.getArr? with
      | .ok v => pure v
      | .error e => .error e
    let tag ← match parts[0]!.getStr? with
      | .ok v => pure v
      | .error e => .error e
    match tag with
    | "nul" => .ok .nul
    | "chr" => do .ok (.chr (UInt8.ofNat (← asNat parts[1]!)))
    | "chrCI" => do .ok (.chrCI (UInt8.ofNat (← asNat parts[1]!)))
    | "cls" => do
        let bytes ← hexBytes (← match parts[1]!.getStr? with
          | .ok v => pure v | .error e => .error e)
        if h : bytes.size = 32 then
          .ok (.cls ⟨bytes.data, h⟩)
        else .error "a class bitmap is 32 bytes"
    | "any" => .ok .any
    | "anyNoNL" => .ok .anyNoNL
    | "bsr" => .ok .bsr
    | "cat" => do
        let kids ← match parts[1]!.getArr? with
          | .ok v => pure v | .error e => .error e
        .ok (.cat (← kids.toList.mapM (astOf fuel)))
    | "alt" => do
        let arms ← match parts[1]!.getArr? with
          | .ok v => pure v | .error e => .error e
        .ok (.alt (← arms.toList.mapM (astOf fuel)))
    | "grp" => do .ok (.grp (← asNat parts[1]!) (← astOf fuel parts[2]!))
    | "rep" => do
        let lo ← asNat parts[1]!
        let hi ← asNat parts[2]!
        let greedy ← asNat parts[3]!
        .ok (.rep lo (if hi == none32 then none else some hi) (greedy != 0)
          (← astOf fuel parts[4]!))
    | "circ" => .ok .circ
    | "circM" => .ok .circM
    | "doll" => .ok .doll
    | "dollE" => .ok .dollE
    | "dollM" => .ok .dollM
    | "sod" => .ok .sod
    | "eod" => .ok .eod
    | "eodn" => .ok .eodn
    | "wordB" => .ok .wordB
    | "notWordB" => .ok .notWordB
    | _ => .error s!"{tag} names no AST constructor"

def opOf (n : Nat) : D Op :=
  match n with
  | 0 => .ok .chr | 1 => .ok .chrCI | 2 => .ok .cls | 3 => .ok .any
  | 4 => .ok .anyNoNL | 5 => .ok .bsr | 6 => .ok .split | 7 => .ok .jump
  | 8 => .ok .save | 9 => .ok .circ | 10 => .ok .circM | 11 => .ok .doll
  | 12 => .ok .dollE | 13 => .ok .dollM | 14 => .ok .sod | 15 => .ok .eod
  | 16 => .ok .eodn | 17 => .ok .wordB | 18 => .ok .notWordB
  | 19 => .ok .repZero | 20 => .ok .repLoop | 21 => .ok .repEnter
  | 22 => .ok .repNext | 23 => .ok .accept
  | _ => .error s!"{n} names no opcode"

def rkOf (n : Nat) : D Rk :=
  match n with
  | 0 => .ok .root | 1 => .ok .group | 2 => .ok .branch
  | 3 => .ok .alt | 4 => .ok .«repeat»
  | _ => .error s!"{n} names no region kind"

/-- What the bridge says the engine compiled: the tables `R.compile` is
held to, plus the certificate slots. -/
structure BridgeRe where
  code : Array Inst
  classes : Array UInt8
  reps : Array RepInfo
  regions : Array Region
  ncap : Nat
  nregs : Nat
  opts : Nat
  nltype : NlType
  bsrtype : BsrType
  hascrlf : Bool
  crfirst : Bool
  pike : Bool
  cert : Json
  hascert : Bool
  pikecert : Json
  haspikecert : Bool

def bridgeReOf (j : Json) : D BridgeRe := do
  let code ← (← arrField j "code").mapM fun i => do
    let parts ← match i.getArr? with
      | .ok v => pure v | .error e => .error e
    let op ← opOf (← asNat parts[0]!)
    .ok (⟨op, ← asNat parts[1]!, ← asNat parts[2]!⟩ : Inst)
  let classes ← hexBytes (← strField j "classes")
  let reps ← (← arrField j "reps").mapM fun r => do
    let parts ← match r.getArr? with
      | .ok v => pure v | .error e => .error e
    .ok (⟨← asNat parts[0]!, ← asNat parts[1]!, (← asNat parts[2]!) != 0,
      ← asNat parts[3]!, ← asNat parts[4]!, ← asNat parts[5]!⟩ : RepInfo)
  let regions ← (← arrField j "regions").mapM fun r => do
    let parts ← match r.getArr? with
      | .ok v => pure v | .error e => .error e
    .ok (⟨← rkOf (← asNat parts[0]!), ← asNat parts[1]!, ← asNat parts[2]!,
      ← asNat parts[3]!⟩ : Region)
  .ok { code, classes := classes.data, reps, regions
        ncap := ← natField j "ncap"
        nregs := ← natField j "nregs"
        opts := ← natField j "opts"
        nltype := ← nlOf (← natField j "nltype")
        bsrtype := ← bsrOf (← natField j "bsr")
        hascrlf := (← natField j "hascrlf") != 0
        crfirst := (← natField j "crfirst") != 0
        pike := ← boolField j "pike"
        cert := (fieldOpt j "cert").getD Json.null
        hascert := ← boolField j "hascert"
        pikecert := (fieldOpt j "pikecert").getD Json.null
        haspikecert := ← boolField j "haspikecert" }

/-- One bridge entry: the AST and the expected compile, or a skip. -/
structure BridgeCase where
  skip : Option Nat
  ast : Option Ast
  expected : Option BridgeRe

def bridgeCaseOf (j : Json) : D BridgeCase := do
  match fieldOpt j "skip" with
  | some code => .ok ⟨some (← asNat code), none, none⟩
  | none =>
      .ok ⟨none, some (← astOf 4096 (← field j "ast")),
        some (← bridgeReOf (← field j "re"))⟩

end Pcrevera.Corpus
