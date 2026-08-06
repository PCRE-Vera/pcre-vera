import Std.Data.TreeMap.Raw
import Pcrevera.Tir.Decode

/-!
# Gate 2: the decoder inverts the printer (I-2)

`Tir/PrintCheck.lean` runs the round trip on the programs there happen to be,
and gate 3 runs it on the artifact. This file is where that becomes a theorem
about every canonical program — and it is the start of one rather than the
whole of it. What is here is the bridge to `Lean.Json` and the first of the
five decoder families, the types; constants, expressions, places, statements
and the program itself are outstanding, and PLAN-M7.md section 11 says what
they are expected to cost.

What the finished theorem will not cover either, and this is the honest
boundary, is the step from the printed text to a `Json` value. `decode` calls
`Lean.Json.parse`, and relating that parser to `renderJ` is a
parser-correctness development rather than a structural induction. So the
statement starts one step in, at the tree `programJ` builds, and `jsonOf` is
the bridge — the same `Json.mkObj` a parser would produce from a canonical
document. Gate 3's byte-level check is what covers the remaining step, on the
artifact and on the toy programs.
-/

namespace Pcrevera.Tir

open Lean (Json)

/-! ## Two sorted lists with the same members are the same list

The decoder reads an object as the association list `Std.TreeMap.Raw.toList`
hands back, which is sorted by key. So the round trip needs to know that
building a map out of a sorted list and reading it back is the identity, and
that is this lemma plus what `Std` already proves about the map. -/

private def keyLt (a b : String × Json) : Prop := compare a.1 b.1 = .lt

private theorem keyLt_irrefl {a : String × Json} : ¬ keyLt a a := by
  simp only [keyLt]
  rw [show compare a.1 a.1 = Ordering.eq from
    Std.ReflCmp.compare_self]
  exact fun h => by cases h

private theorem keyLt_asymm {a b : String × Json} (h : keyLt a b) :
    ¬ keyLt b a := Std.OrientedCmp.not_lt_of_lt h

/-- Neither list can start before the other, so they start together and the
tails repeat the argument. -/
private theorem eq_of_sorted_mem : ∀ {l₁ l₂ : List (String × Json)},
    l₁.Pairwise keyLt → l₂.Pairwise keyLt →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: l₂, _, _, hm => absurd ((hm b).2 (by simp)) (by simp)
  | a :: l₁, [], _, _, hm => absurd ((hm a).1 (by simp)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, hm => by
      have hab : a = b := by
        rcases List.mem_cons.1 ((hm a).1 (by simp)) with h | h
        · exact h
        · rcases List.mem_cons.1 ((hm b).2 (by simp)) with h' | h'
          · exact h'.symm
          · exact absurd (List.rel_of_pairwise_cons h₂ h)
              (keyLt_asymm (List.rel_of_pairwise_cons h₁ h'))
      subst hab
      have hnot₁ : a ∉ l₁ := fun h =>
        keyLt_irrefl (List.rel_of_pairwise_cons h₁ h)
      have hnot₂ : a ∉ l₂ := fun h =>
        keyLt_irrefl (List.rel_of_pairwise_cons h₂ h)
      have htail : ∀ x, x ∈ l₁ ↔ x ∈ l₂ := by
        intro x
        constructor
        · intro hx
          rcases List.mem_cons.1 ((hm x).1 (List.mem_cons_of_mem _ hx)) with h | h
          · exact absurd (h ▸ hx) hnot₁
          · exact h
        · intro hx
          rcases List.mem_cons.1 ((hm x).2 (List.mem_cons_of_mem _ hx)) with h | h
          · exact absurd (h ▸ hx) hnot₂
          · exact h
      exact congrArg (a :: ·) (eq_of_sorted_mem (List.pairwise_cons.1 h₁).2
        (List.pairwise_cons.1 h₂).2 htail)

/-- Building a JSON object and reading its members back sorts them: whatever
order the members arrive in, what comes out is the strictly key-sorted list
they are a permutation of. The printer's own objects are sorted already, so
most uses take `l = l'`. -/
theorem jFields_mkObj_perm {l l' : List (String × Json)}
    (hperm : l.Perm l') (h : l'.Pairwise keyLt) :
    jFields (Json.mkObj l) = some l' := by
  have hwf : (Std.TreeMap.Raw.ofList l compare).WF := Std.TreeMap.Raw.WF.ofList
  have hsym : ∀ {a b : String × Json},
      ¬ compare a.1 b.1 = .eq → ¬ compare b.1 a.1 = .eq := by
    intro a b hab hba
    exact hab (Std.OrientedCmp.eq_symm hba)
  have hdist : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    (List.Perm.pairwise_iff (fun {_ _} => hsym) hperm).2
      (h.imp fun hab => by
        simp only [keyLt] at hab
        rw [hab]
        exact fun hh => by cases hh)
  refine congrArg some (eq_of_sorted_mem ?_ h ?_)
  · exact Std.TreeMap.Raw.ordered_keys_toList hwf
  · intro x
    obtain ⟨k, v⟩ := x
    rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf]
    constructor
    · intro hg
      by_cases hk : (l.map Prod.fst).contains k
      · obtain ⟨v', hv'⟩ : ∃ v', (k, v') ∈ l := by
          have hk' : k ∈ l.map Prod.fst := by simpa using hk
          obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hk'
          exact ⟨p.2, by rw [← hpk]; simpa using hp⟩
        have := Std.TreeMap.Raw.getElem?_ofList_of_mem
          (k := k) (k' := k) Std.ReflCmp.compare_self hdist hv'
        rw [this] at hg
        simp only [Option.some.injEq] at hg
        exact hperm.mem_iff.1 (hg ▸ hv')
      · rw [Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false
          (by simpa using hk)] at hg
        exact absurd hg (by simp)
    · intro hx
      exact Std.TreeMap.Raw.getElem?_ofList_of_mem
        (k := k) (k' := k) Std.ReflCmp.compare_self hdist
        (hperm.mem_iff.2 hx)

/-- The common case: the members were already sorted. -/
theorem jFields_mkObj {l : List (String × Json)} (h : l.Pairwise keyLt) :
    jFields (Json.mkObj l) = some l :=
  jFields_mkObj_perm (List.Perm.refl l) h

/-! ## The bridge from the printer's tree to the parser's

`jsonOf` is what a parser would have built from a canonical document: the
same `Json.mkObj` for an object, so that reading its members back is the
`Std.TreeMap` fact above and nothing else. -/

mutual

def jsonOf : JVal → Json
  | .null => .null
  | .bool b => .bool b
  | .int v => .num ⟨v, 0⟩
  | .str s => .str s
  | .arr items => .arr (jsonOfList items).toArray
  | .obj fields => Json.mkObj (jsonOfFields fields)

def jsonOfList : List JVal → List Json
  | [] => []
  | v :: rest => jsonOf v :: jsonOfList rest

def jsonOfFields : List (String × JVal) → List (String × Json)
  | [] => []
  | (k, v) :: rest => (k, jsonOf v) :: jsonOfFields rest

end

/-! ## Reading a leaf back -/

theorem jStr_str {s w : String} : jStr (jsonOf (.str s)) w = .ok s := rfl

theorem jBool_bool {b : Bool} {w : String} :
    jBool (jsonOf (.bool b)) w = .ok b := rfl

theorem jInt_int {v : Int} {w : String} : jInt (jsonOf (.int v)) w = .ok v := rfl

theorem jNat_int {n : Nat} {w : String} :
    jNat (jsonOf (.int (n : Int))) w = .ok n := by
  rw [jNat, jInt_int]
  simp only [bind, Except.bind]
  rw [if_neg (by omega)]
  simp

theorem jArr_arr {items : List JVal} {w : String} :
    jArr (jsonOf (.arr items)) w = .ok (jsonOfList items) := by
  rw [jsonOf, jArr]
  simp only [Json.getArr?, pure, Except.pure]

theorem jName_str {s w : String} (h : isIdentifier s = true) :
    jName (jsonOf (.str s)) w = .ok s := by
  rw [jName, jStr_str]
  simp only [bind, Except.bind]
  rw [if_pos h]

/-! ## Reading an object back

Every object the printer builds has literal keys, so `jobj`'s sort and the
map's own order both compute; `simp [jobj, List.mergeSort]` is what runs
them. The two clauses whose keys are not literal — a constant's fields and a
struct value's — are where `jFields_mkObj` earns its keep. -/

theorem jsonOf_obj {fields : List (String × JVal)} :
    jsonOf (.obj fields) = Json.mkObj (jsonOfFields fields) := by
  rw [jsonOf.eq_def]

theorem jsonOfFields_eq_map {fields : List (String × JVal)} :
    jsonOfFields fields = fields.map (fun kv => (kv.1, jsonOf kv.2)) := by
  induction fields with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      rw [jsonOfFields, ih, List.map_cons]

theorem jsonOfList_eq_map {items : List JVal} :
    jsonOfList items = items.map jsonOf := by
  induction items with
  | nil => rfl
  | cons v rest ih => rw [jsonOfList, ih, List.map_cons]

/-- A one-key object, which is how every tagged form is spelled. -/
theorem jsonOf_jobj_one {k : String} {v : JVal} :
    jsonOf (jobj [(k, v)]) = Json.mkObj [(k, jsonOf v)] := by
  rw [show jobj [(k, v)] = JVal.obj [(k, v)] by simp [jobj], jsonOf_obj,
    jsonOfFields, jsonOfFields]

theorem tagged_one {k : String} {v : JVal} {w : String} :
    tagged (jsonOf (jobj [(k, v)])) w = .ok (k, jsonOf v) := by
  rw [jsonOf_jobj_one, tagged]
  rfl

/-! ## Bytes, spelled as hex

The one leaf whose round trip is arithmetic rather than a constructor
match. `hexBytes` writes two lowercase digits a byte and `hexToBytes` reads
them back, and nothing about a program has to hold for that to work — which
is why this is proved outright rather than assumed of a canonical program. -/

theorem hexValue_hexDigit {d : Nat} (h : d < 16) :
    hexValue (hexDigit d) = some d := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem toList_foldl_append : ∀ (l : List String) (s : String),
    (l.foldl (· ++ ·) s).toList = s.toList ++ (l.map String.toList).flatten
  | [], s => by simp
  | x :: rest, s => by
      rw [List.foldl_cons, toList_foldl_append rest (s ++ x)]
      simp [String.toList_append]

theorem hexToBytes_hex2 {b : UInt8} {rest : List Char} :
    hexToBytes ((hex2 b.toNat).toList ++ rest)
      = (hexToBytes rest).map (fun more => UInt8.ofNat b.toNat :: more) := by
  have hb : b.toNat < 256 := b.toNat_lt_size
  have h2 : (hex2 b.toNat).toList
      = [hexDigit (b.toNat / 16 % 16), hexDigit (b.toNat % 16)] := by
    rw [hex2, String.toList_ofList]
  rw [h2]
  simp only [List.cons_append, List.nil_append, hexToBytes]
  rw [hexValue_hexDigit (by omega), hexValue_hexDigit (by omega)]
  simp only [Option.bind, bind, Option.some.injEq]
  cases hexToBytes rest with
  | none => rfl
  | some more =>
      simp only [Option.map_some]
      rw [show 16 * (b.toNat / 16 % 16) + b.toNat % 16 = b.toNat by omega]

theorem hexToBytes_hexBytes : ∀ (data : List UInt8),
    hexToBytes (hexBytes data).toList = some data
  | [] => rfl
  | b :: rest => by
      have hfold : (hexBytes (b :: rest)).toList
          = (hex2 b.toNat).toList ++ (hexBytes rest).toList := by
        simp only [hexBytes, List.map_cons, List.foldl_cons,
          toList_foldl_append]
        simp
      rw [hfold, hexToBytes_hex2, hexToBytes_hexBytes rest]
      simp


/-! ## Types

The first of the five families, and the template for the rest: the depth the
decoder's budget has to cover, the canonicality the statement needs, and the
inversion itself. -/

def tyDepth : Ty → Nat
  | .vec e _ => tyDepth e + 1
  | .frozen t => tyDepth t + 1
  | _ => 1

/-- What a type has to satisfy to survive the round trip: only that the names
it carries are names, which is what the decoder checks. -/
def Ty.Canonical : Ty → Prop
  | .enum n => isIdentifier n = true
  | .struct n => isIdentifier n = true
  | .vec e _ => e.Canonical
  | .frozen t => t.Canonical
  | _ => True

theorem decodeTy_tyJ : ∀ (n : Nat) (t : Ty), tyDepth t ≤ n → t.Canonical →
    decodeTy n (jsonOf (tyJ t)) = .ok t
  | 0, t, h, _ => by cases t <;> simp [tyDepth] at h
  | n + 1, t, h, hc => by
      match t with
      | .bool => rfl
      | .int .u8 => rfl
      | .int .i32 => rfl
      | .int .u32 => rfl
      | .int .counter => rfl
      | .bytes => rfl
      | .enum m =>
          rw [tyJ, jsonOf_jobj_one, decodeTy]
          simp only [Json.mkObj, Json.getStr?, jsonOf, tagged, throw, throwThe,
            MonadExceptOf.throw]
          rw [show jFields (Json.obj (Std.TreeMap.Raw.ofList
              [("enum", Json.str m)] compare))
              = some [("enum", Json.str m)] from rfl]
          simp only [bind, Except.bind]
          rw [show jName (Json.str m) "an enum type name" = .ok m by
            simp only [jName, jStr, Json.getStr?, pure, Except.pure, bind,
              Except.bind]
            rw [if_pos (show isIdentifier m = true from hc)]]
          rfl
      | .struct m =>
          rw [tyJ, jsonOf_jobj_one, decodeTy]
          simp only [Json.mkObj, Json.getStr?, jsonOf, tagged, throw, throwThe,
            MonadExceptOf.throw]
          rw [show jFields (Json.obj (Std.TreeMap.Raw.ofList
              [("struct", Json.str m)] compare))
              = some [("struct", Json.str m)] from rfl]
          simp only [bind, Except.bind]
          rw [show jName (Json.str m) "a struct type name" = .ok m by
            simp only [jName, jStr, Json.getStr?, pure, Except.pure, bind,
              Except.bind]
            rw [if_pos (show isIdentifier m = true from hc)]]
          rfl
      | .frozen inner =>
          rw [tyJ, jsonOf_jobj_one, decodeTy]
          simp only [Json.mkObj, Json.getStr?, tagged, throw, throwThe,
            MonadExceptOf.throw]
          rw [show jFields (Json.obj (Std.TreeMap.Raw.ofList
              [("frozen", jsonOf (tyJ inner))] compare))
              = some [("frozen", jsonOf (tyJ inner))] from rfl]
          simp only [bind, Except.bind]
          rw [decodeTy_tyJ n inner (by simp only [tyDepth] at h; omega) hc]
          rfl
      | .vec elem max =>
          rw [tyJ, jsonOf_jobj_one, decodeTy]
          simp only [Json.mkObj, Json.getStr?, tagged, throw, throwThe,
            MonadExceptOf.throw]
          rw [show jFields (Json.obj (Std.TreeMap.Raw.ofList
              [("vec", jsonOf (jobj [("elem", tyJ elem),
                ("max", JVal.int (max : Int))]))] compare))
              = some [("vec", jsonOf (jobj [("elem", tyJ elem),
                ("max", JVal.int (max : Int))]))] from rfl]
          simp only [bind, Except.bind]
          rw [show jobj [("elem", tyJ elem), ("max", JVal.int (max : Int))]
              = JVal.obj [("elem", tyJ elem), ("max", JVal.int (max : Int))] by
            simp [jobj, List.mergeSort]]
          rw [jsonOf_obj, jsonOfFields, jsonOfFields, jsonOfFields,
            show closed (Json.mkObj [("elem", jsonOf (tyJ elem)),
                ("max", jsonOf (JVal.int (max : Int)))]) "a vec type"
                ["elem", "max"]
              = .ok [("elem", jsonOf (tyJ elem)),
                ("max", jsonOf (JVal.int (max : Int)))] from rfl]
          simp only []
          rw [show need [("elem", jsonOf (tyJ elem)),
                ("max", jsonOf (JVal.int (max : Int)))] "a vec type" "elem"
              = .ok (jsonOf (tyJ elem)) from rfl]
          simp only []
          rw [decodeTy_tyJ n elem (by simp only [tyDepth] at h; omega) hc]
          simp only []
          rw [show need [("elem", jsonOf (tyJ elem)),
                ("max", jsonOf (JVal.int (max : Int)))] "a vec type" "max"
              = .ok (jsonOf (JVal.int (max : Int))) from rfl]
          simp only []
          rw [jNat_int]
          rfl

end Pcrevera.Tir
