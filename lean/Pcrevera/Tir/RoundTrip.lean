import Std.Data.TreeMap.Raw
import Pcrevera.Tir.Decode

/-!
# Gate 2: the decoder inverts the printer (I-2)

`Tir/PrintCheck.lean` runs the round trip on the programs there happen to be,
and gate 3 runs it on the artifact. This file is where that becomes a theorem
about every canonical program — and it is under way rather than finished.
What is here is the bridge to `Lean.Json` and the first three of the five
decoder families: the types, the constants, and the expressions and places.
The statements and the declarations and the program itself are outstanding,
and PLAN-M7.md section 11 says what they are expected to cost.

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

/-- The order a `Json` object keeps its members in. -/
def keyLt {α : Type} (a b : String × α) : Prop := compare a.1 b.1 = .lt

/-- Strictly sorted by key, in that same order.

This is what a list of members has to be for the printer's object to hand it
back unchanged, and it is the one thing about a program that the decoder can
neither check nor repair — it reads whatever order the map is in. -/
def SortedKeys {α : Type} (l : List (String × α)) : Prop := l.Pairwise keyLt

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
    (hperm : l.Perm l') (h : SortedKeys l') :
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
theorem jFields_mkObj {l : List (String × Json)} (h : SortedKeys l) :
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

/-- A form with more than one key, once the sort has run.

The printer writes members in whatever order reads best — `op` before `left`
and `right`, for one — and `jobj` puts them in key order, so `l'` is the
sorted list and running the sort is what the caller supplies. `List.mergeSort`
is well-founded, so it takes `simp [jobj, List.mergeSort]` rather than `rfl`;
it computes even where the values are variables, since only the keys are
compared. -/
theorem jsonOf_jobj_fields {l l' : List (String × JVal)}
    (h : jobj l = JVal.obj l') :
    jsonOf (jobj l) = Json.mkObj (jsonOfFields l') := by
  rw [h, jsonOf_obj]

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
  simp only [Option.bind, bind]
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

/-- Canonicality is a side condition, so it has to be one a machine can
settle: the artifact's own premise will be discharged by reduction, not by
hand. -/
instance decTyCanonical : (t : Ty) → Decidable t.Canonical
  | .bool | .int _ | .bytes => isTrue trivial
  | .enum n => inferInstanceAs (Decidable (isIdentifier n = true))
  | .struct n => inferInstanceAs (Decidable (isIdentifier n = true))
  | .vec e _ => decTyCanonical e
  | .frozen t => decTyCanonical t

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

/-! ### The predicate, on a type

The three checks every family carries from here on. `tyDepth` is a number the
composed theorem will have to add up, so what matters is that it is the budget
the decoder actually spends and not merely a bound on it — hence the second
guard, which fails one unit short. -/

private def tySample : Ty := .vec (.frozen (.struct "node")) 8

#guard tyDepth tySample == 3
#guard (decodeTy 2 (jsonOf (tyJ tySample))).toOption.isNone

example : tySample.Canonical := by decide

example : ¬ (Ty.enum "not a name").Canonical := by decide

example : decodeTy (tyDepth tySample) (jsonOf (tyJ tySample)) = .ok tySample :=
  decodeTy_tyJ _ _ (Nat.le_refl _) (by decide)

/-! ## Constants

The second family, and the first with something to say about order. A
constant's fields are printed as an object, and an object hands its members
back sorted, so the entries have to be in that order already or the decoder
reads a different list than the printer was given. That is the whole of the
ordering premise, and constants are where it starts to matter.

The other two premises are already discharged: the bytes clause spends
`hexToBytes_hexBytes` and needs nothing of the program, and the fields clause
spends `jFields_mkObj_perm`, whose keys are the first ones in the schema that
are not literals. -/

mutual

/-- The budget a constant costs, decrementing where `decodeConst` does. -/
def constDepth : ConstValue → Nat
  | .elems items => constItemsDepth items + 1
  | .fields entries => constEntriesDepth entries + 1
  | _ => 1

def constItemsDepth : List ConstValue → Nat
  | [] => 0
  | v :: rest => max (constDepth v) (constItemsDepth rest)

def constEntriesDepth : List (String × ConstValue) → Nat
  | [] => 0
  | (_, v) :: rest => max (constDepth v) (constEntriesDepth rest)

end

mutual

/-- What a constant has to satisfy to survive the round trip: its names are
names, and the members of a struct value are in the order an object keeps
them. Nothing else — an integer, a boolean and a byte string all come back
whatever they hold. -/
def ConstValue.Canonical : ConstValue → Prop
  | .variant v => isIdentifier v = true
  | .elems items => ConstItemsCanonical items
  | .fields entries => SortedKeys entries ∧ ConstEntriesCanonical entries
  | _ => True

def ConstItemsCanonical : List ConstValue → Prop
  | [] => True
  | v :: rest => v.Canonical ∧ ConstItemsCanonical rest

def ConstEntriesCanonical : List (String × ConstValue) → Prop
  | [] => True
  | (k, v) :: rest =>
      isIdentifier k = true ∧ v.Canonical ∧ ConstEntriesCanonical rest

end

instance {α : Type} (a b : String × α) : Decidable (keyLt a b) :=
  inferInstanceAs (Decidable (compare a.1 b.1 = .lt))

instance {α : Type} (l : List (String × α)) : Decidable (SortedKeys l) :=
  inferInstanceAs (Decidable (l.Pairwise keyLt))

mutual

instance decConstCanonical : (v : ConstValue) → Decidable v.Canonical
  | .int _ | .bool _ | .bytes _ => isTrue trivial
  | .variant m => inferInstanceAs (Decidable (isIdentifier m = true))
  | .elems items => decConstItemsCanonical items
  | .fields entries =>
      @instDecidableAnd _ _ inferInstance (decConstEntriesCanonical entries)

instance decConstItemsCanonical :
    (items : List ConstValue) → Decidable (ConstItemsCanonical items)
  | [] => isTrue trivial
  | v :: rest =>
      @instDecidableAnd _ _ (decConstCanonical v) (decConstItemsCanonical rest)

instance decConstEntriesCanonical :
    (entries : List (String × ConstValue)) →
      Decidable (ConstEntriesCanonical entries)
  | [] => isTrue trivial
  | (_, v) :: rest =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ (decConstCanonical v)
          (decConstEntriesCanonical rest))

end

theorem constItemsJ_eq_map {items : List ConstValue} :
    constItemsJ items = items.map constJ := by
  induction items with
  | nil => rfl
  | cons v rest ih => rw [constItemsJ, ih, List.map_cons]

theorem constEntries_eq_map {entries : List (String × ConstValue)} :
    constEntries entries = entries.map (fun kv => (kv.1, constJ kv.2)) := by
  induction entries with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      rw [constEntries, ih, List.map_cons]

/-- The members of a struct value, read back off the object the printer built
out of them. `jobj` sorts, so what comes back is a permutation of what went
in; the ordering premise is what makes that permutation the identity. -/
theorem jFields_constEntries {entries : List (String × ConstValue)}
    (h : SortedKeys entries) :
    jFields (jsonOf (jobj (constEntries entries)))
      = some (jsonOfFields (constEntries entries)) := by
  rw [show jobj (constEntries entries)
      = JVal.obj ((constEntries entries).mergeSort fun a b => a.1 ≤ b.1)
      from rfl, jsonOf_obj]
  refine jFields_mkObj_perm ?_ ?_
  · rw [jsonOfFields_eq_map, jsonOfFields_eq_map]
    exact List.Perm.map _ (List.mergeSort_perm _ _)
  · rw [jsonOfFields_eq_map, constEntries_eq_map, List.map_map]
    show List.Pairwise _ (List.map _ entries)
    rw [List.pairwise_map]
    exact h

/-- Reading past a step that has already succeeded. -/
private theorem ok_bind {α β : Type} {a : α} {f : α → D β} :
    (do let x ← (.ok a : D α); f x) = f a := rfl

/-! The inversion itself, shaped like the decoder's own recursion: the budget
falls between a constant and its members, and within one level the list walks
structurally. Each clause unfolds one step of the decoder, says in `show` what
that step left, and then spends the leaf lemma the step was waiting on. -/

mutual

theorem decodeConst_constJ : ∀ (n : Nat) (v : ConstValue),
    constDepth v ≤ n → v.Canonical →
    decodeConst n (jsonOf (constJ v)) = .ok v
  | 0, v, h, _ => by cases v <;> simp [constDepth] at h
  | _ + 1, .int i, _, _ => by rw [constJ, decodeConst]; rfl
  | _ + 1, .bool b, _, _ => by rw [constJ, decodeConst]; rfl
  | _ + 1, .variant m, _, hc => by
      rw [constJ, jsonOf_jobj_one, decodeConst]
      show (do
        let s ← jName (jsonOf (JVal.str m)) "a variant"
        .ok (ConstValue.variant s)) = .ok (.variant m)
      rw [jName_str (show isIdentifier m = true from hc)]
      rfl
  | _ + 1, .bytes data, _, _ => by
      rw [constJ, jsonOf_jobj_one, decodeConst]
      show (do
        let s ← jStr (jsonOf (JVal.str (hexBytes data))) "a byte string"
        match hexToBytes s.toList with
        | some d => (.ok (ConstValue.bytes d) : D ConstValue)
        | none => .error "a byte string is even-length lowercase hex")
        = .ok (.bytes data)
      simp only [jStr_str, ok_bind, hexToBytes_hexBytes]
  | n + 1, .elems items, h, hc => by
      rw [constJ, jsonOf_jobj_one, decodeConst]
      show (do
        let js ← jArr (jsonOf (JVal.arr (constItemsJ items)))
          "the elements of a constant"
        let vs ← decodeConstList n js
        .ok (ConstValue.elems vs)) = .ok (.elems items)
      simp only [jArr_arr, ok_bind, decodeConstList_constItemsJ n items
        (by simp only [constDepth] at h; omega) hc]
  | n + 1, .fields entries, h, hc => by
      rw [constJ, jsonOf_jobj_one, decodeConst]
      show (match jFields (jsonOf (jobj (constEntries entries))) with
        | none =>
            (.error "the fields of a constant must be an object" : D ConstValue)
        | some fs => do
            let vs ← decodeConstFields n fs
            .ok (ConstValue.fields vs)) = .ok (.fields entries)
      simp only [jFields_constEntries hc.1, decodeConstFields_constEntries n
        entries (by simp only [constDepth] at h; omega) hc.2, ok_bind]
termination_by n _ _ _ => (n, 0)

theorem decodeConstList_constItemsJ : ∀ (n : Nat) (items : List ConstValue),
    constItemsDepth items ≤ n → ConstItemsCanonical items →
    decodeConstList n (jsonOfList (constItemsJ items)) = .ok items
  | _, [], _, _ => by rw [constItemsJ, jsonOfList, decodeConstList]
  | n, v :: rest, h, hc => by
      rw [constItemsJ, jsonOfList, decodeConstList,
        decodeConst_constJ n v
          (by simp only [constItemsDepth] at h; omega) hc.1,
        decodeConstList_constItemsJ n rest
          (by simp only [constItemsDepth] at h; omega) hc.2]
      rfl
termination_by n items _ _ => (n, items.length + 1)

theorem decodeConstFields_constEntries :
    ∀ (n : Nat) (entries : List (String × ConstValue)),
      constEntriesDepth entries ≤ n → ConstEntriesCanonical entries →
      decodeConstFields n (jsonOfFields (constEntries entries)) = .ok entries
  | _, [], _, _ => by rw [constEntries, jsonOfFields, decodeConstFields]
  | n, (k, v) :: rest, h, hc => by
      rw [constEntries, jsonOfFields, decodeConstFields, if_pos hc.1,
        decodeConst_constJ n v
          (by simp only [constEntriesDepth] at h; omega) hc.2.1,
        decodeConstFields_constEntries n rest
          (by simp only [constEntriesDepth] at h; omega) hc.2.2]
      rfl
termination_by n entries _ _ => (n, entries.length + 1)

end

/-! ### The predicate, on a constant

A canonicality nobody can settle is one that can only be stated, so this is
where the decision procedure earns its place: a constant nesting all three
container shapes, the two ways of failing that the premise is there to rule
out, and the theorem instantiated at exactly the depth `constDepth` gives.

The budget is tight rather than merely sufficient, and the second guard is
what keeps it that way: one unit short and the same constant stops decoding,
so a `constDepth` that drifted upward would show here. -/

private def constSample : ConstValue :=
  .fields [("a", .int 1), ("b", .bytes [0xff, 0x00, 0x7a]),
    ("c", .elems [.bool true, .variant "red"])]

#guard constDepth constSample == 3
#guard (decodeConst 2 (jsonOf (constJ constSample))).toOption.isNone

example : constSample.Canonical := by decide

example : ¬ (ConstValue.fields [("b", .int 0), ("a", .int 1)]).Canonical := by
  decide

example : ¬ (ConstValue.variant "not a name").Canonical := by decide

example : decodeConst (constDepth constSample) (jsonOf (constJ constSample))
    = .ok constSample :=
  decodeConst_constJ _ _ (Nat.le_refl _) (by decide)

/-! ## Expressions and places

The third family, and much the widest: seventeen expression forms and three
place forms, most of them read out of a closed set of keys rather than a bare
payload. Nothing about the shape of the induction is new — the budget falls
between an expression and its parts, and a struct value's members walk
structurally within one level, exactly as a constant's did.

Three things are new about the clauses themselves. A `cast` carries a type, so
its clause spends `decodeTy_tyJ` and the premise reaches back into the first
family. Several forms print their keys out of order, so `jobj`'s sort is doing
real work here for the first time and `jsonOf_jobj_fields` is what runs it. And
four forms spell the operator in the tag or in an `op` member, which the
decoder maps back through a partial function; those clauses finish by casing on
the operator, since that is the only way the decoder's own match reduces.

A struct value's fields are the second and last place in the schema where the
keys are a program's own names, so `SortedKeys` and `jFields_mkObj_perm` come
back exactly as they were for a constant's fields. Places are the same shape
one type down, and the only reason they are a separate induction is that the
decoder keeps them separate — a place's index is an expression, so they read
in that order and not the other way. -/

mutual

/-- The budget an expression costs, decrementing where `decodeExpr` does. A
`cast` also pays for its type, since the decoder spends the same budget on
it. -/
def exprDepth : Expr → Nat
  | .field base _ => exprDepth base + 1
  | .index base i => max (exprDepth base) (exprDepth i) + 1
  | .len a => exprDepth a + 1
  | .cap a => exprDepth a + 1
  | .un _ a => exprDepth a + 1
  | .bin _ l r => max (exprDepth l) (exprDepth r) + 1
  | .cmp _ l r => max (exprDepth l) (exprDepth r) + 1
  | .divrem _ l r f => max (exprDepth l) (max (exprDepth r) (exprDepth f)) + 1
  | .shift _ a _ => exprDepth a + 1
  | .cast t a => max (tyDepth t) (exprDepth a) + 1
  | .logical _ l r => max (exprDepth l) (exprDepth r) + 1
  | .structVal _ entries => exprEntriesDepth entries + 1
  | _ => 1

def exprEntriesDepth : List (String × Expr) → Nat
  | [] => 0
  | (_, e) :: rest => max (exprDepth e) (exprEntriesDepth rest)

end

mutual

/-- What an expression has to satisfy to survive the round trip: every name it
carries is a name, and a struct value's members are in the order an object
keeps them. The operators cost nothing — they are written from a closed set
and read back through the inverse of the same table. -/
def Expr.Canonical : Expr → Prop
  | .var n => isIdentifier n = true
  | .constRef n => isIdentifier n = true
  | .field base n => base.Canonical ∧ isIdentifier n = true
  | .index base i => base.Canonical ∧ i.Canonical
  | .len a => a.Canonical
  | .cap a => a.Canonical
  | .un _ a => a.Canonical
  | .bin _ l r => l.Canonical ∧ r.Canonical
  | .cmp _ l r => l.Canonical ∧ r.Canonical
  | .divrem _ l r f => l.Canonical ∧ r.Canonical ∧ f.Canonical
  | .shift _ a _ => a.Canonical
  | .cast t a => t.Canonical ∧ a.Canonical
  | .logical _ l r => l.Canonical ∧ r.Canonical
  | .enumVal t v => isIdentifier t = true ∧ isIdentifier v = true
  | .structVal t entries =>
      isIdentifier t = true ∧ SortedKeys entries
        ∧ ExprEntriesCanonical entries
  | _ => True

def ExprEntriesCanonical : List (String × Expr) → Prop
  | [] => True
  | (k, e) :: rest =>
      isIdentifier k = true ∧ e.Canonical ∧ ExprEntriesCanonical rest

end

mutual

instance decExprCanonical : (e : Expr) → Decidable e.Canonical
  | .litInt _ _ | .litBool _ => isTrue trivial
  | .var n => inferInstanceAs (Decidable (isIdentifier n = true))
  | .constRef n => inferInstanceAs (Decidable (isIdentifier n = true))
  | .field base _ => @instDecidableAnd _ _ (decExprCanonical base) inferInstance
  | .index base i =>
      @instDecidableAnd _ _ (decExprCanonical base) (decExprCanonical i)
  | .len a => decExprCanonical a
  | .cap a => decExprCanonical a
  | .un _ a => decExprCanonical a
  | .bin _ l r =>
      @instDecidableAnd _ _ (decExprCanonical l) (decExprCanonical r)
  | .cmp _ l r =>
      @instDecidableAnd _ _ (decExprCanonical l) (decExprCanonical r)
  | .divrem _ l r f =>
      @instDecidableAnd _ _ (decExprCanonical l)
        (@instDecidableAnd _ _ (decExprCanonical r) (decExprCanonical f))
  | .shift _ a _ => decExprCanonical a
  | .cast t a => @instDecidableAnd _ _ (decTyCanonical t) (decExprCanonical a)
  | .logical _ l r =>
      @instDecidableAnd _ _ (decExprCanonical l) (decExprCanonical r)
  | .enumVal _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .structVal _ entries =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ inferInstance (decExprEntriesCanonical entries))

instance decExprEntriesCanonical : (entries : List (String × Expr)) →
    Decidable (ExprEntriesCanonical entries)
  | [] => isTrue trivial
  | (_, e) :: rest =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ (decExprCanonical e)
          (decExprEntriesCanonical rest))

end

theorem exprEntries_eq_map {entries : List (String × Expr)} :
    exprEntries entries = entries.map (fun kv => (kv.1, exprJ kv.2)) := by
  induction entries with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, e⟩ := kv
      rw [exprEntries, ih, List.map_cons]

/-- The members of a struct value, read back off the object the printer built
out of them. The same argument as for a constant's fields, one family up. -/
theorem jFields_exprEntries {entries : List (String × Expr)}
    (h : SortedKeys entries) :
    jFields (jsonOf (jobj (exprEntries entries)))
      = some (jsonOfFields (exprEntries entries)) := by
  rw [show jobj (exprEntries entries)
      = JVal.obj ((exprEntries entries).mergeSort fun a b => a.1 ≤ b.1)
      from rfl, jsonOf_obj]
  refine jFields_mkObj_perm ?_ ?_
  · rw [jsonOfFields_eq_map, jsonOfFields_eq_map]
    exact List.Perm.map _ (List.mergeSort_perm _ _)
  · rw [jsonOfFields_eq_map, exprEntries_eq_map, List.map_map]
    show List.Pairwise _ (List.map _ entries)
    rw [List.pairwise_map]
    exact h

mutual

theorem decodeExpr_exprJ : ∀ (n : Nat) (e : Expr),
    exprDepth e ≤ n → e.Canonical →
    decodeExpr n (jsonOf (exprJ e)) = .ok e
  | 0, e, h, _ => by cases e <;> simp [exprDepth] at h
  | _ + 1, .litInt t v, _, _ => by
      cases t <;> · rw [exprJ, decodeExpr, tagged_one]; rfl
  | _ + 1, .litBool b, _, _ => by
      rw [exprJ, decodeExpr, tagged_one]
      show (do
        let v ← jBool (jsonOf (JVal.bool b)) "a bool literal"
        .ok (Expr.litBool v)) = .ok (.litBool b)
      rw [jBool_bool]
      rfl
  | _ + 1, .var m, _, hc => by
      rw [exprJ, decodeExpr, tagged_one]
      show (do
        let s ← jName (jsonOf (JVal.str m)) "a variable"
        .ok (Expr.var s)) = .ok (.var m)
      rw [jName_str hc]
      rfl
  | _ + 1, .constRef m, _, hc => by
      rw [exprJ, decodeExpr, tagged_one]
      show (do
        let s ← jName (jsonOf (JVal.str m)) "a constant reference"
        .ok (Expr.constRef s)) = .ok (.constRef m)
      rw [jName_str hc]
      rfl
  | n + 1, .field base m, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("base", exprJ base), ("name", .str m)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ base))
        let s ← jName (jsonOf (JVal.str m)) "a field name"
        .ok (Expr.field v s)) = .ok (.field base m)
      rw [decodeExpr_exprJ n base (by simp only [exprDepth] at h; omega) hc.1,
        ok_bind, jName_str hc.2]
      rfl
  | n + 1, .index base i, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("base", exprJ base), ("index", exprJ i)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ base))
        let w ← decodeExpr n (jsonOf (exprJ i))
        .ok (Expr.index v w)) = .ok (.index base i)
      rw [decodeExpr_exprJ n base (by simp only [exprDepth] at h; omega) hc.1,
        ok_bind,
        decodeExpr_exprJ n i (by simp only [exprDepth] at h; omega) hc.2]
      rfl
  | n + 1, .len a, h, hc => by
      rw [exprJ, decodeExpr, tagged_one]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ a))
        .ok (Expr.len v)) = .ok (.len a)
      rw [decodeExpr_exprJ n a (by simp only [exprDepth] at h; omega) hc]
      rfl
  | n + 1, .cap a, h, hc => by
      rw [exprJ, decodeExpr, tagged_one]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ a))
        .ok (Expr.cap v)) = .ok (.cap a)
      rw [decodeExpr_exprJ n a (by simp only [exprDepth] at h; omega) hc]
      rfl
  | n + 1, .un op a, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("arg", exprJ a), ("op", .str op.name)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let o ← jStr (jsonOf (JVal.str op.name)) "an operator"
        match unOp o with
        | none => (.error s!"unknown operator {o}" : D Expr)
        | some o' => do
            let v ← decodeExpr n (jsonOf (exprJ a))
            .ok (Expr.un o' v)) = .ok (.un op a)
      rw [jStr_str, ok_bind,
        decodeExpr_exprJ n a (by simp only [exprDepth] at h; omega) hc]
      cases op <;> rfl
  | n + 1, .bin op l r, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("left", exprJ l), ("op", .str op.name),
          ("right", exprJ r)]) (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let o ← jStr (jsonOf (JVal.str op.name)) "an operator"
        match binOp o with
        | none => (.error s!"unknown operator {o}" : D Expr)
        | some o' => do
            let v ← decodeExpr n (jsonOf (exprJ l))
            let w ← decodeExpr n (jsonOf (exprJ r))
            .ok (Expr.bin o' v w)) = .ok (.bin op l r)
      rw [jStr_str, ok_bind,
        decodeExpr_exprJ n l (by simp only [exprDepth] at h; omega) hc.1,
        decodeExpr_exprJ n r (by simp only [exprDepth] at h; omega) hc.2]
      cases op <;> rfl
  | n + 1, .cmp op l r, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("left", exprJ l), ("op", .str op.name),
          ("right", exprJ r)]) (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let o ← jStr (jsonOf (JVal.str op.name)) "an operator"
        match cmpOp o with
        | none => (.error s!"unknown operator {o}" : D Expr)
        | some o' => do
            let v ← decodeExpr n (jsonOf (exprJ l))
            let w ← decodeExpr n (jsonOf (exprJ r))
            .ok (Expr.cmp o' v w)) = .ok (.cmp op l r)
      rw [jStr_str, ok_bind,
        decodeExpr_exprJ n l (by simp only [exprDepth] at h; omega) hc.1,
        decodeExpr_exprJ n r (by simp only [exprDepth] at h; omega) hc.2]
      cases op <;> rfl
  | n + 1, .divrem .div l r f, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("fallback", exprJ f), ("left", exprJ l),
          ("right", exprJ r)]) (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ l))
        let w ← decodeExpr n (jsonOf (exprJ r))
        let x ← decodeExpr n (jsonOf (exprJ f))
        .ok (Expr.divrem .div v w x)) = .ok (.divrem .div l r f)
      rw [decodeExpr_exprJ n l (by simp only [exprDepth] at h; omega) hc.1,
        ok_bind,
        decodeExpr_exprJ n r (by simp only [exprDepth] at h; omega) hc.2.1,
        ok_bind,
        decodeExpr_exprJ n f (by simp only [exprDepth] at h; omega) hc.2.2]
      rfl
  | n + 1, .divrem .rem l r f, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("fallback", exprJ f), ("left", exprJ l),
          ("right", exprJ r)]) (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ l))
        let w ← decodeExpr n (jsonOf (exprJ r))
        let x ← decodeExpr n (jsonOf (exprJ f))
        .ok (Expr.divrem .rem v w x)) = .ok (.divrem .rem l r f)
      rw [decodeExpr_exprJ n l (by simp only [exprDepth] at h; omega) hc.1,
        ok_bind,
        decodeExpr_exprJ n r (by simp only [exprDepth] at h; omega) hc.2.1,
        ok_bind,
        decodeExpr_exprJ n f (by simp only [exprDepth] at h; omega) hc.2.2]
      rfl
  | n + 1, .shift op a c, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("arg", exprJ a), ("count", .int (c : Int)),
          ("op", .str op.name)]) (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let o ← jStr (jsonOf (JVal.str op.name)) "an operator"
        match shiftOpOf o with
        | none => (.error s!"unknown operator {o}" : D Expr)
        | some o' => do
            let v ← decodeExpr n (jsonOf (exprJ a))
            let k ← jNat (jsonOf (JVal.int (c : Int))) "a shift count"
            .ok (Expr.shift o' v k)) = .ok (.shift op a c)
      rw [jStr_str, ok_bind,
        decodeExpr_exprJ n a (by simp only [exprDepth] at h; omega) hc,
        jNat_int]
      cases op <;> rfl
  | n + 1, .cast t a, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("arg", exprJ a), ("type", tyJ t)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let u ← decodeTy n (jsonOf (tyJ t))
        let v ← decodeExpr n (jsonOf (exprJ a))
        .ok (Expr.cast u v)) = .ok (.cast t a)
      rw [decodeTy_tyJ n t (by simp only [exprDepth] at h; omega) hc.1, ok_bind,
        decodeExpr_exprJ n a (by simp only [exprDepth] at h; omega) hc.2]
      rfl
  | n + 1, .logical .and l r, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("left", exprJ l), ("right", exprJ r)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ l))
        let w ← decodeExpr n (jsonOf (exprJ r))
        .ok (Expr.logical .and v w)) = .ok (.logical .and l r)
      rw [decodeExpr_exprJ n l (by simp only [exprDepth] at h; omega) hc.1,
        ok_bind,
        decodeExpr_exprJ n r (by simp only [exprDepth] at h; omega) hc.2]
      rfl
  | n + 1, .logical .or l r, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("left", exprJ l), ("right", exprJ r)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodeExpr n (jsonOf (exprJ l))
        let w ← decodeExpr n (jsonOf (exprJ r))
        .ok (Expr.logical .or v w)) = .ok (.logical .or l r)
      rw [decodeExpr_exprJ n l (by simp only [exprDepth] at h; omega) hc.1,
        ok_bind,
        decodeExpr_exprJ n r (by simp only [exprDepth] at h; omega) hc.2]
      rfl
  | _ + 1, .enumVal t v, _, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("type", .str t), ("variant", .str v)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let a ← jName (jsonOf (JVal.str t)) "an enum name"
        let b ← jName (jsonOf (JVal.str v)) "a variant name"
        .ok (Expr.enumVal a b)) = .ok (.enumVal t v)
      rw [jName_str hc.1, ok_bind, jName_str hc.2]
      rfl
  | n + 1, .structVal t entries, h, hc => by
      rw [exprJ, decodeExpr, tagged_one,
        jsonOf_jobj_fields (l' := [("fields", jobj (exprEntries entries)),
          ("type", .str t)]) (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let a ← jName (jsonOf (JVal.str t)) "a struct name"
        match jFields (jsonOf (jobj (exprEntries entries))) with
        | none => (.error "struct value fields must be an object" : D Expr)
        | some fs => do
            let vs ← decodeExprFields n fs
            .ok (Expr.structVal a vs)) = .ok (.structVal t entries)
      simp only [jName_str hc.1, ok_bind, jFields_exprEntries hc.2.1,
        decodeExprFields_exprEntries n entries
          (by simp only [exprDepth] at h; omega) hc.2.2]
termination_by n _ _ _ => (n, 0)

theorem decodeExprFields_exprEntries :
    ∀ (n : Nat) (entries : List (String × Expr)),
      exprEntriesDepth entries ≤ n → ExprEntriesCanonical entries →
      decodeExprFields n (jsonOfFields (exprEntries entries)) = .ok entries
  | _, [], _, _ => by rw [exprEntries, jsonOfFields, decodeExprFields]
  | n, (k, e) :: rest, h, hc => by
      rw [exprEntries, jsonOfFields, decodeExprFields, if_pos hc.1,
        decodeExpr_exprJ n e
          (by simp only [exprEntriesDepth] at h; omega) hc.2.1,
        decodeExprFields_exprEntries n rest
          (by simp only [exprEntriesDepth] at h; omega) hc.2.2]
      rfl
termination_by n entries _ _ => (n, entries.length + 1)

end

/-- The budget a place costs. An index is an expression, so a place's budget
has to cover the deepest one it holds as well as its own nesting. -/
def placeDepth : Place → Nat
  | .var _ => 1
  | .field base _ => placeDepth base + 1
  | .index base i => max (placeDepth base) (exprDepth i) + 1

/-- What a place has to satisfy: the same names-are-names condition as an
expression, and whatever its indices ask for as expressions. -/
def Place.Canonical : Place → Prop
  | .var n => isIdentifier n = true
  | .field base n => base.Canonical ∧ isIdentifier n = true
  | .index base i => base.Canonical ∧ i.Canonical

instance decPlaceCanonical : (p : Place) → Decidable p.Canonical
  | .var n => inferInstanceAs (Decidable (isIdentifier n = true))
  | .field base _ =>
      @instDecidableAnd _ _ (decPlaceCanonical base) inferInstance
  | .index base i =>
      @instDecidableAnd _ _ (decPlaceCanonical base) (decExprCanonical i)

theorem decodePlace_placeJ : ∀ (n : Nat) (p : Place),
    placeDepth p ≤ n → p.Canonical →
    decodePlace n (jsonOf (placeJ p)) = .ok p
  | 0, p, h, _ => by cases p <;> simp [placeDepth] at h
  | _ + 1, .var m, _, hc => by
      rw [placeJ, decodePlace, tagged_one]
      show (do
        let s ← jName (jsonOf (JVal.str m)) "a variable"
        .ok (Place.var s)) = .ok (.var m)
      rw [jName_str hc]
      rfl
  | n + 1, .field base m, h, hc => by
      rw [placeJ, decodePlace, tagged_one,
        jsonOf_jobj_fields (l' := [("base", placeJ base), ("name", .str m)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodePlace n (jsonOf (placeJ base))
        let s ← jName (jsonOf (JVal.str m)) "a field name"
        .ok (Place.field v s)) = .ok (.field base m)
      rw [decodePlace_placeJ n base
          (by simp only [placeDepth] at h; omega) hc.1,
        ok_bind, jName_str hc.2]
      rfl
  | n + 1, .index base i, h, hc => by
      rw [placeJ, decodePlace, tagged_one,
        jsonOf_jobj_fields (l' := [("base", placeJ base), ("index", exprJ i)])
          (by simp [jobj, List.mergeSort])]
      simp only [jsonOfFields]
      show (do
        let v ← decodePlace n (jsonOf (placeJ base))
        let w ← decodeExpr n (jsonOf (exprJ i))
        .ok (Place.index v w)) = .ok (.index base i)
      rw [decodePlace_placeJ n base
          (by simp only [placeDepth] at h; omega) hc.1,
        ok_bind,
        decodeExpr_exprJ n i (by simp only [placeDepth] at h; omega) hc.2]
      rfl

/-! ### The predicate, on an expression and on a place

Same three questions as for a constant, one family up: the depth is the one
the decoder actually spends, the premise refuses what it is there to refuse,
and the theorem applies at exactly that depth. The expression sample reaches
into the type family through its `cast`, which is the part of the premise a
sample made only of expressions would not touch. -/

private def exprSample : Expr :=
  .structVal "point"
    [("x", .cast (.int .u32) (.bin .add (.var "a") (.litInt .u8 3))),
     ("y", .index (.field (.var "p") "row") (.len (.constRef "k")))]

#guard exprDepth exprSample == 4
#guard (decodeExpr 3 (jsonOf (exprJ exprSample))).toOption.isNone

example : exprSample.Canonical := by decide

example : ¬ (Expr.structVal "point"
    [("y", .var "b"), ("x", .var "a")]).Canonical := by decide

example : ¬ (Expr.cast (.struct "not a name") (.var "a")).Canonical := by
  decide

example : decodeExpr (exprDepth exprSample) (jsonOf (exprJ exprSample))
    = .ok exprSample :=
  decodeExpr_exprJ _ _ (Nat.le_refl _) (by decide)

private def placeSample : Place :=
  .index (.field (.var "grid") "cells") (.un .neg (.var "i"))

#guard placeDepth placeSample == 3
#guard (decodePlace 2 (jsonOf (placeJ placeSample))).toOption.isNone

example : placeSample.Canonical := by decide

example : ¬ (Place.var "not a name").Canonical := by decide

example : ¬ (Place.index (.var "grid") (.var "not a name")).Canonical := by
  decide

example : decodePlace (placeDepth placeSample) (jsonOf (placeJ placeSample))
    = .ok placeSample :=
  decodePlace_placeJ _ _ (Nat.le_refl _) (by decide)

end Pcrevera.Tir
