import Pcrevera.Tir.Step
import Pcrevera.Tir.Artifact
import Pcrevera.Ref.Poly

/-!
# Gate 4's target, and the encoding it is stated over

`region_kids` is the smallest function in the artifact that exercises the
whole store model rather than a corner of it: two loops, a frozen vector of
structs read through a field, two inout vectors, pushes that grow a sequence,
and indexed writes whose aliasing is what the linearity discipline exists to
control. Its layer R counterpart is `Ref.regionKids`.

A simulation lemma is an argument about two states, so before it can be
stated the two have to be related. That is what this file is: how a layer R
`Region` and an array of them look as TIR values, and the two facts about the
artifact that the relation depends on — that `Region`'s fields are in the
order assumed here, and that `region_kids` takes the parameters assumed here.
Both are read off the decoded artifact rather than believed, because the
relation is silently wrong if either changes.

The lemma itself — the two loop invariants — is the outstanding part of gate
4, and the number it produces is what says what gate 5 will cost.
-/

namespace Pcrevera.Tir

open Pcrevera.Ref (Region Rk)

/-- The width of the two mark arrays and the region vector, from the
artifact's own declarations. -/
def marksMax : Nat := 8208

/-- A region kind, as the artifact spells one: the `Rk` enum's variants in
declaration order, which is the order the ordinals were pinned in. -/
def rkName : Rk → String
  | .root => "RkRoot"
  | .group => "RkGroup"
  | .branch => "RkBranch"
  | .alt => "RkAlt"
  | .«repeat» => "RkRepeat"

def regionValue (r : Region) : Value :=
  .struct "Region"
    [("kind", .tag "Rk" (rkName r.kind)), ("parent", .int (Int.ofNat r.parent)),
     ("lo", .int (Int.ofNat r.lo)), ("hi", .int (Int.ofNat r.hi))]

/-- A frozen vector of regions, as the parameter arrives.

A relation rather than a function, and the capacity is why. Layer R's arrays
have a length and nothing else, while a TIR sequence also remembers how much
room it was given — and a push grows that room by doubling, so the capacity a
loop leaves behind is a fact about how many pushes happened rather than about
what the answer is. Relating the two by a function would have pinned a number
the specification does not fix, and the first loop of `region_kids` would
have failed to satisfy it for no reason worth having. -/
def RegionsAt (v : Value) (regions : Array Region) : Prop :=
  ∃ cap, v = .frozen (.seq marksMax (regions.toList.map regionValue) cap)

/-- How one mark is spelled as a TIR value. -/
def markVal (n : Nat) : Value := .int (Int.ofNat n)

/-- One of the two mark arrays, related the same way and for the same
reason. -/
def MarksAt (v : Value) (marks : Array Nat) : Prop :=
  ∃ cap, v = .seq marksMax (marks.toList.map markVal) cap

theorem MarksAt.empty : MarksAt (.seq marksMax [] 0) (#[] : Array Nat) :=
  ⟨0, rfl⟩

/-- Which is the shape a push leaves: one more element, and whatever room the
growth rule decided on. -/
theorem MarksAt.push {v : Value} {marks : Array Nat} {n : Nat} {cap : Nat}
    (h : v = .seq marksMax
      (marks.toList.map markVal ++ [markVal n]) cap) :
    MarksAt v (marks.push n) := by
  refine ⟨cap, ?_⟩
  rw [h]
  simp

/-! ## What the artifact has to say for the encoding to mean anything -/

private def artifactStruct (name : String) : Option StructDecl :=
  match artifact with
  | .ok p => p.struct? name
  | .error _ => none

private def artifactFunc (name : String) : Option Func :=
  match artifact with
  | .ok p => p.func? name
  | .error _ => none

-- `Region`'s fields, in the order `regionValue` writes them.
#guard artifactStruct "Region" ==
  some ⟨"Region", [⟨"kind", .enum "Rk"⟩, ⟨"parent", .int .u32⟩,
    ⟨"lo", .int .u32⟩, ⟨"hi", .int .u32⟩]⟩

-- The `Rk` variants, in the order `rkName` assumes.
#guard (match artifact with
  | .ok p => p.enum? "Rk"
  | .error _ => none) ==
  some ⟨"Rk", ["RkRoot", "RkGroup", "RkBranch", "RkAlt", "RkRepeat"]⟩

-- And the parameters `region_kids` is handed, in order and in mode.
#guard (artifactFunc "region_kids").map Func.params ==
  some [⟨"regions", .frozen (.vec (.struct "Region") marksMax), false⟩,
        ⟨"kids", .vec (.int .u32) marksMax, true⟩,
        ⟨"sibs", .vec (.int .u32) marksMax, true⟩]

#guard (artifactFunc "region_kids").map Func.ret == some none

/-- `region_kids` as a term the kernel can reduce. The simulation proof has
to step through the body, and the decoder's definitions are well-founded
rather than structural, so the kernel cannot unfold the decoded artifact.
The guard below holds this term to the artifact, so it is a transcription
with a check, not a statement from memory. -/
def regionKidsFunc : Func :=
  { name := "region_kids"
    params := [⟨"regions", .frozen (.vec (.struct "Region") marksMax), false⟩,
               ⟨"kids", .vec (.int .u32) marksMax, true⟩,
               ⟨"sibs", .vec (.int .u32) marksMax, true⟩]
    ret := none
    body := [
      .letS "total" (.int .u32) (some (.len (.var "regions"))),
      .letS "i" (.int .u32) (some (.litInt .u32 0)),
      .whileS (.cmp .lt (.var "i") (.var "total"))
        (.bin .sub (.cast (.int .counter) (.var "total"))
          (.cast (.int .counter) (.var "i")))
        [.push (.var "kids") (.litInt .u32 4294967295),
         .push (.var "sibs") (.litInt .u32 4294967295),
         .assign (.var "i") (.bin .add (.var "i") (.litInt .u32 1))],
      .assign (.var "i") (.var "total"),
      .whileS (.cmp .gt (.var "i") (.litInt .u32 1))
        (.cast (.int .counter) (.var "i"))
        [.assign (.var "i") (.bin .sub (.var "i") (.litInt .u32 1)),
         .letS "tmp1" (.int .u32)
           (some (.field (.index (.var "regions") (.var "i")) "parent")),
         .assign (.index (.var "sibs") (.var "i"))
           (.index (.var "kids") (.var "tmp1")),
         .assign (.index (.var "kids") (.var "tmp1")) (.var "i")]] }

-- The transcription is the artifact's function, byte for byte through the
-- decoder, or the build stops here.
#guard artifactFunc "region_kids" == some regionKidsFunc

end Pcrevera.Tir
