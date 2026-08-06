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

/-- A frozen vector of regions, as the parameter arrives. -/
def regionsValue (regions : Array Region) : Value :=
  .frozen (.seq marksMax (regions.toList.map regionValue) regions.size)

/-- One of the two mark arrays. -/
def marksValue (marks : Array Nat) : Value :=
  .seq marksMax (marks.toList.map fun (n : Nat) => Value.int (Int.ofNat n)) marks.size

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

end Pcrevera.Tir
