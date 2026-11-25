module

public import Mathlib.CategoryTheory.Category.Basic
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Thms

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory

universe u v
variable {O : Type u}

/-- A fixed ordered typed cap in the open horizontal interval of the
drawing, for the specified signature. -/
structure FixedCap (_S : Signature.{u,v} O) where
  profile : CapProfile O
  inside : profile.Inside

namespace FixedCap

variable (S : Signature.{u,v} O)

def empty : FixedCap S := ⟨CapProfile.empty, CapProfile.empty_inside⟩

/-- Vertical composition of fixed-contact geometric classes. -/
instance : Category.{max u v} (FixedCap S) where
  Hom a b := CapClass S a.profile b.profile
  id a := CapClass.identity S a.profile a.inside
  comp f g := CapClass.thenDo f g
  id_comp f := CapClass.identity_thenDo f _
  comp_id f := CapClass.thenDo_identity f _
  assoc f g h := CapClass.thenDo_assoc f g h

variable {S} {a b : FixedCap S}

/-- Regard an actual polygonal drawing as a morphism of fixed caps. -/
def ofDrawing (d : FixedDrawing S a.profile b.profile) : a ⟶ b :=
  CapClass.ofDrawing d

end FixedCap
end Silmaril.RuntimeWires.ProgressiveGraph
