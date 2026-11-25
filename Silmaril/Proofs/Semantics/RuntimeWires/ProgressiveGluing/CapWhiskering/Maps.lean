module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Sheets

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapWhiskering

open ProgressiveGraph CategoryTheory
open FixedCap (toSliced toSlicedTensorIso toSlicedUnitIso)
open scoped MonoidalCategory

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}

private theorem tensor_word (X Y : FixedCap S) :
    (toSliced S).obj X ⊗ (toSliced S).obj Y = (toSliced S).obj (X ⊗ Y) :=
  congrArg (Sliced.Presented.mk (S := S)) (FixedCap.beside_labels X Y).symm

private theorem unit_word :
    𝟙_ (Sliced.Presented S) = (toSliced S).obj (𝟙_ (FixedCap S)) := rfl

theorem whiskerRight (f : a ⟶ b) (idle : FixedCap S) :
    (toSliced S).map (f ▷ idle) =
      (toSlicedTensorIso a idle).inv ≫ (toSliced S).map f ▷ (toSliced S).obj idle ≫ (toSlicedTensorIso b idle).hom := by
  refine Quotient.inductionOn f fun p => ?_
  change (toSliced S).map ((ActiveStrip.left.whisker idle).map (FixedCap.ofDrawing p)) = _
  erw [ActiveStrip.whisker_drawings, FixedCap.toSliced_drawings,
    FixedCap.toSliced_drawings (a := a) (b := b) p]
  have sheet := read_left p idle p.drawing.layerSweep (ActiveStrip.left.placeDrawing p idle).drawing.layerSweep
  change (ActiveStrip.left.placeDrawing p idle).readSheet = _ at sheet
  erw [sheet, Sliced.Presented.ofSheet_reindex, Sliced.Presented.whiskerRight_ofSheet]
  rfl

theorem whiskerLeft (idle : FixedCap S) (f : a ⟶ b) :
    (toSliced S).map (idle ◁ f) =
      (toSlicedTensorIso idle a).inv ≫ (toSliced S).obj idle ◁ (toSliced S).map f ≫ (toSlicedTensorIso idle b).hom := by
  refine Quotient.inductionOn f fun p => ?_
  change (toSliced S).map ((ActiveStrip.right.whisker idle).map (FixedCap.ofDrawing p)) = _
  erw [ActiveStrip.whisker_drawings, FixedCap.toSliced_drawings,
    FixedCap.toSliced_drawings (a := a) (b := b) p]
  have sheet := read_right p idle p.drawing.layerSweep (ActiveStrip.right.placeDrawing p idle).drawing.layerSweep
  change (ActiveStrip.right.placeDrawing p idle).readSheet = _ at sheet
  erw [sheet, Sliced.Presented.ofSheet_reindex, Sliced.Presented.whiskerLeft_ofSheet]
  rfl

private theorem empty_reindex {A B : List O} (h : A = B) :
    (Sliced.SeamHom.ofSheet ((Sliced.Sheet.empty (S := S) A).reindex rfl h) :
      (⟨A⟩ : Sliced.Presented S) ⟶ ⟨B⟩) =
    eqToHom (congrArg (Sliced.Presented.mk (S := S)) h) := by
  cases h
  rfl

theorem recoordinate (h : a.types = b.types) :
    (toSliced S).map (FixedCap.recoordinate h) =
      eqToHom (congrArg (Sliced.Presented.mk (S := S)) h) :=
  (FixedCap.toSliced_recoordinate h).trans (empty_reindex h)

theorem associator (X Y Z : FixedCap S) :
    (α_ ((toSliced S).obj X) ((toSliced S).obj Y) ((toSliced S).obj Z)).hom ≫
        (toSliced S).obj X ◁ (toSlicedTensorIso Y Z).hom ≫ (toSlicedTensorIso X (Y ⊗ Z)).hom =
      (toSlicedTensorIso X Y).hom ▷ (toSliced S).obj Z ≫ (toSlicedTensorIso (X ⊗ Y) Z).hom ≫
        (toSliced S).map (α_ X Y Z).hom := by
  have sliced : (α_ ((toSliced S).obj X) ((toSliced S).obj Y) ((toSliced S).obj Z)).hom =
      eqToHom (congrArg (Sliced.Presented.mk (S := S)) (List.append_assoc X.types Y.types Z.types)) := rfl
  change _ = _ ≫ _ ≫ (toSliced S).map (FixedCap.objectAssociator X Y Z).hom
  rw [FixedCap.objectAssociator_hom, recoordinate, sliced]
  change eqToHom _ ≫ (toSliced S).obj X ◁ eqToHom (tensor_word Y Z) ≫
      eqToHom (tensor_word X (Y ⊗ Z)) =
    eqToHom (tensor_word X Y) ▷ (toSliced S).obj Z ≫
      eqToHom (tensor_word (X ⊗ Y) Z) ≫ eqToHom _
  simp only [MonoidalCategory.whiskerLeft_eqToHom, MonoidalCategory.eqToHom_whiskerRight]
  repeat erw [eqToHom_trans]

theorem leftUnitor (X : FixedCap S) :
    (toSlicedUnitIso S).hom ▷ (toSliced S).obj X ≫ (toSlicedTensorIso (𝟙_ (FixedCap S)) X).hom ≫
        (toSliced S).map (λ_ X).hom = (λ_ ((toSliced S).obj X)).hom := by
  have sliced : (λ_ ((toSliced S).obj X)).hom =
      eqToHom (congrArg (Sliced.Presented.mk (S := S)) (List.nil_append X.types)) := rfl
  change _ ≫ _ ≫ (toSliced S).map (FixedCap.leftUnitor X).hom = _
  rw [FixedCap.leftUnitor_hom, recoordinate, sliced]
  change eqToHom (unit_word (S := S)) ▷ (toSliced S).obj X ≫
    eqToHom (tensor_word (𝟙_ (FixedCap S)) X) ≫ eqToHom _ = eqToHom _
  simp only [MonoidalCategory.eqToHom_whiskerRight]
  repeat erw [eqToHom_trans]

theorem rightUnitor (X : FixedCap S) :
    (toSliced S).obj X ◁ (toSlicedUnitIso S).hom ≫ (toSlicedTensorIso X (𝟙_ (FixedCap S))).hom ≫
        (toSliced S).map (ρ_ X).hom = (ρ_ ((toSliced S).obj X)).hom := by
  have sliced : (ρ_ ((toSliced S).obj X)).hom =
      eqToHom (congrArg (Sliced.Presented.mk (S := S)) (List.append_nil X.types)) := rfl
  change _ ≫ _ ≫ (toSliced S).map (FixedCap.rightUnitor X).hom = _
  rw [FixedCap.rightUnitor_hom, recoordinate, sliced]
  change (toSliced S).obj X ◁ eqToHom (unit_word (S := S)) ≫
    eqToHom (tensor_word X (𝟙_ (FixedCap S))) ≫ eqToHom _ = eqToHom _
  simp only [MonoidalCategory.whiskerLeft_eqToHom]
  repeat erw [eqToHom_trans]

end Silmaril.RuntimeWires.Proofs.CapWhiskering
