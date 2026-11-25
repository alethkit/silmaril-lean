module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Sheets
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Maps

public noncomputable section

/-!
# Horizontal compatibility of the fixed-contact readout

Affine placement fixes event heights and strictly preserves the horizontal
order of active slots. Every idle wire crosses each event level in the
opposite half strip. Its ordered block therefore pads each typed row,
including rows containing simultaneous generators or scalars. The sheet
comparison allows independent valid cuts in the original and placed drawings.

The functor preserves both whiskerings and the structural morphisms with
the stated word transports. The comparison here is with the sliced seam
category for the same signature.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory
open scoped MonoidalCategory

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}

namespace ActiveStrip

theorem placeDrawing_levels (side : ActiveStrip) (p : FixedDrawing S a.profile b.profile)
    (idle : FixedCap S) : (side.placeDrawing p idle).drawing.levels = p.drawing.levels := by
  exact Proofs.CapWhiskering.levels side p idle

/-- Placing the active drawing on the left appends the idle word to every row. -/
theorem readSheetAt_left (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S)
    (s : p.drawing.LayerSweep) (t : (ActiveStrip.left.placeDrawing p idle).drawing.LayerSweep) :
    (ActiveStrip.left.placeDrawing p idle).readSheetAt t =
      ((p.readSheetAt s).padRight idle.types).reindex
        (ActiveStrip.left.adjoin_labels a idle).symm (ActiveStrip.left.adjoin_labels b idle).symm := by
  exact Proofs.CapWhiskering.read_left p idle s t

/-- Placing the active drawing on the right prepends the idle word to every row. -/
theorem readSheetAt_right (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S)
    (s : p.drawing.LayerSweep) (t : (ActiveStrip.right.placeDrawing p idle).drawing.LayerSweep) :
    (ActiveStrip.right.placeDrawing p idle).readSheetAt t =
      ((p.readSheetAt s).padLeft idle.types).reindex
        (ActiveStrip.right.adjoin_labels a idle).symm (ActiveStrip.right.adjoin_labels b idle).symm := by
  exact Proofs.CapWhiskering.read_right p idle s t

end ActiveStrip

namespace FixedCap

theorem toSliced_whiskerRight (f : a ⟶ b) (idle : FixedCap S) :
    (toSliced S).map (f ▷ idle) =
      (toSlicedTensorIso a idle).inv ≫
        (toSliced S).map f ▷ (toSliced S).obj idle ≫ (toSlicedTensorIso b idle).hom := by
  exact Proofs.CapWhiskering.whiskerRight f idle

theorem toSliced_whiskerLeft (idle : FixedCap S) (f : a ⟶ b) :
    (toSliced S).map (idle ◁ f) =
      (toSlicedTensorIso idle a).inv ≫
        (toSliced S).obj idle ◁ (toSliced S).map f ≫ (toSlicedTensorIso idle b).hom := by
  exact Proofs.CapWhiskering.whiskerLeft idle f

theorem toSliced_recoordinate_eqToHom (h : a.types = b.types) :
    (toSliced S).map (recoordinate h) =
      eqToHom (congrArg (Sliced.Presented.mk (S := S)) h) := by
  exact Proofs.CapWhiskering.recoordinate h

theorem toSliced_associator (X Y Z : FixedCap S) :
    (α_ ((toSliced S).obj X) ((toSliced S).obj Y) ((toSliced S).obj Z)).hom ≫
        (toSliced S).obj X ◁ (toSlicedTensorIso Y Z).hom ≫ (toSlicedTensorIso X (Y ⊗ Z)).hom =
      (toSlicedTensorIso X Y).hom ▷ (toSliced S).obj Z ≫ (toSlicedTensorIso (X ⊗ Y) Z).hom ≫
        (toSliced S).map (α_ X Y Z).hom := by
  exact Proofs.CapWhiskering.associator X Y Z

theorem toSliced_leftUnitor (X : FixedCap S) :
    (toSlicedUnitIso S).hom ▷ (toSliced S).obj X ≫ (toSlicedTensorIso (𝟙_ (FixedCap S)) X).hom ≫
        (toSliced S).map (λ_ X).hom = (λ_ ((toSliced S).obj X)).hom := by
  exact Proofs.CapWhiskering.leftUnitor X

theorem toSliced_rightUnitor (X : FixedCap S) :
    (toSliced S).obj X ◁ (toSlicedUnitIso S).hom ≫ (toSlicedTensorIso X (𝟙_ (FixedCap S))).hom ≫
        (toSliced S).map (ρ_ X).hom = (ρ_ ((toSliced S).obj X)).hom := by
  exact Proofs.CapWhiskering.rightUnitor X

end FixedCap
end Silmaril.RuntimeWires.ProgressiveGraph
