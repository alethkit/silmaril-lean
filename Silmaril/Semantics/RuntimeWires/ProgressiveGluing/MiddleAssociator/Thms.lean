module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Comparison

public noncomputable section

/-!
# Horizontal associator in the middle active slot

Keep the two outside profiles idle. Both ways of placing the middle
drawing have the same ordered cap types. The coordinate change between
their three blocks sends the cuts 0, 1/4, 1/2, 1 to 0, 1/2, 3/4, 1.
It matches the middle drawing and each idle strand on the common active
slab. The framed comparison follows this coordinate change through the
outer interpolating drawings and fixes the outer caps. The geometric
unit comparisons give a comparison of the actual collared composites.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (A C : FixedCap S) {B D : FixedCap S}

theorem middleWhiskerLeft_drawings (p : FixedDrawing S B.profile D.profile) :
    (middleWhiskerLeft A C).map (ofDrawing p) = ofDrawing (middleLeftDrawing A C p) :=
  Proofs.MiddleAssociator.left_map A C p

theorem middleWhiskerRight_drawings (p : FixedDrawing S B.profile D.profile) :
    (middleWhiskerRight A C).map (ofDrawing p) = ofDrawing (middleRightDrawing A C p) :=
  Proofs.MiddleAssociator.right_map A C p

/-- A comparison of the full traces and ordered incidence of both actual
collared composites in the middle-slot associator square. -/
def compareMiddleAssociator (p : FixedDrawing S B.profile D.profile) :
    ((middleLeftDrawing A C p).thenDo (interpolationDrawing (middleAssociator_types A D C))).drawing.CapComparison
      ((interpolationDrawing (middleAssociator_types A B C)).thenDo (middleRightDrawing A C p)).drawing :=
  Proofs.MiddleAssociator.compare A C p

theorem middleAssociator_naturality (f : B ⟶ D) :
    (middleWhiskerLeft A C).map f ≫ (middleAssociatorComponent A D C).hom =
      (middleAssociatorComponent A B C).hom ≫ (middleWhiskerRight A C).map f :=
  Proofs.MiddleAssociator.naturality A C f

/-- Horizontal reassociation is natural in the middle drawing with the
left and right profiles held idle. -/
def middleAssociator : middleWhiskerLeft A C ≅ middleWhiskerRight A C :=
  NatIso.ofComponents (fun B => middleAssociatorComponent A B C)
    (fun f => middleAssociator_naturality A C f)

theorem middleAssociator_hom_app (B : FixedCap S) :
    (middleAssociator A C).hom.app B = (middleAssociatorComponent A B C).hom := by rfl

theorem middleAssociator_inv_app (B : FixedCap S) :
    (middleAssociator A C).inv.app B = (middleAssociatorComponent A B C).inv := by rfl

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
