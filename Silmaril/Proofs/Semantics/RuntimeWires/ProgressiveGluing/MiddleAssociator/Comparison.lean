module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Core
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Framed
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.MiddleAssociator

open ProgressiveGraph CategoryTheory
open FixedCap (middleLeftDrawing middleRightDrawing middleAssociator_types
  middleWhiskerLeft middleWhiskerRight middleAssociatorComponent)
open CapClasses (compare_trans compare_symm compare_id)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (A C : FixedCap S) {B D : FixedCap S}

theorem left_map (p : FixedDrawing S B.profile D.profile) :
    (middleWhiskerLeft A C).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (middleLeftDrawing A C p) := by
  change (ActiveStrip.left.whisker C).map ((ActiveStrip.right.whisker A).map (FixedCap.ofDrawing p)) = _
  rw [ActiveStrip.whisker_drawings (a := B) (b := D)]
  exact ActiveStrip.whisker_drawings (a := ActiveStrip.right.adjoin B A)
    (b := ActiveStrip.right.adjoin D A) .left C (leftInner A p)

theorem right_map (p : FixedDrawing S B.profile D.profile) :
    (middleWhiskerRight A C).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (middleRightDrawing A C p) := by
  change (ActiveStrip.right.whisker A).map ((ActiveStrip.left.whisker C).map (FixedCap.ofDrawing p)) = _
  rw [ActiveStrip.whisker_drawings (a := B) (b := D)]
  exact ActiveStrip.whisker_drawings (a := ActiveStrip.left.adjoin B C)
    (b := ActiveStrip.left.adjoin D C) .right A (rightInner C p)

def compare (p : FixedDrawing S B.profile D.profile) :
    ((middleLeftDrawing A C p).thenDo (shift (middleAssociator_types A D C))).drawing.CapComparison
      ((shift (middleAssociator_types A B C)).thenDo (middleRightDrawing A C p)).drawing := by
  let l := middleLeftDrawing A C p
  let r := middleRightDrawing A C p
  let lower := shift (middleAssociator_types A B C)
  let upper := shift (middleAssociator_types A D C)
  have h : CoreTransport horizontal l r := by
    exact coreTransport A C p
  exact compare_trans (FixedDrawing.thenDo_comparison (l.compareLeftUnit _) (compare_id upper.drawing))
    (compare_trans (framedComparison l r (middleAssociator_types A B C) (middleAssociator_types A D C) h)
      (compare_symm ((lower.thenDo r).compareRightUnit _)))

theorem naturality (f : B ⟶ D) :
    (middleWhiskerLeft A C).map f ≫ (middleAssociatorComponent A D C).hom =
      (middleAssociatorComponent A B C).hom ≫ (middleWhiskerRight A C).map f := by
  refine Quotient.inductionOn f fun p => ?_
  change (middleWhiskerLeft A C).map (FixedCap.ofDrawing p) ≫ (middleAssociatorComponent A D C).hom =
    (middleAssociatorComponent A B C).hom ≫ (middleWhiskerRight A C).map (FixedCap.ofDrawing p)
  rw [left_map, right_map]
  change FixedCap.ofDrawing (middleLeftDrawing A C p) ≫
      FixedCap.ofDrawing (shift (middleAssociator_types A D C)) =
    FixedCap.ofDrawing (shift (middleAssociator_types A B C)) ≫
      FixedCap.ofDrawing (middleRightDrawing A C p)
  rw [FixedCap.comp_drawings, FixedCap.comp_drawings]
  exact CapClass.sound ⟨compare A C p⟩

end Silmaril.RuntimeWires.Proofs.MiddleAssociator
