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
variable {O : Type u} {S : Signature.{u,v} O}

section Composites

variable {a b a' b' : FixedCap S}
variable (p : FixedDrawing S a.profile b.profile) (q : FixedDrawing S a'.profile b'.profile)
variable (ha : a.types = a'.types) (hb : b.types = b'.types)

/-- Align the active slabs using the two geometric unit comparisons,
then apply the common framed transport to the actual composites. -/
def compareComposites (h : CoreTransport horizontal p q) :
    (p.thenDo (shift hb)).drawing.CapComparison ((shift ha).thenDo q).drawing :=
  compare_trans (FixedDrawing.thenDo_comparison (p.compareLeftUnit a.inside) (compare_id (shift hb).drawing))
    (compare_trans (framedComparison p q ha hb h)
      (compare_symm (((shift ha).thenDo q).compareRightUnit b'.inside)))

end Composites

variable (A C : FixedCap S) {B D : FixedCap S}

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
  have h : CoreTransport horizontal l r := by
    exact coreTransport A C p
  exact compareComposites l r (middleAssociator_types A B C) (middleAssociator_types A D C) h

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
