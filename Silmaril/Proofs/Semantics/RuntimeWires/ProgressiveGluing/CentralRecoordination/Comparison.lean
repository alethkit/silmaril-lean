module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Core
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Comparison
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CentralRecoordination

open ProgressiveGraph CategoryTheory
open MiddleAssociator (comparePlacedComposites CoreTransport)
open CapClasses (compare_id compare_trans compare_symm)

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable (side : ActiveStrip) {a a' b d : FixedCap S} (h : a.types = a'.types)

include h in
theorem fixed_active_types (x : FixedCap S) :
    (side.adjoin x a).types = (side.adjoin x a').types := by
  cases side
  · exact ActiveStrip.right.whisker_types x h
  · exact ActiveStrip.left.whisker_types x h

def compareShift (x : FixedCap S) :
    (side.oppositeRecoordination x h).drawing.CapComparison
      (FixedCap.interpolationDrawing (fixed_active_types side h x)).drawing := by
  cases side
  · exact ActiveStrip.right.compareWhiskerRecoordinate x h
  · exact ActiveStrip.left.compareWhiskerRecoordinate x h

def compareSlide (p : FixedDrawing S b.profile d.profile) :
    ((side.placeDrawing (a := b) (b := d) p a).thenDo
      (side.oppositeRecoordination d h)).drawing.CapComparison
      ((side.oppositeRecoordination b h).thenDo
        (side.placeDrawing (a := b) (b := d) p a')).drawing := by
  let l := side.placeDrawing (a := b) (b := d) p a
  let r := side.placeDrawing (a := b) (b := d) p a'
  have c : CoreTransport (horizontal side h) l r := core side h p
  exact compare_trans (FixedDrawing.thenDo_comparison (compare_id l.drawing) (compareShift side h d))
    (compare_trans (comparePlacedComposites l r (fixed_active_types side h b) (fixed_active_types side h d)
      (horizontal_strict side h) c (ambient side h) (fun {_} _ => ambient_track side h _))
      (compare_symm (FixedDrawing.thenDo_comparison (compareShift side h b) (compare_id r.drawing))))

theorem slide (f : b ⟶ d) :
    (side.whisker a).map f ≫ FixedCap.ofDrawing (side.oppositeRecoordination d h) =
      FixedCap.ofDrawing (side.oppositeRecoordination b h) ≫ (side.whisker a').map f := by
  refine Quotient.inductionOn f fun p => ?_
  change (side.whisker a).map (FixedCap.ofDrawing p) ≫ FixedCap.ofDrawing (side.oppositeRecoordination d h) =
    FixedCap.ofDrawing (side.oppositeRecoordination b h) ≫ (side.whisker a').map (FixedCap.ofDrawing p)
  rw [side.whisker_drawings (a := b) (b := d), side.whisker_drawings (a := b) (b := d)]
  change FixedCap.ofDrawing (side.placeDrawing (a := b) (b := d) p a) ≫
      FixedCap.ofDrawing (side.oppositeRecoordination d h) =
    FixedCap.ofDrawing (side.oppositeRecoordination b h) ≫
      FixedCap.ofDrawing (side.placeDrawing (a := b) (b := d) p a')
  rw [FixedCap.comp_drawings, FixedCap.comp_drawings]
  exact CapClass.sound ⟨compareSlide side h p⟩

theorem central :
    @PremonoidalCategory.IsCentral (FixedCap S) inferInstance (FixedCap.geometricMonoidalData S)
      a a' (FixedCap.recoordinate h) := by
  constructor
  · intro x y f
    change (ActiveStrip.left.whisker x).map (FixedCap.ofDrawing (interpolation h)) ≫
        (ActiveStrip.right.whisker a').map f =
       (ActiveStrip.right.whisker a).map f ≫ (ActiveStrip.left.whisker y).map (FixedCap.ofDrawing (interpolation h))
    rw [ActiveStrip.whisker_drawings (a := a) (b := a'), ActiveStrip.whisker_drawings (a := a) (b := a')]
    exact (slide .right h f).symm
  · intro x y f
    change (ActiveStrip.left.whisker a).map f ≫
        (ActiveStrip.right.whisker y).map (FixedCap.ofDrawing (interpolation h)) =
      (ActiveStrip.right.whisker x).map (FixedCap.ofDrawing (interpolation h)) ≫ (ActiveStrip.left.whisker a').map f
    rw [ActiveStrip.whisker_drawings (a := a) (b := a'), ActiveStrip.whisker_drawings (a := a) (b := a')]
    exact slide .left h f

end Silmaril.RuntimeWires.Proofs.CentralRecoordination
