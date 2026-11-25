module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Core
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Comparison
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.OuterAssociator

open ProgressiveGraph CategoryTheory
open MiddleAssociator (compareComposites CoreTransport horizontal)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (side : ActiveStrip) (near far : FixedCap S)
variable {a b : FixedCap S}

theorem nested_map (p : FixedDrawing S a.profile b.profile) :
    (side.nestedWhisker near far).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (side.nestedDrawing near far p) := by
  change (side.whisker far).map ((side.whisker near).map (FixedCap.ofDrawing p)) = _
  rw [ActiveStrip.whisker_drawings (a := a) (b := b)]
  exact ActiveStrip.whisker_drawings (a := side.adjoin a near) (b := side.adjoin b near)
    side far (side.placeDrawing (a := a) (b := b) p near)

theorem grouped_map (p : FixedDrawing S a.profile b.profile) :
    (side.groupedWhisker near far).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (side.groupedDrawing near far p) :=
  side.whisker_drawings (a := a) (b := b) (side.adjoin near far) p

theorem source_map (p : FixedDrawing S a.profile b.profile) :
    (side.outerAssociatorSource near far).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (side.outerSourceDrawing near far p) := by
  cases side
  · exact nested_map .left near far p
  · exact grouped_map .right near far p

theorem target_map (p : FixedDrawing S a.profile b.profile) :
    (side.outerAssociatorTarget near far).map (FixedCap.ofDrawing p) =
      FixedCap.ofDrawing (side.outerTargetDrawing near far p) := by
  cases side
  · exact grouped_map .left near far p
  · exact nested_map .right near far p

def outerTransport (p : FixedDrawing S a.profile b.profile) :
    CoreTransport horizontal (side.outerSourceDrawing near far p) (side.outerTargetDrawing near far p) := by
  cases side
  · exact leftTransport near far p
  · exact rightTransport near far p

def compare (p : FixedDrawing S a.profile b.profile) :
    ((side.outerSourceDrawing near far p).thenDo
      (FixedCap.interpolationDrawing (side.outerAssociator_types near far b))).drawing.CapComparison
      ((FixedCap.interpolationDrawing (side.outerAssociator_types near far a)).thenDo
        (side.outerTargetDrawing near far p)).drawing :=
  compareComposites (side.outerSourceDrawing near far p) (side.outerTargetDrawing near far p)
    (side.outerAssociator_types near far a) (side.outerAssociator_types near far b)
    (outerTransport side near far p)

theorem naturality (f : a ⟶ b) :
    (side.outerAssociatorSource near far).map f ≫ (side.outerAssociatorComponent near far b).hom =
      (side.outerAssociatorComponent near far a).hom ≫ (side.outerAssociatorTarget near far).map f := by
  refine Quotient.inductionOn f fun p => ?_
  change (side.outerAssociatorSource near far).map (FixedCap.ofDrawing p) ≫
      (side.outerAssociatorComponent near far b).hom =
    (side.outerAssociatorComponent near far a).hom ≫
      (side.outerAssociatorTarget near far).map (FixedCap.ofDrawing p)
  rw [source_map, target_map]
  change FixedCap.ofDrawing (side.outerSourceDrawing near far p) ≫
      FixedCap.ofDrawing (FixedCap.interpolationDrawing (side.outerAssociator_types near far b)) =
    FixedCap.ofDrawing (FixedCap.interpolationDrawing (side.outerAssociator_types near far a)) ≫
      FixedCap.ofDrawing (side.outerTargetDrawing near far p)
  rw [FixedCap.comp_drawings, FixedCap.comp_drawings]
  exact CapClass.sound ⟨compare side near far p⟩

end Silmaril.RuntimeWires.Proofs.OuterAssociator
