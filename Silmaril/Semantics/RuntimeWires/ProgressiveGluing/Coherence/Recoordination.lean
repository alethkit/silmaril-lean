module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}
variable (side : ActiveStrip) (idle : FixedCap S)

theorem whisker_types (h : a.types = b.types) :
    (side.adjoin a idle).types = (side.adjoin b idle).types := by
  change List.ofFn a.profile.label = List.ofFn b.profile.label at h
  change List.ofFn (side.adjoin a idle).profile.label = List.ofFn (side.adjoin b idle).profile.label
  rw [side.adjoin_labels, side.adjoin_labels, h]

/-- The placed interpolation and the canonical interpolation of the
placed caps are vertex-free drawings with the same two boundaries.
The comparison carries the full traces at every height. -/
def compareWhiskerRecoordinate (h : a.types = b.types) :
    (side.placeDrawing (a := a) (b := b) (FixedCap.interpolationDrawing h) idle).drawing.CapComparison
      (FixedCap.interpolationDrawing (side.whisker_types idle h)).drawing :=
  FixedDrawing.compareVertexFree _ _ (by rfl) rfl

theorem whisker_recoordinate (h : a.types = b.types) :
    (side.whisker idle).map (FixedCap.recoordinate h) =
      FixedCap.recoordinate (side.whisker_types idle h) := by
  simp only [FixedCap.recoordinate, side.whisker_drawings]
  exact CapClass.sound ⟨side.compareWhiskerRecoordinate idle h⟩

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
