module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Quotient
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Placed
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching

public noncomputable section

/-!
# Horizontal placement respects fixed-contact equivalence

A comparison in the existing quotient can use any common increasing
height reparametrization. Horizontal orientation is forced by injectivity,
continuity and the fixed bottom cap. A global horizontal chart agrees
with affine placement on the compact ranges of both drawings. After
conjugation, the two remaining parts of each active fibre are affinely
continued to the strip walls. The resulting map and inverse match the
height-only map at both walls and on the other strip. This supplies
congruence for the geometric juxtaposition of Lemma 3.4 and Figure 7 in
Román and Sobociński, arXiv:2305.06075v5.

The class operation below acts with a fixed idle cap. Its functor laws
and the coherence of the coordinate choices are separate.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}
variable {p q : FixedDrawing S a.profile b.profile}
variable (side : ActiveStrip) (idle : FixedCap S) (h : p.drawing.CapComparison q.drawing)

theorem comparison_height : (side.comparePlacement idle h).map.height = h.map.height := by rfl

theorem comparison_active_wire (w : Fin p.wires) :
    (side.comparePlacement idle h).incidence.wire (side.activeWire p idle w) =
      side.activeWire q idle (h.incidence.wire w) :=
  Proofs.HorizontalComparison.wire_active h.incidence idle.profile.size w

theorem comparison_idle_wire (i : Fin idle.profile.size) :
    (side.comparePlacement idle h).incidence.wire (side.idleWire p idle i) = side.idleWire q idle i :=
  Proofs.HorizontalComparison.wire_idle h.incidence idle.profile.size i

theorem comparison_active_point (w : Fin p.wires) {y : ℝ} (cover : p.drawing.covers w y) :
    (side.comparePlacement idle h).map.plane (side.place (p.drawing.x w y), y) =
      (side.place (h.map.plane (p.drawing.x w y, y)).1, (h.map.plane (p.drawing.x w y, y)).2) := by
  let span := Classical.choose (Proofs.HorizontalComparison.common_range p.drawing q.drawing)
  let bounds := Classical.choose_spec (Proofs.HorizontalComparison.common_range p.drawing q.drawing)
  exact Proofs.HorizontalComparison.placed_active_point side h
    (Proofs.HorizontalComparison.compression h.map side span) bounds.1 bounds.2 w cover

theorem comparison_exterior (z : ℝ × ℝ)
    (outside : z.1 ≤ side.place 0 ∨ side.place 1 ≤ z.1) :
    (side.comparePlacement idle h).map.plane z = (z.1, h.map.height z.2) := by
  let span := Classical.choose (Proofs.HorizontalComparison.common_range p.drawing q.drawing)
  exact (Proofs.HorizontalComparison.compression h.map side span).window.localized_exterior z outside

theorem comparison_idle_point (i : Fin idle.profile.size) (y : ℝ) :
    (side.comparePlacement idle h).map.plane (side.opposite.place (idle.profile.x i), y) =
      (side.opposite.place (idle.profile.x i), h.map.height y) := by
  let span := Classical.choose (Proofs.HorizontalComparison.common_range p.drawing q.drawing)
  exact (Proofs.HorizontalComparison.compression h.map side span).ambient_idle (idle.inside i) y

theorem comparison_input_slot (i : Fin (side.adjoin a idle).profile.size) :
    (side.comparePlacement idle h).incidence.wire ((side.placeDrawing p idle).input i).val =
      ((side.placeDrawing q idle).input i).val :=
  congrArg Subtype.val (Proofs.CapClasses.input_slot (side.comparePlacement idle h) i)

theorem comparison_output_slot (i : Fin (side.adjoin b idle).profile.size) :
    (side.comparePlacement idle h).incidence.wire ((side.placeDrawing p idle).output i).val =
      ((side.placeDrawing q idle).output i).val :=
  congrArg Subtype.val (Proofs.CapClasses.output_slot (side.comparePlacement idle h) i)

theorem placeDrawing_congr (h : p.Equivalent q) :
    (side.placeDrawing p idle).Equivalent (side.placeDrawing q idle) :=
  h.map (side.comparePlacement idle)

/-- Horizontal placement with a fixed idle cap, on the existing classes. -/
def placeClass (f : CapClass S a.profile b.profile) :
    CapClass S (side.adjoin a idle).profile (side.adjoin b idle).profile :=
  Quotient.map (fun p => side.placeDrawing (a := a) (b := b) p idle)
    (fun _ _ h => side.placeDrawing_congr idle h) f

theorem placeClass_drawings (p : FixedDrawing S a.profile b.profile) :
    side.placeClass (a := a) (b := b) idle (CapClass.ofDrawing p) =
      CapClass.ofDrawing (side.placeDrawing p idle) := by rfl

end Silmaril.RuntimeWires.ProgressiveGraph.ActiveStrip
