module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v

/-- The open support of a vertical strip and a closed core inside it. -/
structure SwapStrip where
  left : ℝ
  coreLeft : ℝ
  coreRight : ℝ
  right : ℝ
  inside : 0 ≤ left ∧ right ≤ 1
  left_gap : left < coreLeft
  core_order : coreLeft ≤ coreRight
  right_gap : coreRight < right

namespace SwapStrip

def core (s : SwapStrip) : Set ℝ := Set.Icc s.coreLeft s.coreRight

def support (s : SwapStrip) : Set ℝ := Set.Ioo s.left s.right

end SwapStrip

/-- The two strips have disjoint open supports. -/
structure SwapStrips where
  left : SwapStrip
  right : SwapStrip
  ordered : left.right ≤ right.left

inductive StripRegion
  | left | right | exterior
  deriving DecidableEq

namespace SwapStrips

def region (s : SwapStrips) : StripRegion → Set ℝ
  | .left => s.left.core
  | .right => s.right.core
  | .exterior => (s.left.support ∪ s.right.support)ᶜ

end SwapStrips

namespace Diagram

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable (d : Diagram S V W .point)

/-- A cap-fixed ambient isotopy through valid progressive polygonal frames
with the original vertex and wire IDs. Vertices may change height. -/
structure ProgressiveIsotopy where
  frame : SlabIsotopy.Time → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)
  zero : ∀ z, frame ⟨0, le_rfl, zero_le_one⟩ z = z
  continuous_frame : Continuous (fun z : SlabIsotopy.Time × (ℝ × ℝ) => frame z.1 z.2)
  continuous_inverse : Continuous (fun z : SlabIsotopy.Time × (ℝ × ℝ) => (frame z.1).symm z.2)
  caps : ∀ t z, z.2 ≤ 0 ∨ 1 ≤ z.2 → frame t z = z
  drawing : SlabIsotopy.Time → Diagram S V W .point
  generator : ∀ t, (drawing t).generator = d.generator
  label : ∀ t, (drawing t).label = d.label
  start : ∀ t, (drawing t).start = d.start
  finish : ∀ t, (drawing t).finish = d.finish
  inputs : ∀ t j, (drawing t).inputs j = d.inputs j
  outputs : ∀ t j, (drawing t).outputs j = d.outputs j
  trace : ∀ t w, frame t '' (d.wire w).trace = ((drawing t).wire w).trace
  vertex : ∀ t j, frame t (d.vertexX j, d.vertexHeight j) =
    ((drawing t).vertexX j, (drawing t).vertexHeight j)

/-- One vertex in each core. Every full wire trace lies in one core or
outside both supports. The supports' transition regions are free of graph
points. Assignment is geometric and includes wire endpoints. -/
structure IsolatedStripSwap where
  strips : SwapStrips
  left : Fin V
  right : Fin V
  ordered : d.vertexHeight left < d.vertexHeight right
  vertexRegion : Fin V → StripRegion
  left_region : vertexRegion left = .left
  right_region : vertexRegion right = .right
  other_region : ∀ j, j ≠ left → j ≠ right → vertexRegion j = .exterior
  vertex_mem : ∀ j, d.vertexX j ∈ strips.region (vertexRegion j)
  wireRegion : Fin W → StripRegion
  wire_mem : ∀ w y, d.covers w y → d.x w y ∈ strips.region (wireRegion w)

end Diagram
end Silmaril.RuntimeWires.ProgressiveGraph
