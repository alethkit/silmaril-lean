module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Associator.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

/-- An ambient homeomorphism of the height slab. Its height may change by
one increasing homeomorphism, independent of horizontal position. -/
structure CapHomeomorph where
  plane : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)
  height : ℝ ≃ₜ ℝ
  increasing : StrictMono height
  height_eq : ∀ z, (plane z).2 = height z.2
  outside : ∀ z, z.2 ≤ 0 ∨ 1 ≤ z.2 → plane z = z

/-- Ordered, typed cap coordinates. The two cuts of a drawing can have
different profiles. -/
structure CapProfile (O : Type*) where
  size : ℕ
  label : Fin size → O
  x : Fin size → ℝ
  ordered : StrictMono x

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace Diagram

/-- The boundary caps are fixed pointwise on the plane. Correspondence is
checked on every full trace and generator occurrence. -/
structure CapComparison {V W V' W' : ℕ} (d : Diagram S V W .point) (e : Diagram S V' W' .point) where
  map : CapHomeomorph
  incidence : d.IncidenceEquiv e
  trace : ∀ w, map.plane '' (d.wire w).trace = (e.wire (incidence.wire w)).trace
  vertex : ∀ j, map.plane (d.vertexX j, d.vertexHeight j) =
    (e.vertexX (incidence.vertex j), e.vertexHeight (incidence.vertex j))

end Diagram

/-- A polygonal drawing with a specified ordered and typed enumeration
of every contact on each cap. -/
structure FixedDrawing (S : Signature.{u,v} O) (bottom top : CapProfile O) where
  vertices : ℕ
  wires : ℕ
  drawing : Diagram S vertices wires .point
  input : Fin bottom.size ≃ {w : Fin wires // drawing.start w = none}
  output : Fin top.size ≃ {w : Fin wires // drawing.finish w = none}
  input_label : ∀ i, drawing.label (input i).val = bottom.label i
  output_label : ∀ i, drawing.label (output i).val = top.label i
  input_x : ∀ i, drawing.x (input i).val 0 = bottom.x i
  output_x : ∀ i, drawing.x (output i).val 1 = top.x i

namespace FixedDrawing

variable {a b : CapProfile O}

/-- Endpoint equivalence under a cap-relative, increasing-height
ambient homeomorphism with typed incidence. -/
def Equivalent (p q : FixedDrawing S a b) : Prop :=
  Nonempty (p.drawing.CapComparison q.drawing)

end FixedDrawing
end Silmaril.RuntimeWires.ProgressiveGraph
