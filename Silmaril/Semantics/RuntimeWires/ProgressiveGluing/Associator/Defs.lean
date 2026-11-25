module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' : ℕ}

/-- Renaming vertices and wires of a typed drawing, including the order of
the incident ports and both kinds of labels. -/
structure IncidenceEquiv (d : Diagram S V W .point) (e : Diagram S V' W' .point) where
  vertex : Fin V ≃ Fin V'
  wire : Fin W ≃ Fin W'
  generator : ∀ v, e.generator (vertex v) = d.generator v
  label : ∀ w, e.label (wire w) = d.label w
  inputs : ∀ v, e.inputs (vertex v) = (d.inputs v).map wire
  outputs : ∀ v, e.outputs (vertex v) = (d.outputs v).map wire

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
