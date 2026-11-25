module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Trace

public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {L M R A B C : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}
variable {f : ProgressiveGraph.Diagram S R C .point}

theorem vertexX_lower (m : d.OrderedVerticalMatch e) (j : Fin L) :
    m.glue.vertexX (Fin.castAdd M j) = d.vertexX j := by
  rw [sameGlue m, m.upperJoin.glue_vertexX_lower]
  exact m.lowerJoin.glue_vertexX_lower j

theorem vertexX_upper (m : d.OrderedVerticalMatch e) (j : Fin M) :
    m.glue.vertexX (Fin.natAdd L j) = e.vertexX j := by
  rw [sameGlue m]
  exact m.upperJoin.glue_vertexX_upper j

theorem height_lower (m : d.OrderedVerticalMatch e) (j : Fin L) :
    m.glue.vertexHeight (Fin.castAdd M j) = Height.lower (d.vertexHeight j) := by
  rw [sameGlue m, m.upperJoin.glue_height_lower]
  change halfHeight 0 (m.lowerJoin.glue.vertexHeight (Fin.castAdd 0 j)) = _
  rw [m.lowerJoin.glue_height_lower]
  rfl

theorem height_upper (m : d.OrderedVerticalMatch e) (j : Fin M) :
    m.glue.vertexHeight (Fin.natAdd L j) = Height.upper (e.vertexHeight j) := by
  rw [sameGlue m]
  exact m.upperJoin.glue_height_upper j

variable (m : d.OrderedVerticalMatch e) (n : e.OrderedVerticalMatch f)

theorem assoc_vertex_point (j : Fin ((L + M) + R)) :
    Height.pointMap ((after m n).glue.vertexX j, (after m n).glue.vertexHeight j) =
      ((before m n).glue.vertexX (vertexEquiv L M R j), (before m n).glue.vertexHeight (vertexEquiv L M R j)) := by
  rcases vertex_cases j with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩
  · rw [vertex_A, vertexX_lower, vertexX_lower, vertexX_lower, height_lower, height_lower, height_lower]
    exact Height.point_placement 0 _ (Set.Ioo_subset_Icc_self (d.vertex_inside a).2)
  · rw [vertex_B, vertexX_upper, vertexX_lower, vertexX_lower, vertexX_upper,
      height_upper, height_lower, height_lower, height_upper]
    exact Height.point_placement 2 _ (Set.Ioo_subset_Icc_self (e.vertex_inside b).2)
  · rw [vertex_C, vertexX_upper, vertexX_upper, vertexX_upper, height_upper, height_upper, height_upper]
    exact Height.point_placement 4 _ (Set.Ioo_subset_Icc_self (f.vertex_inside c).2)

end Silmaril.RuntimeWires.Proofs.CollarAssociator
