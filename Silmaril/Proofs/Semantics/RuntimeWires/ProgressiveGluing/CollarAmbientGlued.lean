module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarAmbient

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CollarAmbient

open ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)
variable (p q : PolygonalCollar m.collarSpec)

theorem ambient_glued_wire (t : PolygonalCollar.Time) (w : Fin m.gluedWireCount)
    {y : ℝ} (cover : (m.glueWith p).covers w y) :
    ambient p q t ((m.glueWith p).x w y, y) = ((m.glueWith (p.blend q t)).x w y, y) := by
  by_cases inside : y ≤ 1 / 4 ∨ 1 / 2 ≤ y
  · rw [ambient_outside _ _ _ _ inside, m.glueWith_fixed_outside p (p.blend q t) w cover inside]
  · have hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) :=
      ⟨le_of_lt (lt_of_not_ge (fun h => inside (.inl h))), le_of_lt (lt_of_not_ge (fun h => inside (.inr h)))⟩
    obtain ⟨c, id⟩ := m.glueWith_collar_id_exists p w hy cover
    rw [id, m.glueWith_x_collar p c hy, m.glueWith_x_collar (p.blend q t) c hy]
    exact ambient_wire p q t c hy

theorem ambient_glued_trace (t : PolygonalCollar.Time) (w : Fin m.gluedWireCount) :
    ambient p q t '' ((m.glueWith p).wire w).trace = ((m.glueWith (p.blend q t)).wire w).trace := by
  obtain ⟨_, hy, _, _, hs, hf, _⟩ := m.glueWith_fixed_data p (p.blend q t)
  have interval : Set.Icc ((m.glueWith p).lower w) ((m.glueWith p).upper w) =
      Set.Icc ((m.glueWith (p.blend q t)).lower w) ((m.glueWith (p.blend q t)).upper w) := by
    simp only [ProgressiveGraph.Diagram.lower, ProgressiveGraph.Diagram.upper, hy, hs, hf]
  change ambient p q t '' (((m.glueWith p).wire w).point ''
      Set.Icc ((m.glueWith p).lower w) ((m.glueWith p).upper w)) =
    ((m.glueWith (p.blend q t)).wire w).point ''
      Set.Icc ((m.glueWith (p.blend q t)).lower w) ((m.glueWith (p.blend q t)).upper w)
  rw [Set.image_image, ← interval]
  exact Set.image_congr (fun y hy => ambient_glued_wire m p q t w (y := y) hy)

theorem ambient_glued_vertex (t : PolygonalCollar.Time) (j : Fin (L + R)) :
    ambient p q t ((m.glueWith p).vertexX j, (m.glueWith p).vertexHeight j) =
      ((m.glueWith (p.blend q t)).vertexX j, (m.glueWith (p.blend q t)).vertexHeight j) := by
  rw [ambient_outside _ _ _ _ (m.glueWith_vertex_outside p j)]
  obtain ⟨hx, hy, _⟩ := m.glueWith_fixed_data p (p.blend q t)
  rw [hx, hy]

end Silmaril.RuntimeWires.Proofs.CollarAmbient
