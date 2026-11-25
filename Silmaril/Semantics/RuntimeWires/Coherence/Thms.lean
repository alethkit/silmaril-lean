module

public import Silmaril.Semantics.RuntimeWires.Coherence.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Premonoidal

@[expose] public section

namespace Silmaril.RuntimeWires.Presentation.Computations

open CategoryTheory
open scoped MonoidalCategory

universe u v
open Silmaril.RuntimeWires.Proofs.RuntimeCoherence

/-- Lemma 3.11. The leftmost representatives of braid clique morphisms form a
strict premonoidal category, with the shared Silmaril premonoidal interface. -/
instance premonoidal {G : EffectfulPolygraph.{u,v}} : PremonoidalCategory (Computations G) where
  toMonoidalCategoryStruct := monoidalData
  tensorHom_def _ _ := rfl
  whiskerLeft_id := by exact Computation.left_id
  whiskerLeft_comp := by exact Computation.left_comp
  id_whiskerRight := by exact Computation.right_id
  comp_whiskerRight := by exact Computation.right_comp
  associator_central X Y Z := by exact Computation.cast_central (concat_assoc X Y Z)
  leftUnitor_central X := by exact Computation.cast_central (empty_concat X)
  rightUnitor_central X := by exact Computation.cast_central (concat_empty X)
  associator_naturality_left := by exact Computation.naturality_left
  associator_naturality_middle := by exact Computation.naturality_middle
  associator_naturality_right := by exact Computation.naturality_right
  leftUnitor_naturality := by exact Computation.naturality_leftUnitor
  rightUnitor_naturality := by exact Computation.naturality_rightUnitor
  pentagon := by exact Computation.pentagon
  triangle := by exact Computation.triangle

end Silmaril.RuntimeWires.Presentation.Computations
