module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Defs

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime

open CategoryTheory Presentation ProgressiveGraph
open scoped MonoidalCategory

universe u v
variable {G : EffectfulPolygraph.{u,v}}

private abbrev toTerms (G : EffectfulPolygraph.{u,v}) :=
  Sliced.Presented.toTerms (signature G)

private abbrev fromTerms (G : EffectfulPolygraph.{u,v}) :=
  FixedRuntimeCap.termToRuntime G

private abbrev fromSlices (G : EffectfulPolygraph.{u,v}) := toTerms G ⋙ fromTerms G

private theorem fromSlices_tensor {A B C D : Sliced.Presented (signature G)}
    (f : A ⟶ B) (g : C ⟶ D) :
    (fromSlices G).map (f ⊗ₘ g) = (fromSlices G).map f ⊗ₘ (fromSlices G).map g := by
  change (fromTerms G).map (Sliced.SeamHom.toTermHom (Sliced.SeamHom.tensor f g)) = _
  have h := congrArg ((fromTerms G).map (X := (toTerms G).obj (A ⊗ C))
    (Y := (toTerms G).obj (B ⊗ D))) (Sliced.SeamHom.toTermHom_tensor f g)
  exact h.trans (Diagram.Presented.imposeEquations_tensor (fun h => h.elim)
    ((toTerms G).map f) ((toTerms G).map g))

private theorem fromSlices_right {A B : Sliced.Presented (signature G)}
    (f : A ⟶ B) (P : Sliced.Presented (signature G)) :
    (fromSlices G).map (f ▷ P) = (fromSlices G).map f ▷ (fromSlices G).obj P := by
  rw [← MonoidalCategory.tensorHom_id, fromSlices_tensor, (fromSlices G).map_id,
    MonoidalCategory.tensorHom_id]

private theorem fromSlices_left {A B : Sliced.Presented (signature G)}
    (P : Sliced.Presented (signature G)) (f : A ⟶ B) :
    (fromSlices G).map (P ◁ f) = (fromSlices G).obj P ◁ (fromSlices G).map f := by
  rw [← MonoidalCategory.id_tensorHom, fromSlices_tensor, (fromSlices G).map_id,
    MonoidalCategory.id_tensorHom]

theorem map_right {A B : FixedCap (signature G)} (f : A ⟶ B) (P : FixedCap (signature G)) :
    (FixedCap.runtimeSweep G).map (f ▷ P) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) (FixedCap.beside_labels A P)) ≫
        (FixedCap.runtimeSweep G).map f ▷ (FixedCap.runtimeSweep G).obj P ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) (FixedCap.beside_labels B P).symm) := by
  change (fromSlices G).map ((FixedCap.toSliced _).map (f ▷ P)) = _
  erw [FixedCap.toSliced_whiskerRight, Functor.map_comp, Functor.map_comp, fromSlices_right]
  change (fromSlices G).map (eqToHom (congrArg (Sliced.Presented.mk (S := signature G))
    (FixedCap.beside_labels A P))) ≫ _ ≫ (fromSlices G).map
      (eqToHom (congrArg (Sliced.Presented.mk (S := signature G)) (FixedCap.beside_labels B P).symm)) = _
  erw [eqToHom_map, eqToHom_map]
  rfl

theorem map_left {A B : FixedCap (signature G)} (P : FixedCap (signature G)) (f : A ⟶ B) :
    (FixedCap.runtimeSweep G).map (P ◁ f) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) (FixedCap.beside_labels P A)) ≫
        (FixedCap.runtimeSweep G).obj P ◁ (FixedCap.runtimeSweep G).map f ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) (FixedCap.beside_labels P B).symm) := by
  change (fromSlices G).map ((FixedCap.toSliced _).map (P ◁ f)) = _
  erw [FixedCap.toSliced_whiskerLeft, Functor.map_comp, Functor.map_comp, fromSlices_left]
  change (fromSlices G).map (eqToHom (congrArg (Sliced.Presented.mk (S := signature G))
    (FixedCap.beside_labels P A))) ≫ _ ≫ (fromSlices G).map
      (eqToHom (congrArg (Sliced.Presented.mk (S := signature G)) (FixedCap.beside_labels P B).symm)) = _
  erw [eqToHom_map, eqToHom_map]
  rfl

end Silmaril.RuntimeWires.Proofs.PositionedRuntime
