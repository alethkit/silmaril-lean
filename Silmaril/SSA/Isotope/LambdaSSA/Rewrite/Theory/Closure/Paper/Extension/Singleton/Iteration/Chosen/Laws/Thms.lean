module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedElgot

/-! # Chosen-coproduct Elgot laws for guarded feedback in a contextual quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "proj" => projection Seed

/-- The chosen quotient iteration of a projected step is the image of standard Paper iteration. -/
theorem iterateChosen_projectStep {X Y : P} (f : X ⟶ Y ⨿ X) :
    iterateChosen Seed (projectStep Seed f) = (proj).map (Paper.TypeCategory.iterate f) :=
  ProjectedElgot.iterateChosen_projectStep Seed f

/-- Guarded feedback unfolds at the chosen quotient coproduct. -/
theorem iterateChosen_fixpoint {X Y : Q} (f : X ⟶ Y ⨿ X) :
    iterateChosen Seed f = f ≫ coprod.desc (𝟙 Y) (iterateChosen Seed f) :=
  ProjectedElgot.iterateChosen_fixpoint Seed f

/-- Postcomposition maps the outward result of the chosen iteration. -/
theorem iterateChosen_naturality {X Y Z : Q} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterateChosen Seed f ≫ g = iterateChosen Seed (f ≫ coprod.map g (𝟙 X)) :=
  ProjectedElgot.iterateChosen_naturality Seed f g

/-- Flatten two iterations after comparing both chosen sums. -/
theorem iterateChosen_codiagonal {X Y : Q} (f : X ⟶ (Y ⨿ X) ⨿ X) :
    iterateChosen Seed (iterateChosen Seed f) =
      iterateChosen Seed (f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) :=
  ProjectedElgot.iterateChosen_codiagonal Seed f

/-- The chosen quotient iteration commutes with rotation of an alternating step. -/
theorem iterateChosen_roll {X Y Z : Q} (h : X ⟶ Z) (s : Z ⟶ Y ⨿ X) :
    iterateChosen Seed (h ≫ s) =
      h ≫ iterateChosen Seed (s ≫ coprod.map (𝟙 Y) h) :=
  ProjectedElgot.iterateChosen_roll Seed h s

/-- A commuting square of projected steps means equality of the projected standard Paper composites. -/
theorem projectSquare_iff {X Y Z : P} (f : X ⟶ Y ⨿ X) (g : Z ⟶ Y ⨿ Z) (h : X ⟶ Z) :
    projectStep Seed f ≫ coprod.map (𝟙 ((proj).obj Y)) ((proj).map h) = (proj).map h ≫ projectStep Seed g ↔
    (proj).map (f ≫ coprod.map (𝟙 Y) h) = (proj).map (h ≫ g) :=
  ProjectedElgot.projectSquare_iff Seed f g h

/-- A factorization of both steps through one intermediate transition gives uniformity in the quotient. -/
theorem uniformity_of_factorization {A B D : Q} (h : A ⟶ D)
    (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D) (s : D ⟶ B ⨿ A)
    (hf : f = h ≫ s) (hg : g = s ≫ coprod.map (𝟙 B) h) :
    iterateChosen Seed f = h ≫ iterateChosen Seed g :=
  ProjectedElgot.uniformity_of_factorization Seed h f g s hf hg

/-- An invertible state map is uniform for every commuting square in the quotient. -/
theorem uniformity_of_iso {A B D : Q} (h : A ≅ D)
    (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h.hom = h.hom ≫ g) :
    iterateChosen Seed f = h.hom ≫ iterateChosen Seed g :=
  ProjectedElgot.uniformity_of_iso Seed h f g comm

/-- A constructor state map with a square in standard Paper remains uniform after projection. -/
theorem uniformity_of_constructor_square {A B D : P} {h : A ⟶ D}
    (hh : Paper.TypeCategory.ConstructorReturn h) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g) :
    iterateChosen Seed (projectStep Seed f) = (proj).map h ≫ iterateChosen Seed (projectStep Seed g) :=
  ProjectedElgot.uniformity_of_constructor_square Seed hh f g comm

/-- Fixpoint, naturality and codiagonal for the guarded iteration on the chosen computation coproduct. -/
theorem guardedElgot :
    letI := Paper.Extension.Singleton.guardedIteration Seed
    ElgotCategory Q :=
  ProjectedElgot.guardedElgot Seed

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
