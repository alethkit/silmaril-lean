module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs

/-! # Representative equations for a descended singleton denotation -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  (sound : SeedDenotes (Seed := Seed) J M)

/-- The descended interpretation factors the guarded denotation functor. -/
theorem projection_comp_denoteFunctor :
    projection Seed ⋙ denoteFunctor J M shared sound = Paper.TypeCategory.denoteFunctor J M shared :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- On a projected arrow, the descended map is the original guarded denotation. -/
theorem denoteFunctor_map_projection {A B : τ}
    (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B) :
    (denoteFunctor J M shared sound).map ((projection Seed).map f) = Paper.TypeCategory.denoteArrow J M f :=
  rfl

/-- Any guarded representative computes the descended arrow's denotation. -/
theorem denoteFunctor_map_ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    (denoteFunctor J M shared sound).map (ofRegion Seed hr) = denoteSingletonRegion J M hr.hasType :=
  Paper.TypeCategory.denoteArrow_ofRegion J M shared hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
