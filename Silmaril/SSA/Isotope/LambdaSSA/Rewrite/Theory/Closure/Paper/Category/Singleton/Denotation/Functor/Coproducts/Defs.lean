module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Finite.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Chosen sum comparisons for guarded singleton denotation -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical (RegionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

/-- First decode the exact sum, then compare the value and computation coproducts. -/
noncomputable def denoteExactSumIso (A B : τ) :
    J.obj (M.obj (Silmaril.coprod A B)) ≅ J.obj (M.obj A) ⨿ J.obj (M.obj B) :=
  J.mapIso (M.coprodIso A B) ≪≫ (asIso (coprodComparison J (M.obj A) (M.obj B))).symm

/-- The comparison of the source's chosen coproduct with the chosen target coproduct. -/
noncomputable def denoteCoprodIso (A B : τ) :
    (denoteFunctor (Φ := Φ) J M shared).obj (ofType A ⨿ ofType B) ≅
      (denoteFunctor (Φ := Φ) J M shared).obj (ofType A) ⨿
        (denoteFunctor (Φ := Φ) J M shared).obj (ofType B) :=
  ((denoteFunctor (Φ := Φ) J M shared).mapIso (sumIso A B)).symm ≪≫ denoteExactSumIso J M A B

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
