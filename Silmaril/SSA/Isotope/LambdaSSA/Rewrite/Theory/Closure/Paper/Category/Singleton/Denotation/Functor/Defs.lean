module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationFunctor

/-! # The denotation functor of guarded Paper singleton regions -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical (RegionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

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

/-- The object image interprets its singleton type. The arrow image evaluates
any guarded representative of the given Paper morphism. -/
noncomputable def denoteFunctor : TypeCategory (τ := τ) Φ ⥤ C where
  obj A := J.obj (M.obj (show τ from A))
  map f := denoteArrow J M f
  map_id A := by exact SingletonDenotation.denoteArrow_id (Φ := Φ) J M shared A
  map_comp f g := by exact SingletonDenotation.denoteArrow_comp J M shared f g

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
