module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationIteration

/-! # Iteration preservation by guarded singleton denotation -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical

open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
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

local notation "F" => denoteFunctor (Φ := Φ) J M shared

/-- The exact sum representative implements categorical iteration after
decoding its return and repeat coordinates. -/
theorem denoteFunctor_map_iterateSum {A B : τ} (f : ofType (Φ := Φ) A ⟶ ofType (Silmaril.coprod B A)) :
    (F).map (Paper.TypeCategory.iterateSum f) =
      CategoryTheory.iterate ((F).map f ≫ (denoteExactSumIso J M B A).hom) :=
  SingletonDenotationIteration.mapIterateSum J M shared f

/-- The functor preserves the guarded iterator on arbitrary step arrows,
using its comparison from the source's chosen sum to the target's. -/
theorem denoteFunctor_map_iterate {A B : τ} (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A) :
    (F).map (Paper.TypeCategory.iterate f) =
      CategoryTheory.iterate ((F).map f ≫ (denoteCoprodIso J M shared B A).hom) :=
  SingletonDenotationIteration.mapIterate J M shared f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
