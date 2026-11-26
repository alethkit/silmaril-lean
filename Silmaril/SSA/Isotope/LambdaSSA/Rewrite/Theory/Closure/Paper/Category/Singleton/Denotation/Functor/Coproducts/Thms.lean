module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationCoproducts

/-! # Coproduct preservation by guarded singleton denotation -/

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

include shared in
theorem denoteFunctor_map_inl (A B : τ) :
    (F).map (coprod.inl : ofType A ⟶ ofType A ⨿ ofType B) ≫
      (denoteCoprodIso J M shared A B).hom = coprod.inl :=
  DenotationCoproducts.mapInl J M shared A B

include shared in
theorem denoteFunctor_map_inr (A B : τ) :
    (F).map (coprod.inr : ofType B ⟶ ofType A ⨿ ofType B) ≫
      (denoteCoprodIso J M shared A B).hom = coprod.inr :=
  DenotationCoproducts.mapInr J M shared A B

include shared in
theorem denoteFunctor_coprodComparison (A B : τ) :
    coprodComparison (F) (ofType A) (ofType B) = (denoteCoprodIso J M shared A B).inv :=
  DenotationCoproducts.comparison J M shared A B

include shared in
theorem denoteFunctor_map_desc {A B D : τ} (f : ofType A ⟶ ofType D) (g : ofType B ⟶ ofType D) :
    (F).map (coprod.desc f g) = (denoteCoprodIso J M shared A B).hom ≫
      coprod.desc ((F).map f) ((F).map g) :=
  DenotationCoproducts.mapDesc J M shared f g

include shared in
theorem denoteFunctor_preservesBinaryCoproducts : PreservesColimitsOfShape (Discrete WalkingPair) (F) :=
  DenotationCoproducts.preservesBinary (Φ := Φ) J M shared

include shared in
theorem denoteFunctor_preservesFiniteCoproducts : PreservesFiniteCoproducts (F) :=
  DenotationCoproducts.preservesFinite (Φ := Φ) J M shared

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
