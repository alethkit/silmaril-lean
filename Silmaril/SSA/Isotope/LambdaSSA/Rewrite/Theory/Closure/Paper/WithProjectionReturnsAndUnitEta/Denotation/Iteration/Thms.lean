module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Representative.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationDenotation

/-! # Denotational preservation of joined singleton iteration -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofType sumIso)
open Reification (canonicalIterate)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (Seed)

/-- Normalize the chosen source coproduct to the exact syntax sum. The
ordinary model comparison then supplies the chosen coproduct in the target. -/
theorem denoteArrow_canonicalIterate {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    denoteArrow J M shared (canonicalIterate f) =
      CategoryTheory.iterate (denoteArrow J M shared (f ≫ (sumIso (Seed) B A).inv) ≫
        (Paper.TypeCategory.denoteExactSumIso J M B A).hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationDenotation.preserve J M shared f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
