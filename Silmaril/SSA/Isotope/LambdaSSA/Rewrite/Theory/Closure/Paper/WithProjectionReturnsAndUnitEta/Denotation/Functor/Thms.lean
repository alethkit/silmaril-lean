module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Functor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotationFunctor

/-! # Functorial and coproduct comparisons for the joined denotation -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofType)
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
local notation "P" => projection (τ := τ) (Φ := Φ)
local notation "F" => Paper.TypeCategory.denoteFunctor (Φ := Φ) J M shared

local notation "G" => denoteFunctor (Φ := Φ) J M shared

/-- Composing with the quotient projection recovers the ordinary guarded functor. -/
theorem projection_comp_denoteFunctor : (P) ⋙ (G) = F :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotationFunctor.factorization J M shared

/-- The functor uses the existing joined denotation on each hom. -/
theorem denoteFunctor_map_arrow {A B : τ} (f : Obj A ⟶ Obj B) :
    (G).map f = denoteArrow J M shared f := rfl

/-- The quotient descent carries the ordinary interpretation's finite coproduct preservation. -/
theorem denoteFunctor_preservesFiniteCoproducts : PreservesFiniteCoproducts (G) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotationFunctor.preservesFinite J M shared

/-- Transport from the image of the joined chosen coproduct to the chosen target coproduct. -/
noncomputable def denoteFunctorCoprodIso (A B : τ) :
    (G).obj (Obj A ⨿ Obj B) ≅ (G).obj (Obj A) ⨿ (G).obj (Obj B) :=
  let := denoteFunctor_preservesFiniteCoproducts (Φ := Φ) J M shared
  (PreservesColimitPair.iso (G) (Obj A) (Obj B)).symm

/-- The inverse comparison is the canonical map induced by the two mapped injections. -/
theorem denoteFunctor_coprodComparison (A B : τ) :
    coprodComparison (G) (Obj A) (Obj B) = (denoteFunctorCoprodIso (Φ := Φ) J M shared A B).inv :=
  rfl

/-- Interpret the chosen joined iterator using the functor's chosen coproduct comparison. -/
theorem denoteFunctor_map_canonicalIterate {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    (G).map (canonicalIterate f) =
      CategoryTheory.iterate ((G).map f ≫ (denoteFunctorCoprodIso (Φ := Φ) J M shared B A).hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotationFunctor.mapIterate J M shared f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
