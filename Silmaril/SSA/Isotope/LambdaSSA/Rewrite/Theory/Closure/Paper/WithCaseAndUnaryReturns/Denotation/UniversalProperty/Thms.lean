module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.UniversalProperty.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Denotation.Preservation.Thms

/-! # The universal property of the generated case and unary return domain -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

open Extension.Singleton.Generation

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "T" => Coordinates.ofModel J M

local notation "instruction" => InstructionModel.denote (J := J) (M := M)
local notation "Interpretation" => Domain.Interpretation (Seed) (T) (instruction)

/-- The guarded model supplies a structure-preserving interpretation of the
generated domain, with exact type coordinates and the given primitive maps. -/
noncomputable def generatedInterpretation : Interpretation :=
  Extension.Singleton.generatedInterpretation J M shared (stepDenotes pe J M shared)

local notation "canonical" => generatedInterpretation (Φ := Φ) pe J M shared

/-- Any interpretation sends each generated arrow to the model arrow in its specified coordinates. -/
theorem generatedInterpretation_map_eq (G : Interpretation) {A B : τ}
    (f : Domain.ofType (Seed) A ⟶ Domain.ofType (Seed) B) :
    (canonical).functor.map f = Domain.mapInCoordinates (Seed) G.functor G.objIso f :=
  Extension.Singleton.generatedInterpretation_map_eq J M shared (stepDenotes pe J M shared) G f

/-- Every preserving interpretation of the generated domain is canonically and
uniquely isomorphic to the model interpretation through its specified type isomorphisms. -/
theorem generatedInterpretation_universal (G : Interpretation) :
    ∃! e : (canonical).functor ≅ G.functor, ∀ A : τ,
      e.hom.app (Domain.ofType (Seed) A) = (G.objIso A).inv :=
  Extension.Singleton.generatedInterpretation_universal J M shared (stepDenotes pe J M shared) G

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns
