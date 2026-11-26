module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.UniversalProperty.Thms

/-! # The canonical model on the generated domain of the opt-in join -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns

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
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Interpretation" => Domain.Interpretation (Seed) (Coordinates.ofModel J M)
  (InstructionModel.denote (J := J) (M := M))

/-- The contextual soundness theorem supplies the canonical interpretation
in the model's exact object and primitive coordinates. -/
noncomputable def generatedInterpretation : Interpretation :=
  Extension.Singleton.generatedInterpretation J M shared (joined_seedDenotes pe J M shared)

local notation "canonical" => generatedInterpretation (Φ := Φ) pe J M shared

/-- Any preserving interpretation agrees with the model on each generated arrow. -/
theorem generatedInterpretation_map_eq (G : Interpretation) {A B : τ}
    (f : Domain.ofType (Seed) A ⟶ Domain.ofType (Seed) B) :
    (canonical).functor.map f = Domain.mapInCoordinates (Seed) G.functor G.objIso f :=
  Extension.Singleton.generatedInterpretation_map_eq J M shared (joined_seedDenotes pe J M shared) G f

/-- The specified object coordinates determine a unique natural comparison
with every interpretation on this generated domain. -/
theorem generatedInterpretation_universal (G : Interpretation) :
    ∃! e : (canonical).functor ≅ G.functor, ∀ A : τ,
      e.hom.app (Domain.ofType (Seed) A) = (G.objIso A).inv :=
  Extension.Singleton.generatedInterpretation_universal J M shared (joined_seedDenotes pe J M shared) G

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns
