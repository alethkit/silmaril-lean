module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

/-! # Contextual iteration for LambdaSSA CFG denotations -/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.Calco2019.LambdaSSA

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Isotope.LetIter.ProofRelevant.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

/-- Make the retained context part of the state and of the returned value.
The external exit is on the left and the local-label continuation is on the right. -/
noncomputable def contextualBody {R A B : V}
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    J.obj (R ⊗ A) ⟶ J.obj (R ⊗ B) ⨿ J.obj (R ⊗ A) :=
  J.map (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst R A) (𝟙 (R ⊗ A))) ≫
    retainLeft J body ≫
    J.map (DistributiveTensor.leftIso R B A).inv ≫
    splitMapCoprod J (R ⊗ B) (R ⊗ A)

end Silmaril.Isotope.Calco2019.LambdaSSA
