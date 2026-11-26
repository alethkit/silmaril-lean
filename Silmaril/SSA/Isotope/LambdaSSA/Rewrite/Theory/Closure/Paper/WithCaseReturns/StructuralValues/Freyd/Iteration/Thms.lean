module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Thms

/-! # Guarded iteration strength for the case-return computation model -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen
  (projectedChosenDistributor projectedChosenDistributor_hom)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (iterateChosen whiskerLeftFunctor whiskerLeft_iterateChosen)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Comp" => TypeCategory (τ := τ) (Φ := Φ) pe

attribute [local instance] computationPremonoidal computationSymmetric computationDistributive

/-- The chosen-coproduct guarded iterator for the structural Freyd model's computations. -/
noncomputable abbrev guardedIteration : Iteration Comp :=
  Extension.Singleton.guardedIteration Seed

/-- The model's canonical left distributor is the projected guarded distributor with sum conversions. -/
theorem leftIso_eq_guarded (Z B A : Comp) :
    DistributiveTensor.leftIso Z B A = projectedChosenDistributor Seed Z.as B.as A.as := by
  apply Iso.ext
  rw [projectedChosenDistributor_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The guarded iterator satisfies the exact strength field on the model's chosen coproducts. -/
theorem iterate_whiskerLeft (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    letI := guardedIteration (τ := τ) (Φ := Φ) pe
    CategoryTheory.iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z B A) =
      Z ◁ CategoryTheory.iterate f := by
  change iterateChosen Seed ((whiskerLeftFunctor Seed Z).map f ≫ (DistributiveTensor.leftIso Z B A).inv) =
    (whiskerLeftFunctor Seed Z).map (iterateChosen Seed f)
  rw [leftIso_eq_guarded pe Z B A]
  exact whiskerLeft_iterateChosen Seed (show τ from Z.as) f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
