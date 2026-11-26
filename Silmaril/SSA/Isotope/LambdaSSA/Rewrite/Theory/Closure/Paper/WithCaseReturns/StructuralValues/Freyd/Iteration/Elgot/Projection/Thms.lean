module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProjectionUniformity

/-! # Structural projection squares for the case-return iterator -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe

attribute [local instance] computationPremonoidal computationSymmetric computationDistributive

/-- Every square for the first projection out of a product with right factor unit is uniform. -/
theorem uniformity_fst_unit {B : Comp} (A : τ)
    (f : tensorObj Seed (ofType Seed A) (ofType Seed (Silmaril.unit : τ)) ⟶
      B ⨿ tensorObj Seed (ofType Seed A) (ofType Seed (Silmaril.unit : τ)))
    (g : ofType Seed A ⟶ B ⨿ ofType Seed A)
    (_square : f ≫ coprod.map (𝟙 B) (productFst Seed A Silmaril.unit) =
      productFst Seed A Silmaril.unit ≫ g) :
    iterateChosen Seed f = productFst Seed A Silmaril.unit ≫ iterateChosen Seed g :=
  ProjectedProjectionUniformity.uniformity_fst_unit pe A f g _square

/-- Every square for the second projection out of a product with left factor unit is uniform. -/
theorem uniformity_snd_unit {B : Comp} (A : τ)
    (f : tensorObj Seed (ofType Seed (Silmaril.unit : τ)) (ofType Seed A) ⟶
      B ⨿ tensorObj Seed (ofType Seed (Silmaril.unit : τ)) (ofType Seed A))
    (g : ofType Seed A ⟶ B ⨿ ofType Seed A)
    (_square : f ≫ coprod.map (𝟙 B) (productSnd Seed Silmaril.unit A) =
      productSnd Seed Silmaril.unit A ≫ g) :
    iterateChosen Seed f = productSnd Seed Silmaril.unit A ≫ iterateChosen Seed g :=
  ProjectedProjectionUniformity.uniformity_snd_unit pe A f g _square

/-- Drop a fixed retained factor after iterating its strengthened step. -/
theorem retained_snd (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    iterateChosen Seed (retainLeftStep pe R g) =
      productSnd Seed R.as A.as ≫ iterateChosen Seed g :=
  ProjectedProjectionUniformity.retained_snd pe R g

/-- The strengthened step with its result projected satisfies the second-projection square. -/
theorem retained_snd_square (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    retainLeftStep pe R g ≫ coprod.map (𝟙 B) (productSnd Seed R.as A.as) =
      productSnd Seed R.as A.as ≫ g :=
  ProjectedProjectionUniformity.retained_snd_square pe R g

/-- Projecting the retained right factor after the loop commutes with iteration. -/
theorem retained_fst (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    iterateChosen Seed (retainRightStep pe R g) =
      productFst Seed A.as R.as ≫ iterateChosen Seed g :=
  ProjectedProjectionUniformity.retained_fst pe R g

/-- The right-retaining step satisfies the first-projection square. -/
theorem retained_fst_square (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    retainRightStep pe R g ≫ coprod.map (𝟙 B) (productFst Seed A.as R.as) =
      productFst Seed A.as R.as ≫ g :=
  ProjectedProjectionUniformity.retained_fst_square pe R g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
