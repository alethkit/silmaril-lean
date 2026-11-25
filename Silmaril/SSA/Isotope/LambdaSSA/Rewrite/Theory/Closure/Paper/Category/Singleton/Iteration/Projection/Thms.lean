module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Projection.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IterationProjection

/-! # Projection for the retained-factor feedback step

These are the empty-capture singleton equations corresponding to
`Eqv.pi_r_fixpoint_uniform_inner` and `Eqv.pi_r_fixpoint` in the companion.
The lifted step threads the retained factor unchanged.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Projection

open CategoryTheory CategoryTheory.Limits
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- Projecting the lifted loop's result agrees with projecting its input before feedback. -/
theorem iterate_productSnd (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    iterate (whiskerLeft Z f ≫ (leftCoproductComparisonIso Z B A).inv) ≫ productSnd Z B =
      productSnd Z A ≫ iterate f :=
  IterationProjection.iterate_productSnd Z f

/-- Drop the retained component on the return branch of the lifted step. -/
theorem iterate_projected_whiskerLeft (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    iterate ((whiskerLeft Z f ≫ (leftCoproductComparisonIso Z B A).inv) ≫
      coprod.map (productSnd Z B) (𝟙 (tensorObj Z A))) =
      productSnd Z A ≫ iterate f :=
  IterationProjection.iterate_projected_whiskerLeft Z f

/-- The lifted step with projected results satisfies the ordinary simulation square.
The state map drops the retained factor and the outward result is fixed. -/
theorem projected_whiskerLeft_square (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    ((whiskerLeft Z f ≫ (leftCoproductComparisonIso Z B A).inv) ≫
      coprod.map (productSnd Z B) (𝟙 (tensorObj Z A))) ≫ coprod.map (𝟙 B) (productSnd Z A) =
      productSnd Z A ≫ f :=
  IterationProjection.projected_whiskerLeft_square Z f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Projection
