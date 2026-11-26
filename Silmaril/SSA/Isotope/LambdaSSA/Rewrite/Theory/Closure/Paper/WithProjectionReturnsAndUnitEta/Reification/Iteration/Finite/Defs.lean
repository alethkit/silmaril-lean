module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs

/-! # Finite unfolding of a return-or-repeat step -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open CategoryTheory CategoryTheory.Limits

universe u v

/-- Unfold a step a finite number of times, with `tail` used on repeat after the last step. -/
noncomputable def unroll {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
    {A B : C} (step : A ⟶ B ⨿ A) (tail : A ⟶ B) : Nat → (A ⟶ B)
  | 0 => tail
  | n + 1 => step ≫ coprod.desc (𝟙 B) (unroll step tail n)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
