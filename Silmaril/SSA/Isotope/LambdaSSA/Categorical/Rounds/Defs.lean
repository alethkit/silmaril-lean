module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Rounds of a step in a category with iteration -/

@[expose] public section

universe v u

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/-- `roundsStep h n` runs up to `n + 1` rounds of `h`, stopping at the first return. -/
noncomputable def roundsStep {X Y : C} (h : X ⟶ Y ⨿ X) : Nat → (X ⟶ Y ⨿ X)
  | 0 => h
  | n + 1 => h ≫ coprod.desc coprod.inl (roundsStep h n)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
