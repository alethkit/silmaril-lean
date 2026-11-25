module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Finite coproducts in the Paper singleton category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

instance hasInitial : HasInitial (TypeCategory (τ := τ) Φ) :=
  (emptyIsInitial (τ := τ) (Φ := Φ)).hasInitial

instance hasFiniteCoproducts : HasFiniteCoproducts (TypeCategory (τ := τ) Φ) :=
  hasFiniteCoproducts_of_has_binary_and_initial

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
