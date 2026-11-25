module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms

/-! # The singleton projection used as a state change -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Projection

open CategoryTheory
open CfgEta.TypeCategory (productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- Unpack the product once and return its right component. -/
@[expose] def productSnd (Z A : Comp) : tensorObj Z A ⟶ A :=
  ofRegion (τ := τ) (productSndBranches (show τ from Z) (show τ from A))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Projection
