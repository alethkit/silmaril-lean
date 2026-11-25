module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms

/-! # Guarded projections and literal sections at the unit type -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => product

abbrev leftUnitProjection (A : τ) : Obj (U ×ₜ A) ⟶ Obj A := ofRegion (productSndBranches U A)
abbrev rightUnitProjection (A : τ) : Obj (A ×ₜ U) ⟶ Obj A := ofRegion (productFstBranches A U)

def leftUnitSection (A : τ) : Obj A ⟶ Obj (U ×ₜ A) :=
  ofRegion (.br (ℓ := 0) rfl (.pair .unit (.var (i := 0) rfl)))

def rightUnitSection (A : τ) : Obj A ⟶ Obj (A ×ₜ U) :=
  ofRegion (.br (ℓ := 0) rfl (.pair (.var (i := 0) rfl) .unit))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
