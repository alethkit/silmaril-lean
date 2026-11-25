module

public import Silmaril.Semantics.Categories.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms

/-! # Distributivity interface for extended singleton quotients -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CoproductDistributivity

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open scoped MonoidalCategory

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "Q" => TypeCategory Seed

variable [PremonoidalCategory Q]

/-- Fixed left tensor in the supplied premonoidal structure. -/
def leftTensorFunctor (X : Q) : Q ⥤ Q where
  obj Y := X ⊗ Y
  map f := X ◁ f
  map_id _ := PremonoidalCategory.whiskerLeft_id _ _
  map_comp f g := PremonoidalCategory.whiskerLeft_comp _ f g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CoproductDistributivity
