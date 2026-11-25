module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms

/-! # Interchange for the Paper singleton whiskerings -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- A central arrow interchanges with every computation in both factor orders. -/
def WhiskerCentral {A B : Comp} (f : A ⟶ B) : Prop :=
  ∀ {X Y : Comp} (g : X ⟶ Y),
    (whiskerRight f X ≫ whiskerLeft B g = whiskerLeft A g ≫ whiskerRight f Y) ∧
    (whiskerLeft X f ≫ whiskerRight g B = whiskerRight g A ≫ whiskerLeft Y f)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
