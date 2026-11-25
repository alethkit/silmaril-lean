module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms

/-! # Interchange for the two singleton whiskerings -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory Φ ([] : VCtx τ)

/-- The two interchange squares using the current whiskering operations. -/
def WhiskerCentral {A B : Comp} (f : A ⟶ B) : Prop :=
  ∀ {X Y : Comp} (g : X ⟶ Y),
    (whiskerRight f X ≫ whiskerLeft B g = whiskerLeft A g ≫ whiskerRight f Y) ∧
    (whiskerLeft X f ≫ whiskerRight g B = whiskerRight g A ≫ whiskerLeft Y f)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
