module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Postcompose.Thms

/-! # The return map of a singleton iteration step -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {B C : τ}

/-- Apply an arrow to the return summand and leave the repeat summand fixed. -/
@[expose] noncomputable def mapReturn (A : τ)
    (g : ofType (Φ := Φ) (Γ := Γ) B ⟶ ofType C) :
    ofType (Φ := Φ) (Γ := Γ) (Silmaril.coprod B A) ⟶ ofType (Silmaril.coprod C A) :=
  (sumIso B A).hom ≫ coprod.map g (𝟙 (ofType A)) ≫ (sumIso C A).inv

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
