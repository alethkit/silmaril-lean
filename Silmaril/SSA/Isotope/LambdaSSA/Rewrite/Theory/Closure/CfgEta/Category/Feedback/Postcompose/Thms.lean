module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Postcompose.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.FeedbackPostcompose

/-! # Postcomposition on the outward exits of CFG feedback -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {X Y Z : ContinuationContext Φ Γ}

/-- Lift an outward arrow while leaving every local exit fixed. -/
@[expose] def prepend (X : ContinuationContext Φ Γ) :
    (fromNative.obj Y ⟶ fromNative.obj Z) → (fromNative.obj (X.append Y) ⟶ fromNative.obj (X.append Z)) :=
  Quotient.map (prependFamily X) (fun _ _ h => by
    exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.prependFamily_congr X h)

@[reassoc] theorem appendInl_prepend (X : ContinuationContext Φ Γ)
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    fromNative.map (X.appendInl Y) ≫ prepend X g = fromNative.map (X.appendInl Z) :=
  Quotient.inductionOn g (Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.appendInl_prepend_reps X)

@[reassoc] theorem appendInr_prepend (X : ContinuationContext Φ Γ)
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    fromNative.map (X.appendInr Y) ≫ prepend X g = g ≫ fromNative.map (X.appendInr Z) :=
  Quotient.inductionOn g (Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.appendInr_prepend_reps X)

/-- Closing the local labels commutes with postcomposition on the outward exits. -/
theorem feedback_postcompose
    (f : fromNative.obj X ⟶ fromNative.obj (X.append Y))
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    feedback (X := X) (Y := Y) f ≫ g =
      feedback (X := X) (Y := Z) (f ≫ prepend X g) :=
  Quotient.inductionOn₂ f g Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.feedback_postcompose_reps

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
