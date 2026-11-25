module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategoryFeedback

/-! # Feedback on the CFG η quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- Pointwise equivalent blocks specify equivalent feedback entries. -/
theorem Equivalent.feedback {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Equivalent Γ L (L ++ K) σ υ) :
    Equivalent Γ L K (feedbackRegion L σ) (feedbackRegion L υ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.feedback_congr h

/-- Turn each input exit into a local CFG label in the enlarged quotient. -/
@[expose] def feedback {X Y : ContinuationContext Φ Γ} :
    (fromNative.obj X ⟶ fromNative.obj (X.append Y)) → (fromNative.obj X ⟶ fromNative.obj Y) :=
  Quotient.map (ContinuationFamily.feedback (X := X) (Y := Y)) (fun _ _ h => Equivalent.feedback h)

/-- Feedback of an image uses the same CFG as native feedback of its representative. -/
@[simp] theorem feedback_fromNative {X Y : ContinuationContext Φ Γ} (f : X ⟶ X.append Y) :
    feedback (X := X) (Y := Y) (fromNative.map f) = fromNative.map (ContinuationContext.feedback f) :=
  Quotient.inductionOn f (fun _ => rfl)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
