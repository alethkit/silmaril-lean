module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationFeedback

/-! # Native CFG feedback is well defined on continuation arrows -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K : LCtx τ}

/-- Each feedback entry and its local CFG blocks retain value-branch typing. -/
theorem LSubst.ValueFamily.feedbackRegion {σ : Nat → Region Φ}
    (h : LSubst.ValueFamily Γ L (L ++ K) σ) :
    LSubst.ValueFamily Γ L K (Region.feedbackRegion L σ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.feedbackRegion_valueFamily h

/-- Changing any local body by a native equation preserves each feedback entry. -/
theorem feedbackRegion_congr {σ υ : Nat → Region Φ}
    (h : ∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (σ i) (υ i) (L ++ K)) :
    ∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (feedbackRegion L σ i) (feedbackRegion L υ i) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.feedbackRegion_congr h

/-- Entering a local block by its payload and unfolding that first branch
rewrites to the block body under the same CFG. -/
theorem LSubst.ValueFamily.feedbackRegion_unfold {σ : Nat → Region Φ}
    (h : LSubst.ValueFamily Γ L (L ++ K) σ) (i : Fin L.length) :
    SubstitutionEquiv (L.get i :: Γ) (Region.feedbackRegion L σ i)
      (.cfg (σ i) L.length (fun j => (σ j).renameVars (lift Nat.succ))) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.feedbackRegion_unfold h i

/-- Form a feedback loop on a representative by turning its first exits into
local CFG labels. -/
@[expose] def ContinuationFamily.feedback {X Y : ContinuationContext Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels (X.append Y).labels) :
    ContinuationFamily (Φ := Φ) Γ X.labels Y.labels :=
  ⟨feedbackRegion X.labels σ.val, σ.property.feedbackRegion⟩

/-- CFG feedback respects the native continuation quotient. -/
@[expose] def ContinuationContext.feedback {X Y : ContinuationContext Φ Γ} :
    (X ⟶ X.append Y) → (X ⟶ Y) :=
  Quotient.map (ContinuationFamily.feedback (X := X) (Y := Y))
    (fun _ _ => feedbackRegion_congr)

@[simp] theorem ContinuationFamily.feedback_toHom {X Y : ContinuationContext Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels (X.append Y).labels) :
    (σ.feedback (X := X) (Y := Y)).toHom = ContinuationContext.feedback (X := X) (Y := Y) σ.toHom :=
  rfl

end Silmaril.Isotope.LambdaSSA.Region
