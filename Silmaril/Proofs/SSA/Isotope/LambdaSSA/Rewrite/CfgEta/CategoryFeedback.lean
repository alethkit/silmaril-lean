module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Thms

/-! # Congruence of CFG feedback in the enlarged relation -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

theorem feedback_congr {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Equivalent Γ L (L ++ K) σ υ) :
    Equivalent Γ L K (feedbackRegion L σ) (feedbackRegion L υ) := by
  intro i A hi
  let R : Fin L.length → τ := L.get
  have hR : List.ofFn R = L := List.ofFn_get L
  refine .cfg R (.native (.base (.refl (.br ?_ (.var rfl))))) (fun j => ?_)
  · simpa only [hR, At, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1] using hi
  · have hj : At L j (R j) := by simp [R, At]
    rw [hR]
    exact (h hj).renameVars ((Ren.wk Γ A).lift (R j))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
