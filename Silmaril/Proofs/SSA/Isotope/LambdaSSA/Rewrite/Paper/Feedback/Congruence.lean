module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Postcompose.Thms

/-! # Feedback and outward continuations respect the paper relation -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

theorem feedback_congr {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Equivalent Γ L (L ++ K) σ υ) :
    Equivalent Γ L K (feedbackRegion L σ) (feedbackRegion L υ) := by
  intro i A hi
  let R : Fin L.length → τ := L.get
  have hR : List.ofFn R = L := List.ofFn_get L
  refine .cfg R (.refl (.br ?_ (.var rfl))) (fun j => ?_)
  · simpa only [hR, At, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1] using hi
  · have hj : At L j (R j) := by simp [R, At]
    rw [hR]
    exact (h hj).renameVars ((Ren.wk Γ A).lift (R j))

private theorem lift_local (n i : Nat) (σ : Nat → Region Φ) (hi : i < n) :
    liftLSubstN n σ i = labelId i := by
  induction n generalizing i with
  | zero => exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (liftLSubstN n σ i).renameLabels Nat.succ = _
      rw [ih i (Nat.lt_of_succ_lt_succ hi)]
      rfl

private theorem lift_outward (n i : Nat) (σ : Nat → Region Φ) :
    liftLSubstN n σ (n + i) = (σ i).renameLabels (n + ·) := by
  induction n with
  | zero =>
    rw [liftLSubstN, Nat.zero_add, show (fun j : Nat => 0 + j) = id from funext Nat.zero_add, renameLabels_id]
  | succ n ih =>
    rw [Nat.succ_add]
    change (liftLSubstN n σ (n + i)).renameLabels Nat.succ = _
    rw [ih, renameLabels_comp]
    congr 1
    funext j
    change Nat.succ (n + j) = n + 1 + j
    omega

theorem prepend_congr (X : ContinuationContext Φ Γ) {Y Z : ContinuationContext Φ Γ}
    {σ υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels}
    (h : Equivalent Γ Y.labels Z.labels σ.val υ.val) :
    Equivalent Γ (X.append Y).labels (X.append Z).labels
      (CfgEta.prependFamily X σ).val (CfgEta.prependFamily X υ).val := by
  intro i A hi
  change At (X.labels ++ Y.labels) i A at hi
  change Eqv (A :: Γ) (liftLSubstN X.labels.length σ.val i)
    (liftLSubstN X.labels.length υ.val i) (X.labels ++ Z.labels)
  by_cases hlt : i < X.labels.length
  · rw [lift_local _ _ _ hlt, lift_local _ _ _ hlt]
    rw [At, List.getElem?_append_left hlt] at hi
    exact .refl (.br ((List.getElem?_append_left hlt).trans hi) (.var rfl))
  · have hle := Nat.le_of_not_gt hlt
    rw [At, List.getElem?_append_right hle] at hi
    have hshift : Ren Z.labels (X.labels ++ Z.labels) (X.labels.length + ·) := by
      intro j T hj
      rw [At, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact hj
    rw [← Nat.add_sub_of_le hle, lift_outward, lift_outward]
    exact (h hi).renameLabels hshift

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
