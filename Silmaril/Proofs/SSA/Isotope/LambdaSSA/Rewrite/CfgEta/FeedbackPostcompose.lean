module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Postcompose.Defs

/-! # Outgoing continuation substitution through feedback -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (Equivalent Eqv Interface prependFamily fromNative toHom toHom_eq_iff)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

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

private theorem refl_eqv {r : Region Φ} {Δ : VCtx τ} {P : LCtx τ} (h : HasType Δ r P) :
    Eqv Δ r r P := .native (.base (.refl h))

theorem prependFamily_congr (X : ContinuationContext Φ Γ) {Y Z : ContinuationContext Φ Γ}
    {σ υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels}
    (h : Equivalent Γ Y.labels Z.labels σ.val υ.val) :
    Equivalent Γ (X.append Y).labels (X.append Z).labels
      (prependFamily X σ).val (prependFamily X υ).val := by
  intro i A hi
  change At (X.labels ++ Y.labels) i A at hi
  change Eqv (A :: Γ) (liftLSubstN X.labels.length σ.val i)
    (liftLSubstN X.labels.length υ.val i) (X.labels ++ Z.labels)
  by_cases hlt : i < X.labels.length
  · rw [lift_local _ _ _ hlt, lift_local _ _ _ hlt]
    rw [At, List.getElem?_append_left hlt] at hi
    exact refl_eqv (.br ((List.getElem?_append_left hlt).trans hi) (.var rfl))
  · have hle := Nat.le_of_not_gt hlt
    rw [At, List.getElem?_append_right hle] at hi
    have hshift : Ren Z.labels (X.labels ++ Z.labels) (X.labels.length + ·) := by
      intro j T hj
      rw [At, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact hj
    have h' := (h hi).renameLabels hshift
    rw [← Nat.add_sub_of_le hle, lift_outward, lift_outward]
    exact h'

private theorem liftVars_liftN (n : Nat) (σ : Nat → Region Φ) :
    liftLSubstVars (liftLSubstN n σ) = liftLSubstN n (liftLSubstVars σ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have commute (υ : Nat → Region Φ) :
        liftLSubstVars (liftLSubst υ) = liftLSubst (liftLSubstVars υ) := by
      funext i
      cases i with
      | zero => rfl
      | succ i => exact (υ i).renameVars_renameLabels (lift Nat.succ) Nat.succ
    simp only [liftLSubstN, commute, ih]

private theorem weaken_twice (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
      (r.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) := by
  rw [renameVars_comp, renameVars_comp]
  congr 1
  funext i
  cases i <;> rfl

omit [TypeFormers τ] [HasTy Φ τ] in
/-- This equality operates on raw CFG representatives. The entry must select a local block. -/
theorem feedbackRegion_postcompose (L : LCtx τ) (σ υ : Nat → Region Φ) (i : Nat)
    (hi : i < L.length) :
    (feedbackRegion L σ i).lsubst (liftLSubstVars υ) =
      feedbackRegion L (compLSubst σ (liftLSubstN L.length υ)) i := by
  simp only [feedbackRegion, cfgEntryContinuations, lsubst, lift_local _ i _ hi]
  congr 1
  funext j
  simp only [compLSubst, renameVars_lsubst, ← liftVars_liftN, liftLSubstVars, weaken_twice]
  rfl

variable {X Y Z : ContinuationContext Φ Γ}

theorem feedback_postcompose_reps
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels (X.append Y).labels)
    (υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels) :
    Region.CfgEta.feedback (X := X) (Y := Y) (toHom σ) ≫ toHom (X := fromNative.obj Y) (Y := fromNative.obj Z) υ =
      Region.CfgEta.feedback (X := X) (Y := Z) (toHom σ ≫ toHom (prependFamily X υ)) := by
  apply toHom_eq_iff.mpr
  intro i A hi
  have he := feedbackRegion_postcompose X.labels σ.val υ.val i (List.getElem?_eq_some_iff.mp hi).1
  change Eqv (A :: Γ) ((feedbackRegion X.labels σ.val i).lsubst (liftLSubstVars υ.val))
    (feedbackRegion X.labels (compLSubst σ.val (liftLSubstN X.labels.length υ.val)) i) Z.labels
  rw [he]
  exact refl_eqv (((σ.compose (prependFamily X υ)).feedback (X := X) (Y := Z)).property hi).hasType

theorem appendInl_prepend_reps (X : ContinuationContext Φ Γ)
    (υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels) :
    fromNative.map (X.appendInl Y) ≫ toHom (prependFamily X υ) = fromNative.map (X.appendInl Z) := by
  apply toHom_eq_iff.mpr
  intro i A hi
  change At X.labels i A at hi
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  change Eqv (A :: Γ) (compLSubst labelId (liftLSubstN X.labels.length υ.val) i)
    (labelId i) (X.labels ++ Z.labels)
  rw [compLSubst_id_left, lift_local _ _ _ hlt]
  exact refl_eqv (.br ((List.getElem?_append_left hlt).trans hi) (.var rfl))

theorem appendInr_prepend_reps (X : ContinuationContext Φ Γ)
    (υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels) :
    fromNative.map (X.appendInr Y) ≫ toHom (prependFamily X υ) =
      toHom υ ≫ fromNative.map (X.appendInr Z) := by
  apply toHom_eq_iff.mpr
  intro i A hi
  let n := X.labels.length
  change Eqv (A :: Γ)
    (compLSubst labelId (liftLSubstN n υ.val) (n + i))
    ((υ.val i).lsubst (labelId ∘ (n + ·))) (X.labels ++ Z.labels)
  rw [compLSubst_id_left, lift_outward, ← renameLabels_eq_lsubst]
  apply refl_eqv
  refine (υ.property hi).hasType.renameLabels ?_
  intro j D hj
  change At (X.labels ++ Z.labels) (X.labels.length + j) D
  rw [At, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact hj

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
