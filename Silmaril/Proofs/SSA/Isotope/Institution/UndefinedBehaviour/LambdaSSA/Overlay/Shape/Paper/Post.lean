module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta (singleCfg)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal (nested flattened)

universe u

variable {Φ : Type u} (e p : Region Φ) (k : Nat → Region Φ)

private theorem shift_capture :
    lift (lift Nat.succ) ∘ lift Nat.succ = lift Nat.succ ∘ lift Nat.succ := by
  funext i
  cases i <;> rfl

private theorem nested_captures :
    liftLSubstVars (liftLSubst (liftLSubstVars (liftLSubst k))) =
      fun i => (liftLSubstVars (liftLSubst (liftLSubst k)) i).renameVars (lift (lift Nat.succ)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [liftLSubst, liftLSubstVars, renameVars_renameLabels, renameVars_comp, shift_capture]

/-- Push the outgoing substitution through the two CFG binders. The inner
body passes over a captured copy of the outer payload. -/
theorem nested_post :
    (nested e p).lsubst k =
      nested (e.lsubst (liftLSubst k)) (p.lsubst (liftLSubstVars (liftLSubst (liftLSubst k)))) := by
  unfold nested singleCfg
  simp only [lsubst, liftLSubstN, renameVars_lsubst]
  rw [nested_captures]
  rfl

private theorem flattened_labels :
    liftLSubstVars (liftLSubst k) ∘ Nat.pred =
      mapLSubstLabels Nat.pred (liftLSubstVars (liftLSubst (liftLSubst k))) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [Function.comp_apply, Nat.pred_succ, mapLSubstLabels, liftLSubstVars,
        liftLSubst, renameVars_renameLabels, renameLabels_comp]
      rfl

/-- Merging the local labels commutes with the lifted outgoing substitution. -/
theorem flattened_post :
    (flattened e p).lsubst k =
      flattened (e.lsubst (liftLSubst k)) (p.lsubst (liftLSubstVars (liftLSubst (liftLSubst k)))) := by
  unfold flattened singleCfg
  simp only [lsubst, liftLSubstN, lsubst_renameLabels, renameLabels_lsubst, flattened_labels]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
