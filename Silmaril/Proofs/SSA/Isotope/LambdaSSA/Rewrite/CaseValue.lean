module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

/-! # Substitution into the arms of a constructor-value case -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

theorem lsubst_replaceNewest (r : Region Φ) (a : Tm Φ) (σ : Nat → Region Φ) :
    (r.substVars (Tm.replaceNewest a)).lsubst (liftLSubstVars σ) =
      (r.lsubst (liftLSubstVars σ)).substVars (Tm.replaceNewest a) := by
  rw [substVars_lsubst]
  congr 1
  funext j
  have e : Tm.liftSubst (Tm.replaceNewest a) ∘ lift Nat.succ = Tm.var ∘ lift Nat.succ := by
    funext i
    cases i <;> rfl
  rw [mapLSubstVars, liftLSubstVars, substVars_renameVars, e, ← renameVars_eq_substVars]

theorem substVars_replaceNewest_lift (r : Region Φ) {a : Tm Φ} (θ : Nat → Tm Φ)
    (ha : a.subst (Tm.liftSubst θ) = a) :
    (r.substVars (Tm.replaceNewest a)).substVars (Tm.liftSubst θ) =
      (r.substVars (Tm.liftSubst θ)).substVars (Tm.replaceNewest a) := by
  rw [substVars_comp, substVars_comp]
  congr 1
  funext i
  cases i with
  | zero => exact ha
  | succ i =>
      change (θ i).rename Nat.succ = ((θ i).rename Nat.succ).subst (Tm.replaceNewest a)
      rw [Tm.subst_rename, show Tm.replaceNewest a ∘ Nat.succ = Tm.var ∘ Nat.succ from rfl,
        ← Tm.rename_eq_subst]

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

theorem replaceNewest_typed {Γ : VCtx τ} {a : Tm Φ} {A B : τ}
    (ha : Tm.HasType (B :: Γ) a A) :
    Tm.Subst.HasType (A :: Γ) (B :: Γ) (Tm.replaceNewest a) := by
  have h : Tm.Subst.HasType Γ (B :: Γ) ((Tm.var : Nat → Tm Φ) ∘ Nat.succ) :=
    fun _ _ hi => .var ((Silmaril.Isotope.SSA.Ren.wk Γ B) hi)
  exact h.cons ha

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
