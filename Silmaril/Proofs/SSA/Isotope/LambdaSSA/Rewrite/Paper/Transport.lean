module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Typed renaming and guarded composition in the paper relation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Transport

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem compLSubst_congr {Γ : VCtx τ} {L K P : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : ∀ ⦃i A⦄, At L i A → Eqv (A :: Γ) (σ i) (σ' i) K)
    (hυ : ∀ ⦃i A⦄, At K i A → Eqv (A :: Γ) (υ i) (υ' i) P)
    (hsource : LSubst.ValueFamily Γ L K σ) (htarget : LSubst.ValueFamily Γ L K σ') :
    ∀ ⦃i A⦄, At L i A → Eqv (A :: Γ) (compLSubst σ υ i) (compLSubst σ' υ' i) P := by
  intro ℓ A hi
  have hυTyped : LSubst.HasType Γ K P υ := fun _ _ hj => (hυ hj).typed.1
  have hpost := Eqv.lsubstPost (hσ hi) (hsource hi) (htarget hi) (hυTyped.liftVars A)
  have hreplace : ∀ ⦃i B⦄, At K i B →
      Eqv (B :: A :: Γ) (liftLSubstVars υ i) (liftLSubstVars υ' i) P :=
    fun _ B hj => (hυ hj).renameVars ((Ren.wk Γ A).lift B)
  exact hpost.trans (.lsubstCongr (htarget hi) hreplace)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Transport
