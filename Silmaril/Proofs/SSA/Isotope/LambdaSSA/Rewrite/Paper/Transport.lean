module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Thms

/-! # Typed renaming and guarded composition in the paper relation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Transport

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.DeBruijn (lift)

universe u v
variable {Φ : Type v}

private theorem rename_weaken (r : Region Φ) (ρ : Nat → Nat) :
    (r.renameVars (lift Nat.succ)).renameVars (lift (lift ρ)) =
      (r.renameVars (lift ρ)).renameVars (lift Nat.succ) := by
  rw [renameVars_comp, renameVars_comp]
  congr 1
  funext i
  cases i <;> rfl

private theorem rename_lift_family (σ : Nat → Region Φ) (ρ : Nat → Nat) :
    (fun i => (liftLSubstVars σ i).renameVars (lift (lift ρ))) =
      liftLSubstVars (fun i => (σ i).renameVars (lift ρ)) := by
  funext i
  exact rename_weaken (σ i) ρ

private theorem rename_singleCfg (r s : Region Φ) (ρ : Nat → Nat) :
    (CfgEta.singleCfg r s).renameVars ρ = CfgEta.singleCfg (r.renameVars ρ) (s.renameVars (lift ρ)) := rfl

private theorem rename_nested (r s : Region Φ) (ρ : Nat → Nat) :
    (CfgEta.Codiagonal.nested r s).renameVars ρ =
      CfgEta.Codiagonal.nested (r.renameVars ρ) (s.renameVars (lift ρ)) := by
  simp only [CfgEta.Codiagonal.nested, rename_singleCfg, renameVars, Tm.rename, lift, rename_weaken]

private theorem rename_flattened (r s : Region Φ) (ρ : Nat → Nat) :
    (CfgEta.Codiagonal.flattened r s).renameVars ρ =
      CfgEta.Codiagonal.flattened (r.renameVars ρ) (s.renameVars (lift ρ)) := by
  simp only [CfgEta.Codiagonal.flattened, rename_singleCfg, renameVars_renameLabels]

private theorem rename_localMap (a : Tm Φ) (ρ : Nat → Nat) :
    (fun i => (CfgEta.Uniformity.localMap a i).renameVars (lift ρ)) =
      CfgEta.Uniformity.localMap (a.rename (lift ρ)) := by
  funext i
  cases i <;> rfl

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem rename_branchValue {Γ Δ : VCtx τ} {A : τ} {a : Tm Φ} {ρ : Nat → Nat}
    (ha : Tm.BranchValue Γ a A) (hρ : Ren Γ Δ ρ) : Tm.BranchValue Δ (a.rename ρ) A := by
  have hv : ValueBranches Γ (.br 0 a) [A] := .br rfl ha
  have hrenamed : ValueBranches Δ (.br 0 (a.rename ρ)) [A] := hv.renameVars hρ
  cases hrenamed with
  | br hℓ ha => cases Option.some.inj hℓ; exact ha

private theorem rename_beta {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {ρ : Nat → Nat}
    (h : ProductBeta.Step Γ r s L) (hρ : Ren Γ Δ ρ) :
    ProductBeta.Step Δ (r.renameVars ρ) (s.renameVars ρ) L := by
  cases h with
  | @let₂Beta a A b B r L ha hb hr =>
    have e : (r.substVars (Tm.consSubst b (Tm.singleSubst a))).renameVars ρ =
        (r.renameVars (lift (lift ρ))).substVars
          (Tm.consSubst (b.rename ρ) (Tm.singleSubst (a.rename ρ))) := by
      rw [renameVars_substVars, substVars_renameVars]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
    rw [e]
    exact .let₂Beta (rename_branchValue ha hρ) (rename_branchValue hb hρ) (hr.renameVars ((hρ.lift A).lift B))

private theorem rename_family {Γ Δ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ} {ρ : Nat → Nat}
    (hσ : LSubst.HasType Γ L K σ) (hρ : Ren Γ Δ ρ) :
    LSubst.HasType Δ L K (fun i => (σ i).renameVars (lift ρ)) :=
  fun _ A hi => (hσ hi).renameVars (hρ.lift A)

theorem eqv_renameVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    Eqv Δ (r.renameVars ρ) (s.renameVars ρ) L := by
  induction h generalizing Δ ρ with
  | cfgEta h => exact .cfgEta (h.renameVars hρ)
  | productBeta h => exact .productBeta (rename_beta h hρ)
  | productEta h => exact .productEta (h.renameVars hρ)
  | symm _ ih => exact .symm (ih hρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hρ) (ih₂ hρ)
  | let₁ ha _ ih => exact .let₁ (ha.rename hρ) (ih (hρ.lift _))
  | let₂ ha _ ih => exact .let₂ (ha.rename hρ) (ih ((hρ.lift _).lift _))
  | case ha _ _ ih₁ ih₂ => exact .case (ha.rename hρ) (ih₁ (hρ.lift _)) (ih₂ (hρ.lift _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hρ) (fun i => ihb i (hρ.lift _))
  | lsubstCongr hp _ ih =>
    rw [renameVars_lsubst, renameVars_lsubst]
    exact .lsubstCongr (hp.renameVars hρ) (fun _ A hi => ih hi (hρ.lift A))
  | lsubstPost _ hr hs hσ ih =>
    rw [renameVars_lsubst, renameVars_lsubst]
    exact .lsubstPost (ih hρ) (hr.renameVars hρ) (hs.renameVars hρ) (rename_family hσ hρ)
  | collapsePost he hp hσ =>
    rw [renameVars_lsubst, renameVars_lsubst, rename_nested, rename_flattened]
    exact .collapsePost (he.renameVars hρ) (hp.renameVars (hρ.lift _)) (rename_family hσ hρ)
  | uniform he hp hq ha _ ih =>
    rw [rename_singleCfg, rename_singleCfg, renameVars_lsubst, rename_localMap]
    refine .uniform (he.renameVars hρ) (hp.renameVars (hρ.lift _)) (hq.renameVars (hρ.lift _))
      (rename_branchValue ha (hρ.lift _)) ?_
    simpa only [renameVars_lsubst, rename_lift_family, rename_localMap, renameVars] using ih (hρ.lift _)

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
    fun _ B hj => eqv_renameVars (hυ hj) ((Ren.wk Γ A).lift B)
  exact hpost.trans (.lsubstCongr (htarget hi) hreplace)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Transport
