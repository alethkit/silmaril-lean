module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels

/-! # Branch argument normalization respects native rewrite equivalence -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {Φ : Type v}

theorem bindBranchArguments_renameLabels (r : Region Φ) (ρ : Nat → Nat) :
    (r.renameLabels ρ).bindBranchArguments = r.bindBranchArguments.renameLabels ρ := by
  induction r generalizing ρ <;> simp_all only [renameLabels, bindBranchArguments]

theorem bindBranchArguments_renameVars (r : Region Φ) (ρ : Nat → Nat) :
    (r.renameVars ρ).bindBranchArguments = r.bindBranchArguments.renameVars ρ := by
  induction r generalizing ρ <;>
    simp_all only [renameVars, bindBranchArguments, Tm.rename, Silmaril.DeBruijn.lift]

theorem bindBranchArguments_substVars (r : Region Φ) (σ : Nat → Tm Φ) :
    (r.substVars σ).bindBranchArguments = r.bindBranchArguments.substVars σ := by
  induction r generalizing σ <;>
    simp_all only [substVars, bindBranchArguments, Tm.subst, Tm.liftSubst]

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem normalizedBranch {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {ℓ : Nat} {A : τ}
    (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A) :
    SubstitutionEquiv Γ (Region.br ℓ a).bindBranchArguments (.br ℓ a) L :=
  .letValue ha (.br hℓ (.var rfl))

private theorem normalizedLetValue {Γ : VCtx τ} {L : LCtx τ} {A : τ} {a : Tm Φ} {r : Region Φ}
    (ha : Tm.BranchValue Γ a A) (hr : Region.HasType (A :: Γ) r L) :
    SubstitutionEquiv Γ (Region.let₁ a r).bindBranchArguments
      (r.substVars (Tm.singleSubst a)).bindBranchArguments L := by
  rw [bindBranchArguments_substVars]
  exact .letValue ha hr.bindBranchArguments.hasType

private theorem cfgEquiv_normalize {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : CfgEquiv Γ r s L) : SubstitutionEquiv Γ r.bindBranchArguments s.bindBranchArguments L := by
  induction h with
  | refl hr => exact .base (.refl hr.bindBranchArguments.hasType)
  | symm _ ih => exact .symm ih
  | trans _ _ ihr ihs => exact .trans ihr ihs
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | cfgZero he _ => exact .base (.entry (.cfgZero he.bindBranchArguments.hasType _))
  | cfgBrExit R hℓ ha hb =>
      have hblocks := fun i => (hb i).bindBranchArguments.hasType
      exact .trans (.cfg R (normalizedBranch (exitAt R hℓ) ha)
          (fun i => .base (.refl (hblocks i))))
        (.trans (.base (.entry (.cfgBrExit R hℓ ha hblocks))) (.symm (normalizedBranch hℓ ha)))
  | cfgBrLocal R i ha hb =>
      have hblocks := fun j => (hb j).bindBranchArguments.hasType
      exact .trans (.cfg R (normalizedBranch (localAt R i _) ha)
          (fun j => .base (.refl (hblocks j))))
        (.base (.entry (.cfgBrLocal R i ha hblocks)))

private theorem rewriteEquiv_normalize {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) : SubstitutionEquiv Γ r.bindBranchArguments s.bindBranchArguments L := by
  induction h with
  | entry h => exact cfgEquiv_normalize h
  | symm _ ih => exact .symm ih
  | trans _ _ ihr ihs => exact .trans ihr ihs
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | letBr ha hb hℓ => exact normalizedLetValue ha (.br hℓ hb.hasType)
  | caseInl ha hl hr => exact .base (.caseInl ha hl.bindBranchArguments.hasType hr.bindBranchArguments.hasType)
  | caseInr hb hl hr => exact .base (.caseInr hb hl.bindBranchArguments.hasType hr.bindBranchArguments.hasType)

theorem substitutionEquiv_normalize {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) : SubstitutionEquiv Γ r.bindBranchArguments s.bindBranchArguments L := by
  induction h with
  | base h => exact rewriteEquiv_normalize h
  | symm _ ih => exact .symm ih
  | trans _ _ ihr ihs => exact .trans ihr ihs
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | letValue ha hr => exact normalizedLetValue ha hr
  | caseValue ha hr =>
      simpa only [bindBranchArguments, bindBranchArguments_substVars] using
        SubstitutionEquiv.caseValue ha hr.bindBranchArguments.hasType
  | @caseCfg Γ e A B l L r he hl hr =>
      let R : Fin 2 → τ := Fin.cases A (fun _ => B)
      have hl' := hl.bindBranchArguments.hasType
      have hr' := hr.bindBranchArguments.hasType
      have hmain := SubstitutionEquiv.caseCfg he hl' hr'
      refine hmain.trans ?_
      have hleft : SubstitutionEquiv (A :: Γ) (.br 0 (.var 0) : Region Φ)
          (Region.br 0 (.var 0)).bindBranchArguments (List.ofFn R ++ L) :=
        (normalizedBranch (localAt R 0 _) (.var (i := 0) rfl)).symm
      have hright : SubstitutionEquiv (B :: Γ) (.br 1 (.var 0) : Region Φ)
          (Region.br 1 (.var 0)).bindBranchArguments (List.ofFn R ++ L) :=
        (normalizedBranch (localAt R 1 _) (.var (i := 0) rfl)).symm
      refine .cfg R (.case he hleft hright) (fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cases_zero, bindBranchArguments_renameLabels]
        exact .base (.refl (hl'.renameLabels (fun _ _ hi => exitAt R hi)))
      · simp only [Fin.cases_succ, bindBranchArguments_renameLabels]
        exact .base (.refl (hr'.renameLabels (fun _ _ hi => exitAt R hi)))
  | initial ha hr hs => exact .initial ha hr.bindBranchArguments.hasType hs.bindBranchArguments.hasType
  | cfgOutward R hr hb =>
      simpa only [bindBranchArguments, bindBranchArguments_renameLabels] using
        SubstitutionEquiv.cfgOutward R hr.bindBranchArguments.hasType
          (fun i => (hb i).bindBranchArguments.hasType)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
