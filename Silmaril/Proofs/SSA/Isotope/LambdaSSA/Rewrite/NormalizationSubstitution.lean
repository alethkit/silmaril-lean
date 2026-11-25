module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizationCongruence
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ClosureValues
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Forwarding

/-! # Normalization and native continuation substitution -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {Φ : Type v}

theorem normalizeLiftVars (σ : Nat → Region Φ) :
    (fun ℓ => (liftLSubstVars σ ℓ).bindBranchArguments) =
      liftLSubstVars (fun ℓ => (σ ℓ).bindBranchArguments) := by
  funext ℓ
  exact bindBranchArguments_renameVars _ _

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem normalizeLiftLabels {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.HasType Γ L K σ) (Ξ : LCtx τ) :
    ∀ ⦃ℓ A⦄, At (Ξ ++ L) ℓ A →
      SubstitutionEquiv (A :: Γ) (liftLSubstN Ξ.length σ ℓ).bindBranchArguments
        (liftLSubstN Ξ.length (fun i => (σ i).bindBranchArguments) ℓ) (Ξ ++ K) := by
  intro ℓ A hℓ
  by_cases hlo : ℓ < Ξ.length
  · have hk : At (Ξ ++ K) ℓ A := by simpa only [At, List.getElem?_append_left hlo] using hℓ
    simp only [liftAtLocal _ hlo]
    exact .letValue (.var rfl) (.br hk (.var rfl))
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hlo)
    have ht := ((hσ.append Ξ) hℓ).bindBranchArguments.hasType
    simp only [liftAtExit, bindBranchArguments_renameLabels] at ht ⊢
    exact .base (.refl ht)

/-- Normalizing after substitution at value branches agrees with substituting
the normalized continuation bodies. -/
theorem normalize_lsubst_valueBranches {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    SubstitutionEquiv Γ (r.lsubst σ).bindBranchArguments
      (r.lsubst (fun i => (σ i).bindBranchArguments)) K := by
  induction hr generalizing K σ with
  | br hℓ ha =>
      simp only [lsubst, bindBranchArguments_substVars]
      exact .base (.refl ((hσ hℓ).bindBranchArguments.hasType.substVars (Tm.Subst.HasType.single ha.hasType)))
  | let₁ ha _ ih =>
      simpa only [lsubst, bindBranchArguments, normalizeLiftVars] using
        SubstitutionEquiv.let₁ ha (ih (hσ.liftVars _))
  | let₂ ha _ ih =>
      simpa only [lsubst, bindBranchArguments, normalizeLiftVars] using
        SubstitutionEquiv.let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | case ha _ _ ihl ihr =>
      simpa only [lsubst, bindBranchArguments, normalizeLiftVars] using
        SubstitutionEquiv.case ha (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | cfg R he hb ihe ihb =>
      have hlabels := hσ.append (List.ofFn R)
      simp only [List.length_ofFn] at hlabels
      have hnorm := normalizeLiftLabels hσ (List.ofFn R)
      simp only [List.length_ofFn] at hnorm
      refine .cfg R (.trans (ihe hlabels) (he.lsubst_substitutionEquiv hnorm)) (fun i => ?_)
      refine .trans ?_ ((hb i).lsubst_substitutionEquiv (substitutionEquiv_liftLSubstVars hnorm (R i)))
      simpa only [normalizeLiftVars] using ihb i (hlabels.liftVars (R i))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
