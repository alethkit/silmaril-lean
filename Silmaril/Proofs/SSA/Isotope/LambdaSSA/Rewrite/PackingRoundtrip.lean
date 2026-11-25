module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Packing

/-! # Syntactic roundtrip for a packed exit interface -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} {Φ : Type v}

private theorem unpackExits_substVars (L : LCtx τ) (σ : Nat → Tm Φ)
    (h₀ : σ 0 = .var 0) :
    (unpackExits L).substVars σ = unpackExits L := by
  induction L generalizing σ with
  | nil => simp only [unpackExits, substVars, Tm.subst, Tm.liftSubst, h₀]
  | cons _ L ih =>
      simp only [unpackExits, substVars, Tm.subst, h₀, substVars_renameLabels,
        ih (Tm.liftSubst σ) (show Tm.liftSubst σ 0 = .var 0 from rfl), Tm.liftSubst]

private theorem unpackExits_cons_subst (B : τ) (L : LCtx τ) (a : Tm Φ) :
    (unpackExits (B :: L)).substVars (Tm.singleSubst a) =
      .case a (.br 0 (.var 0)) ((unpackExits L).renameLabels Nat.succ) := by
  change Region.case a (.br 0 (.var 0))
    (((unpackExits L).renameLabels Nat.succ).substVars (Tm.liftSubst (Tm.singleSubst a))) = _
  rw [substVars_renameLabels, unpackExits_substVars L (Tm.liftSubst (Tm.singleSubst a)) rfl]

variable [TypeFormers τ] [HasTy Φ τ]

private theorem equiv_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ} {ρ : Nat → Nat}
    (h : SubstitutionEquiv Γ r s L) (hρ : Ren L K ρ) :
    SubstitutionEquiv Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
  exact h.lsubst (fun _ _ hi => .br (hρ hi) (.var rfl))

theorem unpackExits_packedArg {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {A : τ} {a : Tm Φ}
    (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A) :
    SubstitutionEquiv Γ ((unpackExits L).substVars (Tm.singleSubst (packedExitArg ℓ a))) (.br ℓ a) L := by
  induction L generalizing Γ ℓ with
  | nil => simp [At] at hℓ
  | cons B L ih =>
      have hl : Region.HasType (B :: Γ) (.br 0 (.var 0) : Region Φ) (B :: L) := .br rfl (.var rfl)
      have hw := Silmaril.Isotope.SSA.Ren.wk L B
      have hr := (unpackExits_hasType (Φ := Φ) Γ L).renameLabels hw
      rw [unpackExits_cons_subst]
      cases ℓ with
      | zero =>
          cases Option.some.inj hℓ
          exact .trans (.base (.caseInl ha.hasType hl hr)) (.letValue ha hl)
      | succ ℓ =>
          have hv : Tm.BranchValue Γ (packedExitArg ℓ a) (packedExitType L) := packedExitArg_value hℓ ha
          refine .trans (.base (.caseInr hv.hasType hl hr)) (.trans (.letValue hv hr) ?_)
          rw [substVars_renameLabels]
          exact equiv_renameLabels (ih hℓ ha) hw

theorem unpack_packExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) :
    SubstitutionEquiv Γ (r.packExits.lsubst (fun _ => unpackExits L)) r L := by
  let inject : Nat → Region Φ := fun i => .br 0 (packedExitArg i (.var 0))
  let decode : Nat → Region Φ := fun _ => unpackExits L
  have hdecode : liftLSubstVars decode 0 = (unpackExits L : Region Φ) := by
    change (unpackExits L : Region Φ).renameVars (Silmaril.DeBruijn.lift Nat.succ) = unpackExits L
    rw [renameVars_eq_substVars]
    exact unpackExits_substVars L _ rfl
  have hpoint : ∀ ⦃ℓ A⦄, At L ℓ A →
      SubstitutionEquiv (A :: Γ) (compLSubst inject decode ℓ) (labelId ℓ) L := by
    intro ℓ A hℓ
    change SubstitutionEquiv (A :: Γ)
      ((liftLSubstVars decode 0).substVars (Tm.singleSubst (packedExitArg ℓ (.var 0)))) (.br ℓ (.var 0)) L
    rw [hdecode]
    exact unpackExits_packedArg hℓ (.var rfl)
  change SubstitutionEquiv Γ ((r.lsubst inject).lsubst decode) r L
  rw [lsubst_comp]
  simpa only [lsubst_labelId] using hr.lsubst_substitutionEquiv hpoint

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
