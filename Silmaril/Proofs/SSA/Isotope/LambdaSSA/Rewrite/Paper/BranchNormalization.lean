module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Composition.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Preservation of Paper rewrites by branch argument normalization -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchNormalization

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta (singleCfg)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem native {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) : Eqv Γ r s L :=
  .cfgEta (.native h)

private theorem normalized {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (h : ValueBranches Γ r L) : Eqv Γ r.bindBranchArguments r L :=
  native h.substitutionEquiv_bindBranchArguments.symm

private theorem normalized_of_guarded {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) (h : Eqv Γ r s L) :
    Eqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  (normalized hr).trans (h.trans (normalized hs).symm)

private theorem singleCfg_values {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L)) :
    ValueBranches Γ (singleCfg e p) L :=
  .cfg (fun _ : Fin 1 => A) he (fun _ => hp)

private theorem localMap_values {Γ : VCtx τ} {L : LCtx τ} {A D : τ} {a : Tm Φ}
    (ha : Tm.BranchValue (A :: Γ) a D) :
    LSubst.ValueFamily Γ (A :: L) (D :: L) (CfgEta.Uniformity.localMap a) := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact .br (ℓ := 0) rfl ha
  | succ i => exact .br (ℓ := i + 1) hi (.var rfl)

private theorem collapse_normalize {Γ : VCtx τ} {L K : LCtx τ} {A : τ} {e p : Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L))
    {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    Eqv Γ ((CfgEta.Codiagonal.nested e p).lsubst σ).bindBranchArguments
      ((CfgEta.Codiagonal.flattened e p).lsubst σ).bindBranchArguments K := by
  have left : ValueBranches Γ (CfgEta.Codiagonal.nested e p) L :=
    singleCfg_values he (singleCfg_values (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      (hp.renameVars ((Ren.wk Γ A).lift A)))
  have right : ValueBranches Γ (CfgEta.Codiagonal.flattened e p) L := by
    apply singleCfg_values he
    rw [renameLabels_eq_lsubst]
    exact hp.lsubst (fun i _ hi => .br (ℓ := i.pred) (CfgEta.Codiagonal.mergeLabels A L hi) (.var rfl))
  exact (native (left.normalize_lsubst hσ)).trans
    ((Eqv.collapsePost he hp (fun _ _ hi => (hσ hi).bindBranchArguments.hasType)).trans
      (native (right.normalize_lsubst hσ).symm))

private theorem uniform_normalize {Γ : VCtx τ} {L : LCtx τ} {A D : τ} {entry p q : Region Φ}
    {a : Tm Φ} (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : HasType (D :: Γ) q (D :: L)) (ha : Tm.BranchValue (A :: Γ) a D)
    (square : Eqv (A :: Γ)
      (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a))).bindBranchArguments
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q))).bindBranchArguments (D :: L)) :
    Eqv Γ (singleCfg entry p).bindBranchArguments
      (singleCfg (entry.lsubst (CfgEta.Uniformity.localMap a)) q).bindBranchArguments L := by
  have hm : LSubst.ValueFamily Γ (A :: L) (D :: L) (CfgEta.Uniformity.localMap a) :=
    localMap_values ha
  have hleft := hp.lsubst (hm.liftVars A)
  have hright : ValueBranches (A :: Γ) (.br 0 a) [D] := .br (ℓ := 0) rfl ha
  have hqFamily : LSubst.HasType Γ [D] (D :: L) (fun _ => q) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq
  have hrightNorm := hright.normalize_lsubst (hqFamily.liftVars A)
  rw [bindBranchArguments_liftLSubstVars] at hrightNorm
  have hstep := (normalized hleft).symm.trans (square.trans (native hrightNorm))
  have h := Eqv.uniform he hp hq.bindBranchArguments.hasType ha hstep
  exact (normalized (singleCfg_values he hp)).trans
    (h.trans (.cfg (fun _ : Fin 1 => D) (normalized (he.lsubst hm)).symm
      (fun _ => .refl hq.bindBranchArguments.hasType)))

theorem paper_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) : Eqv Γ r.bindBranchArguments s.bindBranchArguments L := by
  induction h with
  | cfgEta h => exact .cfgEta h.bindBranchArguments
  | productBeta h =>
      cases h with
      | let₂Beta ha hb hr =>
          rw [bindBranchArguments_substVars]
          exact .productBeta (.let₂Beta ha hb hr.bindBranchArguments.hasType)
  | productEta h =>
      cases h with
      | let₂Eta hi hℓ =>
          exact normalized_of_guarded (.let₂ (.var hi) (.br hℓ (.pair (.var rfl) (.var rfl))))
            (.br hℓ (.var hi)) (.productEta (.let₂Eta hi hℓ))
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp recur ih =>
      exact (native (hp.normalize_lsubst (fun _ _ hi => (recur hi).typed.1))).trans
        ((Eqv.lsubstCongr hp ih).trans
          (native (hp.normalize_lsubst (fun _ _ hi => (recur hi).typed.2)).symm))
  | lsubstPost h hr hs hσ _ =>
      exact (native (hr.normalize_lsubst hσ)).trans
        ((Eqv.lsubstPost h hr hs
          (fun _ _ hi => (hσ hi).bindBranchArguments.hasType)).trans
          (native (hs.normalize_lsubst hσ).symm))
  | substVars _ hθ ih =>
      simpa only [bindBranchArguments_substVars] using ih.substVars hθ
  | renameLabels _ hρ ih =>
      simpa only [bindBranchArguments_renameLabels] using ih.renameLabels hρ
  | collapsePost he hp hσ => exact collapse_normalize he hp hσ
  | uniform he hp hq ha _ ih => exact uniform_normalize he hp hq ha ih

namespace Extension

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension (Eqv)

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

theorem congr_of_guardedSeed
    (guarded : ∀ {Γ r s L}, Seed Γ r s L → ValueBranches Γ r L ∧ ValueBranches Γ s L)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Seed Γ r s L) : Eqv Seed Γ r.bindBranchArguments s.bindBranchArguments L := by
  induction h with
  | paper h => exact .paper (paper_congr h)
  | extra hr hs h =>
      obtain ⟨hr', hs'⟩ := guarded h
      exact (Eqv.paper (Seed := Seed) (normalized hr')).trans ((Eqv.extra hr hs h).trans (Eqv.paper (Seed := Seed) (normalized hs').symm))
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp recur ih =>
      exact (Eqv.paper (Seed := Seed) (native (hp.normalize_lsubst (fun _ _ hi => (recur hi).typed.1)))).trans
        ((Eqv.lsubstCongr hp ih).trans
          (Eqv.paper (Seed := Seed) (native (hp.normalize_lsubst (fun _ _ hi => (recur hi).typed.2)).symm)))
  | lsubstPost h hr hs hσ _ =>
      exact (Eqv.paper (Seed := Seed) (native (hr.normalize_lsubst hσ))).trans
        ((Eqv.lsubstPost h hr hs
          (fun _ _ hi => (hσ hi).bindBranchArguments.hasType)).trans
          (Eqv.paper (Seed := Seed) (native (hs.normalize_lsubst hσ).symm)))
  | substVars _ hθ ih =>
      simpa only [bindBranchArguments_substVars] using ih.substVars hθ
  | renameLabels _ hρ ih =>
      simpa only [bindBranchArguments_renameLabels] using ih.renameLabels hρ

end Extension
end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchNormalization
