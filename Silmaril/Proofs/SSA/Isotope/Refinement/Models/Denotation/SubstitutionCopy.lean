module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionSplitting

/-! # Entrywise duplication of interpreted substitutions -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]

/-- Each split component has at least the resource permissions of its source. -/
theorem QCtx.Split.linearity_le_left {n : Nat} {Γ Γl Γr : QCtx τ n} (s : Γ.Split Γl Γr) :
    Γ.linearity ≤ Γl.linearity := by
  apply QCtx.le_linearity_iff.mpr
  intro i
  have h := (QCtx.le_linearity_iff.mp (le_rfl : Γ.linearity ≤ Γ.linearity)) i
  rw [(s i).2.2.linearity] at h
  simpa only [(s i).1] using h.trans inf_le_left

namespace Models
namespace SeqModel
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Tensoring commuting computations preserves their directed copy comparisons. -/
theorem tensor_copy (p : Polarity) {e η : ε} {A B D E : τ}
    (f : M.Hom A B) (g : M.Hom D E)
    (cA : Quantity.relevant ≤ quantity A) (cB : Quantity.relevant ≤ quantity B)
    (cD : Quantity.relevant ≤ quantity D) (cE : Quantity.relevant ≤ quantity E)
    (cAD : Quantity.relevant ≤ quantity (product A D))
    (cBE : Quantity.relevant ≤ quantity (product B E))
    (hf : p.orient M.le (M.compose f (M.copy B cB)) (M.compose (M.copy A cA) (M.tensor f f)))
    (hg : p.orient M.le (M.compose g (M.copy E cE)) (M.compose (M.copy D cD) (M.tensor g g)))
    (hm : EffectSystem.commutes e η) (hfe : M.hasEffect e f) (hge : M.hasEffect η g) :
    p.orient M.le (M.compose (M.tensor f g) (M.copy (product B E) cBE))
      (M.compose (M.copy (product A D) cAD) (M.tensor (M.tensor f g) (M.tensor f g))) := by
  rw [M.copy_product _ _ cB cE,
    ← M.toSeqData.compose_assoc (M.tensor f g),
    M.toSeqData.tensor_comp_pure_middle _ _ _ _ (M.toSeqData.copy_pure _ cB)]
  have h := M.toSeqData.orient_compose_right p (M.toSeqData.orient_tensor p hf hg) (M.middleSwap B B E E)
  rw [← M.toSeqData.tensor_comp_pure _ _ _ _ (M.toSeqData.copy_pure _ cD),
    M.toSeqData.compose_assoc, M.toSeqData.tensor_middleSwap _ _ _ _ hm hfe hge,
    ← M.toSeqData.compose_assoc, ← M.copy_product _ _ cA cD] at h
  exact h

end SeqModel
namespace Denotation
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (E : ControlEffects K)

include E in
set_option backward.isDefEq.respectTransparency false in
/-- Copying a substitution depends on the permissions of its individual entries,
not the possibly loose aggregate effect annotation. -/
theorem denoteSubstitution_copy (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η)
    (hΓ : Quantity.relevant ≤ Γ.linearity) (hΔ : Quantity.relevant ≤ Δ.linearity) :
    p.orient M.le
      (M.compose (denoteSubstitution M.toSeqData K h) (M.copy (packed Δ) (hΔ.trans (packed_quantity Δ))))
      (M.compose (M.copy (packed Γ) (hΓ.trans (packed_quantity Γ)))
        (M.tensor (denoteSubstitution M.toSeqData K h) (denoteSubstitution M.toSeqData K h))) := by
  induction h with
  | @nil m Γ e hd =>
    have he := M.toSeqData.pure_copy_natural (discard M.toSeqData hd) (discard_pure _ _)
      (hΓ.trans (packed_quantity Γ)) (hΔ.trans (packed_quantity QCtx.nil))
    let := M.toSeqData.homOrder
    cases p with
    | positive => exact he.le
    | negative => exact he.ge
  | @zero m n Γ Δ e σ h a A ih =>
    exact ih hh hΓ (by rw [QCtx.linearity_snoc] at hΔ; exact hΔ.trans inf_le_right)
  | @cons m n Γ Γl Γr Δ e el er σ a A q s h ha hq hc hel her ih =>
    have hΓl := hΓ.trans s.linearity_le_left
    have hΓr := hΓ.trans s.symm.linearity_le_left
    have hΔt : Quantity.relevant ≤ Δ.linearity := by
      rw [QCtx.linearity_snoc] at hΔ
      exact hΔ.trans inf_le_right
    have hA : Quantity.relevant ≤ quantity A := by
      rw [QCtx.linearity_snoc, Usage.linearity_used] at hΔ
      exact hΔ.trans (inf_le_left.trans inf_le_left)
    have hqe : EffectSystem.canCopy p er := by
      rw [QCtx.linearity_snoc, Usage.linearity_used] at hΔ
      exact (hΔ.trans (inf_le_left.trans inf_le_right)).trans hh.2.1
    have hprod : Quantity.relevant ≤ quantity (product (packed Γl) (packed Γr)) := by
      rw [TypeQuantity.product_quantity]
      exact le_inf (hΓl.trans (packed_quantity Γl)) (hΓr.trans (packed_quantity Γr))
    have ht := M.tensor_copy p (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)
      (hΓl.trans (packed_quantity Γl)) (hΔt.trans (packed_quantity Δ))
      (hΓr.trans (packed_quantity Γr)) hA hprod (hΔ.trans (packed_quantity _))
      (ih hh.1 hΓl hΔt)
      (M.toSeqData.copy_naturality p _ (hΓr.trans (packed_quantity Γr)) hA hqe (denote_effect K E ha))
      hc (denoteSubstitution_effect M.toSeqData K E h) (denote_effect K E ha)
    have ht' := M.toSeqData.orient_compose_left p ht (split M.toSeqData s)
    rw [← M.toSeqData.compose_assoc (split M.toSeqData s) (M.copy _ hprod),
      M.toSeqData.pure_copy_natural _ (split_pure _ _) (hΓ.trans (packed_quantity Γ)) hprod,
      M.toSeqData.compose_assoc, M.toSeqData.tensor_comp_pure _ _ _ _ (split_pure _ _)] at ht'
    simpa only [denoteSubstitution_cons, packed_snoc_used, M.toSeqData.compose_assoc] using ht'

end Denotation
end Models
end Silmaril.Isotope.Refinement
