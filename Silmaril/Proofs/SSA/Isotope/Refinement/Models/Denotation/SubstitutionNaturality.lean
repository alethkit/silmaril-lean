module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.SubstitutionAdmissibility
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Directed

/-! # Directed resource naturality of quantitative substitutions -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.SeqData

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem orient_trans (p : Polarity) {A B : τ} {f g h : M.Hom A B}
    (hfg : p.orient M.le f g) (hgh : p.orient M.le g h) : p.orient M.le f h := by
  let := M.homOrder
  cases p with
  | positive => exact le_trans hfg hgh
  | negative => exact le_trans hgh hfg

theorem orient_tensor (p : Polarity) {A B D E : τ}
    {f f' : M.Hom A B} {g g' : M.Hom D E}
    (hf : p.orient M.le f f') (hg : p.orient M.le g g') :
    p.orient M.le (M.tensor f g) (M.tensor f' g') := by
  cases p <;> exact M.tensor_mono hf hg

/-- Commuting effect bounds give exact interchange. -/
theorem exchange_commutes {e η : ε} {A B D E : τ}
    (f : M.Hom A B) (g : M.Hom D E) (hm : EffectSystem.commutes e η)
    (hf : M.hasEffect e f) (hg : M.hasEffect η g) :
    M.compose (M.right f D) (M.left B g) =
      M.compose (M.left A g) (M.right f E) := by
  let := M.homOrder
  exact le_antisymm (M.exchange .positive f g hm.1 hf hg)
    (M.exchange .negative f g hm.2 hf hg)

end Silmaril.Isotope.Refinement.Models.SeqData

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (E : ControlEffects K)

include E in
/-- Discarding the destination of an allowed substitution deletes precisely its
retained computations; its zero slots never introduce a computation. -/
theorem denoteSubstitution_discard (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) (hd : Δ.Discardable) :
    p.orient M.le
      (M.compose (denoteSubstitution M.toSeqData K h) (discard M.toSeqData hd))
      (discard M.toSeqData (h.discardable hd)) := by
  induction h with
  | nil hd' =>
    have hI : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
      rw [TypeQuantity.unit_quantity]
      exact le_top
    change p.orient M.le
      (M.compose (discard M.toSeqData hd') (M.discard Silmaril.unit hI))
      (discard M.toSeqData hd')
    rw [M.discard_unit, M.toSeqData.compose_identity]
    cases p <;> exact M.toSeqData.le_refl _
  | zero h a A ih => exact ih hh (fun i => hd i.succ)
  | @cons m n Γ Γl Γr Δ e el er σ a A q s h ha hq hc hl hr ih =>
    have hΔ : Δ.Discardable := fun i => hd i.succ
    have hqa : Quantity.affine ≤ q ⊓ quantity A := (Usage.zero_le_used _).mp (hd 0)
    have hA : Quantity.affine ≤ quantity A := hqa.trans inf_le_right
    have hΓr : Quantity.affine ≤ quantity (packed Γr) :=
      ((hqa.trans inf_le_left).trans hq).trans (packed_quantity Γr)
    have hΓl := discardable_quantity (h.discardable hΔ)
    have hsrc : Quantity.affine ≤ quantity (product (packed Γl) (packed Γr)) := by
      rw [TypeQuantity.product_quantity]
      exact le_inf hΓl hΓr
    have hdst := discardable_quantity hd
    have hdelete : EffectSystem.canDelete p er := (hqa.trans inf_le_left).trans hh.2.1
    have hstep := M.toSeqData.orient_tensor p (ih hh.1 hΔ)
      (M.toSeqData.discard_naturality p (denote M.toSeqData K ha) hΓr hA hdelete
        (denote_effect K E ha))
    have hfinal := M.toSeqData.orient_compose_left p
      (M.toSeqData.orient_compose_right p hstep (M.leftUnitor Silmaril.unit)) (split M.toSeqData s)
    have hsplit := M.toSeqData.pure_discard_natural (split M.toSeqData s)
      (split_pure M.toSeqData s) (discardable_quantity ((Substitution.cons s h ha hq hc hl hr).discardable hd)) hsrc
    rw [M.discard_product _ _ hΓl hΓr hsrc] at hsplit
    change p.orient M.le
      (M.compose (M.compose (split M.toSeqData s)
        (M.tensor (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)))
        (M.discard (product (packed Δ) A) hdst)) _
    rw [M.discard_product _ _ (discardable_quantity hΔ) hA hdst]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.tensor _ _),
      M.toSeqData.tensor_comp_pure_middle _ _ _ _ (M.toSeqData.discard_pure (packed Δ) (discardable_quantity hΔ))]
    change p.orient M.le _ (M.discard (packed Γ) _)
    rw [← hsplit]
    simpa only [discard] using hfinal

end Silmaril.Isotope.Refinement.Models.Denotation
