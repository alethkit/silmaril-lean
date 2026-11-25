module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlSubstitution
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionCopy
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterationDirectedEnvironment

/-! # Directed quantitative substitution through iteration -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Iteration preserves substitution soundness. The persistent source environment
is unrestricted, and its entries are duplicated using their individual allowances. -/
theorem denoteIter_bsubst_loop (p : Polarity) {n : Nat}
    (a : Term Φ n) (b : Term Φ (n + 1))
    (iha : SubstitutionSoundAt M.toSeqModel (ControlData.iter M) p a)
    (ihb : SubstitutionSoundAt M.toSeqModel (ControlData.iter M) p b) :
    SubstitutionSoundAt M.toSeqModel (ControlData.iter M) p (.iter a b) := by
  intro Δ η B ht m Γ e σ hs hh hm
  cases ht with
  | @iter n Δ Δl Δr η a b A B hf sd hu hi ha hb =>
    obtain ⟨Γr, Γl, sg, sr, sl, hr, hl, hlin, he⟩ :=
      denoteSubstitution_split_right_exists M.toSeqModel (ControlData.iter M) (ControlEffects.iter M)
        p hs hh sd.symm
    have hΓu : Γl.linearity = ⊤ := top_unique (hu ▸ hlin)
    have hΓc : Quantity.relevant ≤ Γl.linearity := hΓu ▸ le_top
    have hΓd : Quantity.affine ≤ Γl.linearity := hΓu ▸ le_top
    have hΔc : Quantity.relevant ≤ Δl.linearity := hu ▸ le_top
    have hΔd : Quantity.affine ≤ Δl.linearity := hu ▸ le_top
    obtain ⟨ka, hea⟩ := iha ha sr hr hm
    obtain ⟨hbn, hbnEq⟩ := denote_normalizeBinder_exists M.toSeqModel (ControlData.iter M)
      (ControlEnvironment.iter M) hb
    obtain ⟨su, huS, hue⟩ := denoteSubstitution_up_exists M.toSeqModel (ControlData.iter M)
      (ControlEnvironment.iter M) p sl hl A
    obtain ⟨kb, heb⟩ := ihb hbn su huS hm
    have hebody : M.compose (denoteSubstitution M.toSeqData (ControlData.iter M) su) (denoteIter M hbn) =
        M.compose (M.right (denoteSubstitution M.toSeqData (ControlData.iter M) sl) A) (denoteIter M hb) :=
      congrArg₂ (fun (f : M.Hom (product (packed Γl) A) (product (packed Δl) A))
        (g : M.Hom (product (packed Δl) A) (coprod B A)) => M.compose f g) hue hbnEq
    replace heb := (congrArg (fun f => p.orient M.le f (denoteIter M kb)) hebody).mp heb
    refine ⟨.iter hf sg.symm hΓu (EffectSystem.iterable_sup_right e hi) ka kb, ?_⟩
    have hc := denoteSubstitution_copy M.toSeqModel (ControlData.iter M) (ControlEffects.iter M)
      p sl hl hΓc hΔc
    have hd := denoteSubstitution_discard M.toSeqModel (ControlData.iter M) (ControlEffects.iter M)
      p sl hl (QCtx.discardable_iff_linearity.mpr hΔd)
    have hloop := M.iterateWithContext_directed_environment p
      (denoteSubstitution M.toSeqData (ControlData.iter M) sl) (denoteIter M hb) (denoteIter M kb)
      (hΓc.trans (packed_quantity Γl)) (hΓd.trans (packed_quantity Γl))
      (hΔc.trans (packed_quantity Δl)) (hΔd.trans (packed_quantity Δl))
      hi (denoteSubstitution_effect M.toSeqData (ControlData.iter M) (ControlEffects.iter M) sl)
      (denoteIter_effect M hb) hm hc hd heb
    let bsem : M.Hom (product (packed Δl) A) B :=
      (ControlData.iter M).iterateWithContext hf (packed Δl)
        (hΔc.trans (packed_quantity Δl)) (hΔd.trans (packed_quantity Δl)) (denoteIter M hb)
    have h1 := M.toSeqData.orient_compose_right p he
      (M.compose (M.braiding (packed Δr) (packed Δl))
        (M.compose (M.left (packed Δl) (denoteIter M ha)) bsem))
    simp only [M.compose_assoc] at h1
    rw [← M.compose_assoc (split M.toSeqData sd.symm), split_symm] at h1
    have h2 := M.toSeqData.orient_compose_left p
      (M.toSeqData.tensor_bind_mover p
        (denoteSubstitution M.toSeqData (ControlData.iter M) sr)
        (denoteSubstitution M.toSeqData (ControlData.iter M) sl)
        (denoteIter M ha) bsem hm
        (denoteSubstitution_effect M.toSeqData (ControlData.iter M) (ControlEffects.iter M) sl)
        (denoteIter_effect M ha)) (split M.toSeqData sg)
    rw [← M.compose_assoc (split M.toSeqData sg) (M.braiding (packed Γr) (packed Γl)), split_symm] at h2
    have h3 := M.toSeqData.orient_compose_left p
      (M.toSeqData.orient_compose p (M.toSeqData.orient_left p (packed Γl) hea) hloop)
      (split M.toSeqData sg.symm)
    exact M.toSeqData.orient_trans p h1 (M.toSeqData.orient_trans p h2 h3)

/-- Native simultaneous substitution is sound for every iteration term. -/
theorem denoteIter_bsubst_exists (p : Polarity) {n : Nat} (t : Term Φ n) :
    SubstitutionSoundAt M.toSeqModel (ControlData.iter M) p t :=
  denote_bsubst_of_iteration M.toSeqModel (ControlData.iter M)
    (ControlEffects.iter M) (ControlEnvironment.iter M) (ControlMonotone.iter M) p
    (denoteIter_bsubst_loop M p) t

end Silmaril.Isotope.Refinement.Models.Denotation
