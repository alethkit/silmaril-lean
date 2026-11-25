module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterSoundness
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationEquations

/-! # Soundness of written Conway equations for contextual iteration -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- The written fixpoint equation is the first-step equation of the explicit
loop machine, with native resource splitting and actual endpoint typing. -/
theorem denoteIter_fixpoint_exists {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B : τ}
    (s : Γ.Split Γl Γr) (hu : Γl.linearity = ⊤) (hi : EffectSystem.iterable e)
    (ha : HasType .iter Γr e a A) (hb : HasType .iter (Γl.snoc A) e b (coprod B A)) :
    ∃ k : HasType .iter Γ e
        (.let₁ a (.case b (.bv 0) (.iter (.bv 0) b.underBinder.underBinder))) B,
      denoteIter M (.iter trivial s hu hi ha hb) = denoteIter M k := by
  have hcopy : Quantity.relevant ≤ Γl.linearity := hu ▸ le_top
  have hui : (Γl.snoc A .zero).linearity = ⊤ := by
    simp only [QCtx.linearity_snoc, Usage.linearity_zero, hu, inf_top_eq]
    rfl
  have hdisci : (Γl.snoc A .zero).Discardable :=
    QCtx.discardable_iff_linearity.mpr (hui ▸ le_top)
  have ht : (⊤ : Quantity) ≤ quantity (packed Γl) := hu ▸ packed_quantity Γl
  let c : Quantity.relevant ≤ quantity (packed Γl) := le_top.trans ht
  let d : Quantity.affine ≤ quantity (packed Γl) := le_top.trans ht
  obtain ⟨kb, hkb⟩ := denote_underBinder_zero_exists M.toCaseData (fun _ => M.iterate)
    (ControlEnvironment.iter M) (A := A) hb
  obtain ⟨kr, hkr⟩ := denote_iterParameter_exists M.toCaseData (fun _ => M.iterate)
    (ControlEnvironment.iter M) trivial hui hi kb c d
  change denoteIter M kb = denoteIter M hb at hkb
  change denoteIter M kr = (ControlData.iter M).iterateWithContext trivial (packed Γl) c d (denoteIter M kb) at hkr
  let kl : HasType .iter ((Γl.snoc A .zero).snoc B) e (.bv 0 : Term Φ (n+2)) B :=
    .var 0 (QCtx.varAllowed_snoc hdisci B)
  let si := (QCtx.Split.diagonal Γl hcopy).snoc (.right (.used ⊤)) (A := A)
  let ki := HasType.case (F := .iter) trivial si hb kl kr
  refine ⟨.let₁ s ha ki, ?_⟩
  have hk : denoteIter M ki = (ControlData.iter M).iterateWithContext trivial (packed Γl) c d (denoteIter M hb) := by
    change M.compose
      (M.compose (M.right (split M.toSeqData (QCtx.Split.diagonal Γl hcopy)) A)
        (M.associator (packed Γl) (packed Γl) A))
      (M.compose (M.left (packed Γl) (denoteIter M hb))
        (M.compose (M.distribute (packed Γl) B A)
          (M.desc (M.compose (M.right (discard M.toSeqData hdisci) B) (M.leftUnitor B))
            (denoteIter M kr)))) = _
    rw [hkr, hkb, split_diagonal M.toSeqModel Γl hcopy]
    simpa only [M.compose_assoc, discard, packed_snoc_zero] using (M.iterateWithContext_fixpoint c d (A := A) (denoteIter M hb)).symm
  change M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (denoteIter M ha)) _) =
    M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (denoteIter M ha)) (denoteIter M ki))
  rw [hk]
  rfl

end Silmaril.Isotope.Refinement.Models.Denotation
