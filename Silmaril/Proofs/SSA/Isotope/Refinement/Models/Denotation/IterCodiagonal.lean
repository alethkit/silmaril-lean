module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationCoaction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterConwaySoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseFold

/-! # Codiagonal for persistent environments and written iteration

Nested contextual loops flatten by the ordinary Conway codiagonal law. The
environment is retained by its actual pure copying coaction, so no equation
about effectful copying is needed.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData.RightCoaction
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- The diagonal makes an unrestricted object its own persistent environment. -/
def diagonal (D : τ) (cD : Quantity.relevant ≤ quantity D)
    (dD : Quantity.affine ≤ quantity D) : M.RightCoaction D D cD dD where
  map := M.copy D cD
  pure := M.copy_pure D cD
  coassoc := M.copy_associator D cD
  counit := by
    have h := congrArg Subtype.val (pure_copy_discard_right M D cD dD)
    change M.compose (M.copy D cD) (M.left D (M.discard D dD)) = M.rightUnitorInv D at h
    rw [← M.compose_assoc, h, M.rightUnitor_inv_hom]

end SeqData.RightCoaction

namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- The contextual iteration operator satisfies the Conway codiagonal law. -/
theorem iterateWithContext_codiagonal {D A B : τ}
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (f : M.Hom (product D A) (coprod (coprod B A) A)) :
    (ControlData.iter M).iterateWithContext trivial D cD dD
        ((ControlData.iter M).iterateWithContext trivial D cD dD f) =
      (ControlData.iter M).iterateWithContext trivial D cD dD
        (M.compose f (M.desc (M.identity (coprod B A)) (M.inr B A))) := by
  let j := SeqData.RightCoaction.diagonal M.toSeqData D cD dD
  let exit : M.Hom (product D (coprod B A)) (coprod B (product D A)) :=
    M.compose (M.distribute D B A)
      (M.desc (M.compose (M.right (M.discard D dD) B)
        (M.compose (M.leftUnitor B) (M.inl B (product D A)))) (M.inr B (product D A)))
  have hi := M.coaction_iterate j f
  have he : M.compose (M.left D (M.desc (M.identity (coprod B A)) (M.inr B A))) exit =
      M.compose (M.distribute D (coprod B A) A) (M.desc exit (M.inr B (product D A))) := by
    apply M.toCaseData.distributed_hom_ext
    · rw [← M.compose_assoc, ← M.left_compose, M.toCaseData.inl_desc,
        M.left_identity, M.identity_compose, ← M.compose_assoc,
        M.toCaseData.left_inl_distribute, M.toCaseData.inl_desc]
    · rw [← M.compose_assoc, ← M.left_compose, M.toCaseData.inr_desc,
        ← M.compose_assoc, M.toCaseData.left_inr_distribute, M.toCaseData.inr_desc]
      dsimp only [exit]
      rw [← M.compose_assoc, M.toCaseData.left_inr_distribute, M.toCaseData.inr_desc]
  have hs (g : M.Hom (product D A) (coprod B A)) :
      (ControlData.iter M).contextStep trivial D cD dD g =
        M.compose (j.action A) (M.compose (M.left D g) exit) := by
    simp only [ControlData.contextStep, ControlData.iter, ControlData.ofCase,
      j, SeqData.RightCoaction.diagonal, SeqData.RightCoaction.action, exit, M.compose_assoc]
  change M.iterate ((ControlData.iter M).contextStep trivial D cD dD
      ((ControlData.iter M).iterateWithContext trivial D cD dD f)) =
    M.iterate ((ControlData.iter M).contextStep trivial D cD dD
      (M.compose f (M.desc (M.identity (coprod B A)) (M.inr B A))))
  rw [hs, hs]
  rw [← M.compose_assoc, hi, M.output_naturality, M.codiagonal]
  apply congrArg M.iterate
  simp only [M.compose_assoc, M.toCaseData.desc_compose, M.toCaseData.inl_desc,
    M.toCaseData.inr_desc, M.compose_identity]
  simp only [M.left_compose, M.compose_assoc]
  rw [he]

end IterModel

namespace Denotation
variable (M : IterModel.{u,v,w,r} τ Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Actual native witnesses of the written codiagonal equation have equal
denotations. Both the initial computation and the loop body retain their effects. -/
theorem denoteIter_codiagonal_exists {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B : τ}
    (s : Γ.Split Γl Γr) (hu : Γl.linearity = ⊤) (hi : EffectSystem.iterable e)
    (ha : HasType .iter Γr e a A)
    (hb : HasType .iter (Γl.snoc A) e b (coprod (coprod B A) A)) :
    ∃ kl : HasType .iter Γ e (.iter a (.iter (.bv 0) b.underBinder)) B,
      ∃ kr : HasType .iter Γ e (.iter a (.case b (.bv 0) (.inr (.bv 0)))) B,
        denoteIter M kl = denoteIter M kr := by
  have ht : (⊤ : Quantity) ≤ quantity (packed Γl) := hu ▸ packed_quantity Γl
  let c : Quantity.relevant ≤ quantity (packed Γl) := le_top.trans ht
  let d : Quantity.affine ≤ quantity (packed Γl) := le_top.trans ht
  obtain ⟨ki, hki⟩ := denote_iterParameter_exists M.toCaseData (fun _ => M.iterate)
    (ControlEnvironment.iter M) trivial hu hi hb c d
  obtain ⟨kf, hkf⟩ := denote_codiagonalBody_exists M.toCaseData (F := .iter) (fun _ => M.iterate) trivial hb
  refine ⟨.iter trivial s hu hi ha ki, .iter trivial s hu hi ha kf, ?_⟩
  change denoteIter M ki =
    (ControlData.iter M).iterateWithContext trivial (packed Γl) c d (denoteIter M hb) at hki
  change denoteIter M kf =
    M.compose (denoteIter M hb) (M.desc (M.identity (coprod B A)) (M.inr B A)) at hkf
  change M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (denoteIter M ha))
        ((ControlData.iter M).iterateWithContext trivial (packed Γl) c d (denoteIter M ki))) =
    M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (denoteIter M ha))
        ((ControlData.iter M).iterateWithContext trivial (packed Γl) c d (denoteIter M kf)))
  rw [hki, hkf, M.iterateWithContext_codiagonal]

variable {α : Type u} [HasQuantity α] [HasTy Φ (Ty α)]

/-- The written codiagonal equation is sound for every pair of endpoint
derivations over free types, using the proved witness-coherence theorem. -/
theorem denoteIter_codiagonal (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {n : Nat} {Γ Γl Γr : QCtx (Ty α) n} {e e₁ e₂ : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B : Ty α}
    (s : Γ.Split Γl Γr) (hu : Γl.linearity = ⊤) (hi : EffectSystem.iterable e)
    (ha : HasType .iter Γr e a A)
    (hb : HasType .iter (Γl.snoc A) e b (coprod (coprod B A) A))
    (hl : HasType .iter Γ e₁ (.iter a (.iter (.bv 0) b.underBinder)) B)
    (hr : HasType .iter Γ e₂ (.iter a (.case b (.bv 0) (.inr (.bv 0)))) B) :
    denoteIter M hl = denoteIter M hr := by
  obtain ⟨kl, kr, h⟩ := denoteIter_codiagonal_exists M s hu hi ha hb
  exact (denoteIter_coherent M hl kl).trans (h.trans (denoteIter_coherent M kr hr))

end Denotation
end Silmaril.Isotope.Refinement.Models
