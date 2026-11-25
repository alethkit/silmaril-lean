module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionLookup

/-! # Categorical bridges from simultaneous substitution to ordinary beta -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.SeqData
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Normalize the identity substitution on the retained environment around one initializer. -/
theorem tensor_retract_left {L D R A : τ} (u : M.Hom L D) (w : M.Hom D L)
    (hw : M.hasEffect ⊥ w) (huw : M.compose u w = M.identity L) (a : M.Hom R A) :
    M.compose (M.tensor u a) (M.right w A) = M.left L a := by
  rw [M.tensor_right_after _ _ _ hw, huw, tensor, M.right_identity, M.identity_compose]

/-- A retraction in the substitution environment cancels through its continuation. -/
theorem substitution_retract {G L D A : τ} (z : M.Hom G L) (u : M.Hom L D)
    (w : M.Hom D L) (huw : M.compose u w = M.identity L) (b : M.Hom L A) :
    M.compose (M.compose z u) (M.compose w b) = M.compose z b := by
  rw [M.compose_assoc, ← M.compose_assoc u, huw, M.identity_compose]

end Silmaril.Isotope.Refinement.Models.SeqData

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Deleting a discarded initializer leaves the weakening to the retained context.
Only the initializer's own input must be affine. -/
theorem split_delete_right (p : Polarity) {e : ε} {n : Nat} {Γ Γl Γr : QCtx τ n}
    {A B : τ} (s : Γ.Split Γl Γr) (a : M.Hom (packed Γr) A)
    (b : M.Hom (packed Γl) B) (hr : Γr.Discardable) (hA : Quantity.affine ≤ quantity A)
    (he : EffectSystem.canDelete p e) (ha : M.hasEffect e a) :
    p.orient M.le
      (M.compose (split M.toSeqData s)
        (M.compose (M.left (packed Γl) a)
          (M.compose (M.compose (M.left (packed Γl) (M.discard A hA)) (M.rightUnitor (packed Γl))) b)))
      (M.compose (weaken M.toSeqData (s.weakenLeft hr)) b) := by
  have h := M.toSeqData.orient_compose_left p
    (M.toSeqData.orient_compose_right p
      (M.toSeqData.orient_compose_right p
        (M.toSeqData.orient_left p (packed Γl)
          (M.toSeqData.discard_naturality p a (discardable_quantity hr) hA he ha))
        (M.rightUnitor (packed Γl))) b) (split M.toSeqData s)
  have hp := congrArg (fun k => M.compose k b) (split_weakenLeft M s hr)
  have hp' : M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (M.discard (packed Γr) (discardable_quantity hr)))
        (M.compose (M.rightUnitor (packed Γl)) b)) =
      M.compose (weaken M.toSeqData (s.weakenLeft hr)) b := by
    simpa only [discard, M.toSeqData.compose_assoc] using hp
  simp only [M.toSeqData.compose_assoc] at h
  rw [hp'] at h
  simpa only [M.toSeqData.left_compose, M.toSeqData.compose_assoc] using h

end Silmaril.Isotope.Refinement.Models.Denotation
