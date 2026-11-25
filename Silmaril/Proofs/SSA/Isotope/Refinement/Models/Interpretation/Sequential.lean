module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Basic
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Binding

/-! # Sequential operations on interpreted representatives -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)

theorem denote_identityDeriv (A : τ) (e : ε) :
    Denotation.denote M.toSeqData K (Syntactic.identityDeriv (F := F) A e) = M.leftUnitor A := by
  have hu : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]; exact le_top
  change M.compose (M.right (M.discard Silmaril.unit hu) A) (M.leftUnitor A) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.identity_compose]

theorem denoteArrow_identityDeriv (A : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.identityDeriv (F := F) A e) = M.identity A := by
  rw [denoteArrow, denote_identityDeriv, M.toSeqData.leftUnitor_inv_hom]

theorem denoteArrow_instructionDeriv (f : Φ) :
    denoteArrow M.toSeqData K (Syntactic.instructionDeriv (F := F) (ε := ε) f) = M.instruction f := by
  change M.compose (M.leftUnitorInv (instrSrc f))
    (M.compose (Denotation.denote M.toSeqData K (Syntactic.identityDeriv _ _)) (M.instruction f)) = _
  rw [denote_identityDeriv]
  change M.compose (M.leftUnitorInv (instrSrc f))
    (M.compose (M.leftUnitor (instrSrc f)) (M.instruction f)) = _
  rw [← M.compose_assoc, M.toSeqData.leftUnitor_inv_hom, M.identity_compose]

theorem denoteArrow_discardDeriv (A : τ) (hA : Quantity.affine ≤ quantity A) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.discardDeriv (F := F) A hA e) = M.discard A hA := by
  exact M.toSeqData.pure_discard_natural (M.leftUnitorInv A) (M.toSeqData.leftUnitorInv_pure A) _ _

theorem denoteArrow_copyDeriv (A : τ) (hA : Quantity.relevant ≤ quantity A) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.copyDeriv (F := F) A hA e) = M.copy A hA := by
  have hr : Quantity.relevant ≤ (Syntactic.input A).linearity := by
    simpa only [Syntactic.input_linearity] using hA
  change M.compose (M.leftUnitorInv A)
    (M.compose (split M.toSeqData (QCtx.Split.diagonal (Syntactic.input A) hr))
      (M.tensor (Denotation.denote M.toSeqData K (Syntactic.identityDeriv A e))
        (Denotation.denote M.toSeqData K (Syntactic.identityDeriv A e)))) = _
  rw [denote_identityDeriv, split_diagonal M _ hr]
  have hp : Quantity.relevant ≤ quantity (product Silmaril.unit A) := by
    simpa only [TypeQuantity.product_quantity, TypeQuantity.unit_quantity, top_inf_eq] using hA
  change M.compose (M.leftUnitorInv A)
    (M.compose (M.copy (product Silmaril.unit A) hp)
      (M.tensor (M.leftUnitor A) (M.leftUnitor A))) = _
  rw [← M.toSeqData.pure_copy_natural (M.leftUnitor A) (M.toSeqData.leftUnitor_pure A) _ hA]
  rw [← M.compose_assoc, M.toSeqData.leftUnitor_inv_hom, M.identity_compose]

variable (N : ControlEnvironment K) (H : WitnessCoherent M K)
include N H

theorem denote_continuation {A B C : τ} {e : ε} {b : Term Φ 1}
    (hb : HasType F (Syntactic.input B) e b C) :
    Denotation.denote M.toSeqData K
      (hb.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B)) =
        Denotation.denote M.toSeqData K hb := by
  have hu : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]; exact le_top
  have hw : weaken M.toSeqData ((QCtx.Weakening.insertZero QCtx.nil A).up B) =
      M.identity (product Silmaril.unit B) := by
    change M.right (M.discard Silmaril.unit hu) B = _
    rw [M.discard_unit, M.toSeqData.right_identity]
  have hd := denote_rename_of_typing M K N H hb _
    ((QCtx.Weakening.insertZero QCtx.nil A).up B)
    (hb.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B))
  exact hd.trans ((congrArg (fun f : M.Hom (product Silmaril.unit B) (product Silmaril.unit B) =>
    M.compose f (Denotation.denote M.toSeqData K hb)) hw).trans (M.identity_compose _))

theorem denoteArrow_composeDeriv {A B C : τ} {e : ε} {a b : Term Φ 1}
    (ha : HasType F (Syntactic.input A) e a B) (hb : HasType F (Syntactic.input B) e b C) :
    denoteArrow M.toSeqData K (Syntactic.composeDeriv ha hb) =
      M.compose (denoteArrow M.toSeqData K ha) (denoteArrow M.toSeqData K hb) := by
  have hs : split M.toSeqData (Syntactic.inputSplit A) =
      M.leftUnitorInv (product Silmaril.unit A) :=
    eq_of_heq (split_zero_left M.toSeqData (Syntactic.input A))
  change M.compose (M.leftUnitorInv A)
    (M.compose (split M.toSeqData (Syntactic.inputSplit A))
      (M.compose (M.left Silmaril.unit (Denotation.denote M.toSeqData K ha))
        (Denotation.denote M.toSeqData K
          (hb.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B))))) = _
  rw [denote_continuation M K N H, hs]
  let da : M.Hom (product Silmaril.unit A) B := Denotation.denote M.toSeqData K ha
  let db : M.Hom (product Silmaril.unit B) C := Denotation.denote M.toSeqData K hb
  change M.compose (M.leftUnitorInv A)
    (M.compose (M.leftUnitorInv (product Silmaril.unit A))
      (M.compose (M.left Silmaril.unit da) db)) =
        M.compose (M.compose (M.leftUnitorInv A) da) (M.compose (M.leftUnitorInv B) db)
  have hu := congrArg (fun f => M.compose f (M.leftUnitorInv B)) (M.toSeqData.unit_bind da)
  simp only [M.compose_assoc, M.toSeqData.leftUnitor_hom_inv, M.compose_identity] at hu
  rw [← M.compose_assoc (M.leftUnitorInv (product Silmaril.unit A)), hu]
  simp only [M.compose_assoc]

end Silmaril.Isotope.Refinement.Models.Interpretation
