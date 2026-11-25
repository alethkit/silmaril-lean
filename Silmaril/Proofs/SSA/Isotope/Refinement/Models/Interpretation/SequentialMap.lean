module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Tensor
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SeqModel

/-! # Preservation of the native sequential quotient operations -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)
variable (h : Sound M.toSeqData K R)

theorem map_identity (A : τ) :
    map M.toSeqData K h (Syntactic.identity A) = M.identity A :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.identityDeriv A (⊤ : ε))).trans
    (denoteArrow_identityDeriv M K A ⊤)

theorem map_instruction (f : Φ) :
    map M.toSeqData K h (Syntactic.instruction f) = M.instruction f :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.instructionDeriv f)).trans
    (denoteArrow_instructionDeriv M K f)

theorem map_discard (A : τ) (hA : Quantity.affine ≤ quantity A) :
    map M.toSeqData K h (Syntactic.discard A hA) = M.discard A hA :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.discardDeriv A hA (⊤ : ε))).trans
    (denoteArrow_discardDeriv M K A hA ⊤)

theorem map_copy (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    map M.toSeqData K h (Syntactic.copy A hA) = M.copy A hA :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.copyDeriv A hA (⊤ : ε))).trans
    (denoteArrow_copyDeriv M K A hA ⊤)

variable (hR : R.RenamingClosed) (N : ControlEnvironment K)
include N

theorem map_compose {A B C : τ}
    (a : Syntactic.Hom (ε := ε) F R A B) (b : Syntactic.Hom (ε := ε) F R B C) :
    map M.toSeqData K h (Syntactic.compose hR a b) =
      M.compose (map M.toSeqData K h a) (map M.toSeqData K h b) := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    obtain ⟨da⟩ := a.property
    obtain ⟨db⟩ := b.property
    exact (map_ofArrow M.toSeqData K h (Syntactic.composeArrow a b) (Syntactic.composeDeriv da db)).trans
      ((denoteArrow_composeDeriv M K N (Sound.coherent M.toSeqData K h) da db).trans
        (congrArg₂ M.compose (map_ofArrow M.toSeqData K h a da).symm
          (map_ofArrow M.toSeqData K h b db).symm))

theorem map_left (A : τ) {B C : τ} (a : Syntactic.Hom (ε := ε) F R B C) :
    map M.toSeqData K h (Syntactic.left hR A a) = M.left A (map M.toSeqData K h a) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨da⟩ := a.property
    exact (map_ofArrow M.toSeqData K h (Syntactic.leftArrow A a) (Syntactic.leftDeriv A da)).trans
      ((denoteArrow_leftDeriv M K N (Sound.coherent M.toSeqData K h) A da).trans
        (congrArg (M.left A) (map_ofArrow M.toSeqData K h a da).symm))

theorem map_right {A B : τ} (a : Syntactic.Hom (ε := ε) F R A B) (C : τ) :
    map M.toSeqData K h (Syntactic.right hR a C) = M.right (map M.toSeqData K h a) C := by
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨da⟩ := a.property
    exact (map_ofArrow M.toSeqData K h (Syntactic.rightArrow a C) (Syntactic.rightDeriv C da)).trans
      ((denoteArrow_rightDeriv M K N (Sound.coherent M.toSeqData K h) C da).trans
        (congrArg (fun f => M.right f C) (map_ofArrow M.toSeqData K h a da).symm))

/-- The quotient interpretation is an actual functor on the native categories. -/
def functor : Syntactic.Object ε F R hR ⥤ M.toSeqData.Object where
  obj A := ⟨A.type⟩
  map := map M.toSeqData K h
  map_id A := map_identity M K h A.type
  map_comp := map_compose M K h hR N

end Silmaril.Isotope.Refinement.Models.Interpretation
