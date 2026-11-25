module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.SequentialMap
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Associator

/-! # Preservation of chosen coherence on the native quotient -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)
variable (h : Sound M.toSeqData K R)

theorem map_leftUnitor (A : τ) :
    map M.toSeqData K h (Syntactic.leftUnit A) = M.leftUnitor A :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.leftUnitDeriv A (⊤ : ε))).trans
    (denoteArrow_leftUnitDeriv M K A ⊤)

theorem map_leftUnitorInv (A : τ) :
    map M.toSeqData K h (Syntactic.leftUnitInv A) = M.leftUnitorInv A :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.leftUnitInvDeriv A (⊤ : ε))).trans
    (denoteArrow_leftUnitInvDeriv M K A ⊤)

theorem map_rightUnitor (A : τ) :
    map M.toSeqData K h (Syntactic.rightUnit A) = M.rightUnitor A :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.rightUnitDeriv A (⊤ : ε))).trans
    (denoteArrow_rightUnitDeriv M K A ⊤)

theorem map_rightUnitorInv (A : τ) :
    map M.toSeqData K h (Syntactic.rightUnitInv A) = M.rightUnitorInv A :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.rightUnitInvDeriv A (⊤ : ε))).trans
    (denoteArrow_rightUnitInvDeriv M K A ⊤)

theorem map_braiding (A B : τ) :
    map M.toSeqData K h (Syntactic.swap A B) = M.braiding A B :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.swapDeriv A B (⊤ : ε))).trans
    (denoteArrow_swapDeriv M K A B ⊤)

theorem map_associator (A B C : τ) :
    map M.toSeqData K h (Syntactic.assoc A B C) = M.associator A B C :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.assocDeriv A B C (⊤ : ε))).trans
    (denoteArrow_assocDeriv M K A B C ⊤)

theorem map_associatorInv (A B C : τ) :
    map M.toSeqData K h (Syntactic.assocInv A B C) = M.associatorInv A B C :=
  (map_ofArrow M.toSeqData K h _ (Syntactic.assocInvDeriv A B C (⊤ : ε))).trans
    (denoteArrow_assocInvDeriv M K A B C ⊤)

end Silmaril.Isotope.Refinement.Models.Interpretation
