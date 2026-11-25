module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.StructureMap

/-! # The categorical interpretation morphism

A soundness theorem descends the constructor interpretation to the native
refinement quotient. Every preservation law of the actual model morphism is
proved from its representatives and the existing categorical model laws.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
universe u w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The shared sequential part of quotient interpretation for any fragment. -/
def seqDataMap (M : SeqModel.{u,w,w,r} τ Φ ε) (K : ControlData M.toSeqData F)
    (h : Sound M.toSeqData K R) (hR : R.RenamingClosed)
    (N : ControlEnvironment K) (E : ControlEffects K) :
    SeqData.HomMap (Syntactic.seqData (ε := ε) (F := F) (R := R) hR) M.toSeqData where
  map := map M.toSeqData K h
  monotone := map_monotone M.toSeqData K h
  effect := map_effect M.toSeqData K h E
  identity A := by
    simpa only [Syntactic.seqData_identity] using map_identity M K h A
  compose a b := map_compose M K h hR N a b
  left A {_ _} f :=
    (congrArg (map M.toSeqData K h) (Syntactic.seqData_left (ε := ε) (F := F) (R := R) hR A f)).trans
      (map_left M K h hR N A f)
  right f A :=
    (congrArg (map M.toSeqData K h) (Syntactic.seqData_right (ε := ε) (F := F) (R := R) hR f A)).trans
      (map_right M K h hR N f A)
  associator A B C := by
    simpa only [Syntactic.seqData_associator] using map_associator M K h A B C
  associatorInv A B C := by
    simpa only [Syntactic.seqData_associatorInv] using map_associatorInv M K h A B C
  leftUnitor A := by
    simpa only [Syntactic.seqData_leftUnitor] using map_leftUnitor M K h A
  leftUnitorInv A := by
    simpa only [Syntactic.seqData_leftUnitorInv] using map_leftUnitorInv M K h A
  rightUnitor A := by
    simpa only [Syntactic.seqData_rightUnitor] using map_rightUnitor M K h A
  rightUnitorInv A := by
    simpa only [Syntactic.seqData_rightUnitorInv] using map_rightUnitorInv M K h A
  braiding A B := by
    simpa only [Syntactic.seqData_braiding] using map_braiding M K h A B
  discard A hA := by
    simpa only [Syntactic.seqData_discard] using map_discard M K h A hA
  copy A hA := by
    simpa only [Syntactic.seqData_copy] using map_copy M K h A hA
  instruction := map_instruction M K h

/-- A genuine map of sequential categorical models, given proved native soundness. -/
def seqModelMap (M : SeqModel.{u,w,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.seq M) R) (hR : R.RenamingClosed) :
    Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR ⟶ M :=
  seqDataMap M (ControlData.seq M) h hR (ControlEnvironment.seq M) (ControlEffects.seq M)

@[simp] theorem seqModelMap_of_typing (M : SeqModel.{u,w,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.seq M) R) (hR : R.RenamingClosed)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .seq (Syntactic.input A) e t B) :
    (seqModelMap M h hR).map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteSeq M d) :=
  map_of_typing M.toSeqData (ControlData.seq M) h d

end Silmaril.Isotope.Refinement.Models.Interpretation
