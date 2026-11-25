module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyProducts
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.DiscardProducts

/-! # The native categorical sequential model

The hom posets are mutual-refinement quotients of singleton-context terms.
Every sequential-model law is derived from the written quantitative calculus,
including compatibility of copy/discard with both unit and product types.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} (hR : R.RenamingClosed)

@[simp] theorem seqData_identity (A : τ) :
    (seqData (ε := ε) (F := F) hR).identity A = identity (R := R) A := rfl

@[simp] theorem seqData_compose {A B C : τ} (f : Hom (ε := ε) F R A B) (g : Hom (ε := ε) F R B C) :
    (seqData hR).compose f g = compose hR f g := rfl

@[simp] theorem seqData_left (A : τ) {B C : τ} (f : Hom (ε := ε) F R B C) :
    (seqData hR).left A f = left hR A f := by
  change compose hR (identity _) (compose hR (left hR A f) (identity _)) = _
  rw [compose_identity, identity_compose]

@[simp] theorem seqData_right {A B : τ} (f : Hom (ε := ε) F R A B) (C : τ) :
    (seqData hR).right f C = right hR f C := by
  change compose hR (identity _) (compose hR (right hR f C) (identity _)) = _
  rw [compose_identity, identity_compose]

@[simp] theorem seqData_discard (A : τ) (hA : Quantity.affine ≤ quantity A) :
    (seqData (ε := ε) (F := F) hR).discard A hA = discard (R := R) A hA := by
  change compose hR (discard A hA) (identity _) = _
  exact compose_identity hR _

@[simp] theorem seqData_copy (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    (seqData (ε := ε) (F := F) hR).copy A hA = copy (R := R) A hA := by
  change compose hR (copy A hA) (identity _) = _
  exact compose_identity hR _

@[simp] theorem seqData_associator (A B C : τ) :
    (seqData (ε := ε) (F := F) hR).associator A B C = assoc (R := R) A B C := by
  change compose hR (identity _) (compose hR (assoc A B C) (identity _)) = _
  rw [compose_identity, identity_compose]

@[simp] theorem seqData_associatorInv (A B C : τ) :
    (seqData (ε := ε) (F := F) hR).associatorInv A B C = assocInv (R := R) A B C := by
  change compose hR (identity _) (compose hR (assocInv A B C) (identity _)) = _
  rw [compose_identity, identity_compose]

@[simp] theorem seqData_leftUnitor (A : τ) :
    (seqData (ε := ε) (F := F) hR).leftUnitor A = leftUnit (R := R) A := by
  change compose hR (identity _) (leftUnit A) = _
  exact identity_compose hR _

@[simp] theorem seqData_leftUnitorInv (A : τ) :
    (seqData (ε := ε) (F := F) hR).leftUnitorInv A = leftUnitInv (R := R) A := by
  change compose hR (leftUnitInv A) (identity _) = _
  exact compose_identity hR _

@[simp] theorem seqData_rightUnitor (A : τ) :
    (seqData (ε := ε) (F := F) hR).rightUnitor A = rightUnit (R := R) A := by
  change compose hR (identity _) (rightUnit A) = _
  exact identity_compose hR _

@[simp] theorem seqData_rightUnitorInv (A : τ) :
    (seqData (ε := ε) (F := F) hR).rightUnitorInv A = rightUnitInv (R := R) A := by
  change compose hR (rightUnitInv A) (identity _) = _
  exact compose_identity hR _

@[simp] theorem seqData_braiding (A B : τ) :
    (seqData (ε := ε) (F := F) hR).braiding A B = swap (R := R) A B := by
  change compose hR (identity _) (compose hR (swap A B) (identity _)) = _
  rw [compose_identity, identity_compose]

@[simp] theorem seqData_middleSwap (A B C D : τ) :
    (seqData (ε := ε) (F := F) hR).middleSwap A B C D = middleSwap (R := R) A B C D := by
  simp only [SeqData.middleSwap, seqData_associator, seqData_associatorInv,
    seqData_braiding, seqData_left, seqData_right, seqData_compose]
  rfl

/-- The quantitative syntax quotient is a genuine sequential categorical model. -/
def seqModel : SeqModel τ Φ ε := by
  refine { toSeqData := seqData (F := F) (R := R) (ε := ε) hR
           discard_unit := ?_, copy_unit := ?_, discard_product := ?_, copy_product := ?_ }
  · intro h
    rw [seqData_discard, seqData_identity]
    exact discard_unit (F := F) (R := R) (ε := ε) h
  · intro h
    rw [seqData_copy, seqData_leftUnitorInv]
    exact copy_unit (F := F) (R := R) (ε := ε) h
  · intro A B hA hB hAB
    simp only [SeqData.tensor, seqData_discard, seqData_right, seqData_left,
      seqData_compose, seqData_leftUnitor]
    exact discard_product (F := F) (R := R) (ε := ε) hR A B hA hB hAB
  · intro A B hA hB hAB
    simp only [SeqData.tensor, seqData_copy, seqData_right, seqData_left,
      seqData_compose, seqData_middleSwap]
    exact copy_product (F := F) (R := R) (ε := ε) hR A B hA hB hAB

end Silmaril.Isotope.Refinement.Models.Syntactic
