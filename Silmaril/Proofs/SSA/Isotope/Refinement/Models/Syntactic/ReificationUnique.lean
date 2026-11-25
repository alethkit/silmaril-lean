module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Reification
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Naturality

/-! # Uniqueness of interpretation from the native sequential model

A map preserving the actual categorical structure is determined on every
syntactic arrow by interpretation. This uses native reification and naturality,
not a generation assumption on model objects or a definition of maps as lifts.
Existence of interpretation requires the separate soundness theorem for the
chosen primitive relation.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open CategoryTheory Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation τ Φ}

/-- Every structure-preserving model map agrees with interpretation on an
arbitrary typed representative. The initial unit is removed explicitly. -/
theorem modelMap_ofArrow (hR : R.RenamingClosed)
    {M : SeqModel.{u,v,v,w} τ Φ ε}
    (φ : seqModel (ε := ε) (F := .seq) (R := R) hR ⟶ M)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .seq (input A) e t B) :
    φ.map (ofArrow (R := R) ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteSeq M d) := by
  have hu := φ.leftUnitorInv A
  change φ.map ((seqData (ε := ε) (F := .seq) (R := R) hR).leftUnitorInv A) = _ at hu
  rw [seqData_leftUnitorInv (ε := ε) (F := .seq) (R := R) hR A] at hu
  calc
    _ = φ.map (compose (ε := ε) (F := .seq) (R := R) hR (leftUnitInv A)
        (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d)) :=
      congrArg φ.map (denoteSeq_reify (R := R) hR d).symm
    _ = M.compose (φ.map (leftUnitInv A))
        (φ.map (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d)) :=
      φ.compose (leftUnitInv A) (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d)
    _ = _ := congrArg₂ M.compose hu (denoteSeq_naturality φ d)

/-- Maps from the native sequential model are unique because their values on
all quotient representatives are fixed by the categorical operations. -/
theorem modelMap_unique (hR : R.RenamingClosed)
    {M : SeqModel.{u,v,v,w} τ Φ ε}
    (φ ψ : seqModel (ε := ε) (F := .seq) (R := R) hR ⟶ M) : φ = ψ := by
  apply SeqData.HomMap.ext
  intro A B a
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨d⟩ := a.property
    exact (modelMap_ofArrow hR φ d).trans (modelMap_ofArrow hR ψ d).symm

end Silmaril.Isotope.Refinement.Models.Syntactic
