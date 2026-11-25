module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyAssociativity
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Structure
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Category

/-! # Native quantity-sensitive sequential model data

The copy/discard structure uses exactly the directed laws of the written
calculus. In particular it imposes no exchange equality for arbitrary effects
that admit duplication in only one polarity.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} (hR : R.RenamingClosed)

/-- Copy and discard on the literal signature types, with all laws derived. -/
def typeCopyDiscard :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
    letI := typeSymmetric (F := F) (R := R) (ε := ε) hR
    letI := typeHomOrder (F := F) (R := R) (ε := ε) hR
    CopyDiscard τ ε (typeEffects (F := F) (R := R) (ε := ε) hR) quantity := by
  letI := category (ε := ε) F R hR
  letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
  letI := typeSymmetric (F := F) (R := R) (ε := ε) hR
  letI := typeHomOrder (F := F) (R := R) (ε := ε) hR
  exact
    { discard := discard
      copy := copy
      discard_pure := discard_pure
      copy_pure := copy_pure
      copy_assoc := copy_assoc hR
      copy_comm := copy_comm hR
      discard_natural := by
        intro p e A B f hA hB he hf
        exact discard_natural hR p f hf hA hB he
      retained_elimination := by
        intro p e A B f hA hB he hf
        exact retained_elimination hR p f hf hA hB he
      copy_natural := by
        intro p e A B f hA hB he hf
        exact copy_natural hR p f hf hA hB he }

/-- The native category, effects, quantities, and primitive instructions. -/
def seqData : SeqData τ Φ ε where
  category := category (ε := ε) F R hR
  homOrder := typeHomOrder (F := F) (R := R) (ε := ε) hR
  premonoidal := typePremonoidal (F := F) (R := R) (ε := ε) hR
  symmetric := typeSymmetric (F := F) (R := R) (ε := ε) hR
  ordered := typeOrderedPremonoidal (F := F) (R := R) (ε := ε) hR
  tensor_obj _ _ := rfl
  tensor_unit := rfl
  effects := typeEffects (F := F) (R := R) (ε := ε) hR
  copyDiscard := typeCopyDiscard (F := F) (R := R) (ε := ε) hR
  instruction := instruction
  instruction_effect := instruction_effect

end Silmaril.Isotope.Refinement.Models.Syntactic
