module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlSubstitution

/-! # Directed substitution soundness for branching syntax -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Native simultaneous substitution is sound for all branching terms. -/
theorem denoteCase_bsubst_exists (M : CaseModel.{u,v,w,r} τ Φ ε)
    (p : Polarity) {n : Nat} (t : Term Φ n) :
    SubstitutionSoundAt M.toSeqModel (ControlData.case M) p t := by
  refine denote_bsubst_of_iteration M.toSeqModel (ControlData.case M)
    (ControlEffects.case M) (ControlEnvironment.case M) (ControlMonotone.case M) p ?_ t
  intro n a b _ _ Δ η A ht
  cases ht with
  | iter hf _ _ _ _ _ => exact False.elim hf

end Silmaril.Isotope.Refinement.Models.Denotation
