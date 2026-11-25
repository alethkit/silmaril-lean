module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Beta
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseSubstitution
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence

/-! # Actual directed beta soundness for branching syntax -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)

/-- The written beta rule is sound for arbitrary typing witnesses of its endpoints. -/
theorem denoteCase_beta (p : Polarity) {n : Nat} {Γ Γl Γr : QCtx (Ty α) n}
    {e η eL eR : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : Ty α} {q : Usage}
    (s : Γ.Split Γl Γr) (ha : HasType .case Γl e a A)
    (hb : HasType .case (Γr.snoc A q) η b B)
    (hd : HasType .case (Γr.snoc A) η b B)
    (hm : EffectSystem.moves p e η)
    (hq : q ≤ Usage.used (Γl.linearity ⊓ EffectSystem.quantity p e))
    (hl : HasType .case Γ eL (.let₁ a b) B)
    (hr : HasType .case Γ eR (Tm.instantiate b a) B) :
    p.orient M.le (denoteCase M hl) (denoteCase M hr) :=
  Sequential.denote_beta M.toSeqModel (ControlData.case M) (ControlEffects.case M)
    (ControlEnvironment.case M) (Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M) p (denoteCase_bsubst_exists M p)
    s ha hb hd hm hq hl hr

end Silmaril.Isotope.Refinement.Models.Denotation
