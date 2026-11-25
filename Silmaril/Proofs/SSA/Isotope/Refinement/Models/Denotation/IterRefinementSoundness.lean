module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.RefinementSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterEquationSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterBeta
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseEquationSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterUniformitySoundness

/-! # Full categorical soundness of the written iteration refinement calculus -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Every written iterative directed axiom respects the given quantities,
effect mover, and endpoint derivations. -/
theorem denoteIter_directional (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    (p : Polarity) {n : Nat} {Γ : QCtx (Ty α) n} {a b : Term Φ n} {A : Ty α}
    {e η : ε} (h : DirectionalAxiom (ε := ε) .iter p Γ a b A)
    (ha : HasType .iter Γ e a A) (hb : HasType .iter Γ η b A) :
    p.orient M.le (denoteIter M ha) (denoteIter M hb) := by
  cases h with
  | eliminate s hd hq he => exact denoteIter_eliminate M p s hd hq he ha hb
  | beta s hd he hf hm hq => exact denoteIter_beta M p s hd he hf hm hq ha hb

/-- An iterative categorical model validating the primitive presentation
validates the entire written native refinement calculus. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.iter_validates_refines (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {R : Relation (Ty α) Φ} (hR : Validates M.toSeqData (ControlData.iter M) R) :
    Validates M.toSeqData (ControlData.iter M) (Refines (ε := ε) .iter R) := by
  refine validates_refines M.toSeqModel (ControlData.iter M) (ControlMonotone.iter M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) (denoteIter_equation M)
    (fun p h ha hb => denoteIter_directional M p h ha hb) ?_ hR
  intro n m Γ Δ a b c d A B p h ha hb hc hd hs
  exact denoteIter_uniformity M p h ha hb hc hd hs

end Silmaril.Isotope.Refinement.Models.Denotation
