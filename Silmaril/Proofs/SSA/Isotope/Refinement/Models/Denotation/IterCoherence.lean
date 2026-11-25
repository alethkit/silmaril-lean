module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonInduction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonIteration
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonIterationSupport

/-! # Typing coherence for categorical iteration interpretation

The common typing compares hidden loop-state types by pure maps. The actual
categorical uniformity and output-naturality laws discharge the loop step.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- The categorical iteration laws prove the optional common-typing step. -/
theorem iterationComparisonRule (M : IterModel.{u,v,w,r} (Ty α) Φ ε) [DecidableEq α] :
    IterationComparisonRule M.toCaseData (ControlData.iter M) := by
  intro n a b iha ihb Γ Δ e e' A B h k hc
  cases h with
  | iter cap s ug ie ha hb =>
    cases k with
    | iter _ t ud ie' ka kb =>
      apply TypingComparison.iter_support M.toCaseData (ControlData.iter M) (ControlEnvironment.iter M)
        cap s t ug ud ie ie' hc ha hb ka kb
      exact TypingComparison.iter M cap _ _
        (QCtx.restrict_unrestricted ug _) (QCtx.restrict_unrestricted ud _) ie ie'
        (hc.restrict _) (hb.outerSupport₁_aligned kb) (ha.support_aligned ka)
        ((hb.outerSupport₁_aligned kb).snoc _ _)
        ha.support hb.outerSupport₁ ka.support kb.outerSupport₁
        (iha ha.support ka.support (ha.support_aligned ka))
        (ihb hb.outerSupport₁ kb.outerSupport₁ ((hb.outerSupport₁_aligned kb).snoc _ _))

/-- Categorical iteration interpretation is independent of every typing witness,
including hidden loop states, sum choices, and quantitative resource splits. -/
theorem denoteIter_coherent (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε} {t : Term Φ n} {A : Ty α}
    (h : HasType .iter Γ e t A) (k : HasType .iter Γ e' t A) :
    denoteIter M h = denoteIter M k := by
  classical
  exact TypingComparison.eq M.toCaseData (ControlData.iter M) h k
    (hasTypingComparison M.toCaseData (fun _ => M.iterate) (ControlEnvironment.iter M)
      (iterationComparisonRule M) t h k (QCtx.Aligned.refl Γ))

end Silmaril.Isotope.Refinement.Models.Denotation
