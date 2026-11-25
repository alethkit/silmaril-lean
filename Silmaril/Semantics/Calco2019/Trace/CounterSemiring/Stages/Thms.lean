module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Stages.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringStages

/-! # Staged vanishing and ordinary sliding for weighted networks -/

public section

universe a b u v

namespace Silmaril.Calco2019.CounterSemiring

variable {A : Type a} {B : Type b} {U : Type u} {V : Type v} [Fintype U] [Fintype V]

/-- Closing the two feedback blocks in stages agrees with closing both at once. -/
theorem networkFeedback_vanishPair (f : Network A B (U ⊕ V)) :
    networkFeedback (networkFeedback (innerBody f)) = networkFeedback f :=
  Proofs.CounterSemiringStages.feedback_pair f

/-- An ordinary adapter can slide across the weighted feedback boundary. -/
theorem networkFeedback_slide (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    networkFeedback (slidingAfter f q) = networkFeedback (slidingBefore f q) :=
  Proofs.CounterSemiringStages.feedback_slide f q

end Silmaril.Calco2019.CounterSemiring
