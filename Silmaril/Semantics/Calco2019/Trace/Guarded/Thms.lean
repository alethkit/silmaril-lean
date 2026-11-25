module

public import Silmaril.Semantics.Calco2019.Trace.Guarded.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Guarded

/-! # The guarded output of the four-interface trace -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U : K} {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}

/-- Reordering a body of the four-interface trace gives a guarded feedback body. -/
theorem traceBody_guard (hf : G.TraceGuard f) : G.FeedbackGuard (traceBody f) :=
  Proofs.Feedback.traceBody_guard f hf

/-- The four-interface trace induced by guarded Conway iteration. -/
@[expose]
def Fixpoints.guardedTrace (F : G.Fixpoints) (hf : G.TraceGuard f) :
    P.sum A B ⟶ P.sum C D :=
  F.feedback (traceBody f) (traceBody_guard hf)

/-- The trace remains guarded from the first input to the designated output. -/
theorem Fixpoints.guardedTrace_guarded (F : G.Fixpoints) (hf : G.TraceGuard f) :
    G.guarded (P.inl ≫ F.guardedTrace hf) :=
  Proofs.Feedback.trace_preserves_guard f hf F

end Silmaril.Calco2019.Guardedness
