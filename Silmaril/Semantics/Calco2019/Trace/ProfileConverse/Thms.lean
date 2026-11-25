module

public import Silmaril.Semantics.Calco2019.Trace.ProfileConverse.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileConverse

/-! # Recover a four-interface operator by guarded tightening -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.FourInterfaceTrace

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {I : K} (i : IsInitial I)

theorem feedbackBody_guard {A B U : K} (f : P.sum A U ⟶ P.sum B U) (hf : G.FeedbackGuard f) :
    G.TraceGuard (feedbackBody i f) :=
  Proofs.Feedback.feedbackBody_guard i f hf

/-- Apply the four-interface trace with both external marked ports initial. -/
@[expose]
def toFeedback (T : G.FourInterfaceTrace) : G.Feedback :=
  fun f hf => P.inr ≫ T.run (feedbackBody_guard i f hf) ≫ P.desc (𝟙 _) (i.to _)

theorem ofConway_tightening (F : G.Conway) : (ofConway F).Tightening :=
  fun a b hf ha hb => guardedTrace_tighten a b F hf ha hb

/-- Tightening with coproduct unit maps recovers the original trace value. -/
theorem toFeedback_run (T : G.FourInterfaceTrace) (laws : T.Tightening)
    {A B C D U : K} {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (hf : G.TraceGuard f) :
    T.toFeedback i (traceBody f) (traceBody_guard hf) = T.run hf :=
  Proofs.Feedback.run_recovered i T laws hf

/-- For a trace induced by Conway iteration the restriction is the usual
coproduct feedback formula. -/
theorem toFeedback_ofConway (F : G.Conway) :
    @Eq G.Feedback ((ofConway F).toFeedback i) F.toFixpoints.feedback := by
  funext A B U f hf
  exact Proofs.Feedback.feedback_recovered i F f hf

/-- Four-interface tightening induces arbitrary retargeting of the unmarked
interfaces in ordinary coproduct feedback. -/
theorem toFeedback_tighten (T : G.FourInterfaceTrace) (laws : T.Tightening)
    {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (hf : G.FeedbackGuard f) :
    T.toFeedback i (tighten f a b) (tighten_feedbackGuard f a b hf) =
      a ≫ T.toFeedback i f hf ≫ b :=
  Proofs.Feedback.reduced_tighten i T laws f a b hf

/-- Restricting a four-interface trace needs only tightening to be independent
of the choice of initial object used to pad the marked ports. -/
theorem toFeedback_eq_of_initial {J : K} (j : IsInitial J)
    (T : G.FourInterfaceTrace) (laws : T.Tightening) :
    @Eq G.Feedback (T.toFeedback i) (T.toFeedback j) := by
  funext A B U f hf
  exact Proofs.Feedback.reduced_initial_independent i j T laws f hf

end Silmaril.Calco2019.Guardedness.FourInterfaceTrace
