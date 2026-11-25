module

public import Silmaril.Semantics.Calco2019.Trace.ProfileEquivalence.Thms

public section

universe u v

namespace Silmaril.Calco2019.Proofs.TraceCompatibility

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] [HasInitial K] {P : Coproducts K} {G : Guardedness P}

theorem conway_feedback {I : K} (i : IsInitial I)
    (T : G.FourInterfaceTrace) (laws : T.Lawful) :
    @Eq G.Feedback (T.conway laws).toFixpoints.feedback (T.toFeedback i) := by
  have localLaws := (T.toFeedback_lawful initialIsInitial laws).toLocalLaws
  have reconstructed : @Eq G.Feedback (T.conway laws).toFixpoints.feedback
      (T.toFeedback initialIsInitial) := by
    funext A B U f hf
    exact Feedback.fixpoints_feedback localLaws f hf
  exact reconstructed.trans (T.toFeedback_eq_of_initial initialIsInitial i laws.tighten)

end Silmaril.Calco2019.Proofs.TraceCompatibility
