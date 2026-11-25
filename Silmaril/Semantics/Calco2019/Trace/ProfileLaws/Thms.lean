module

public import Silmaril.Semantics.Calco2019.Trace.ProfileLaws.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileLaws

/-! # Four-interface trace laws and their coproduct restrictions -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.FourInterfaceTrace

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- Conway feedback satisfies the local four-interface trace laws. -/
theorem localLaws_ofConway (T : G.Conway) : (ofConway T).LocalLaws where
  tighten := ofConway_tightening T
  superpose hf hg := guardedTrace_superpose T hf hg
  vanishInitial := by
    intro A B C D I i f hf
    exact guardedTrace_vanish_initial T.toFixpoints i hf
  yank i := guardedTrace_yank T i
  slideI i s := s.slidingI T i
  slideII i s := s.slidingII T i
  slideIII s := s.slidingIII T

/-- Four-interface superposition restricts to ordinary coproduct superposition. -/
theorem toFeedback_superpose {I A B U A' B' : K}
    (i : IsInitial I) (T : G.FourInterfaceTrace) (laws : T.LocalLaws)
    (f : P.sum A U ⟶ P.sum B U) (g : A' ⟶ B') (hf : G.FeedbackGuard f) :
    T.toFeedback i (superpose f g) (superpose_feedbackGuard f g hf) =
      P.map (T.toFeedback i f hf) g :=
  Proofs.Feedback.reduced_superpose i T laws f g hf

/-- The four-interface equations imply all local coproduct feedback laws. -/
theorem toFeedback_localLaws {I : K} (i : IsInitial I)
    (T : G.FourInterfaceTrace) (laws : T.LocalLaws) :
    Feedback.LocalLaws (T.toFeedback i) where
  tighten := T.toFeedback_tighten i laws.tighten
  superpose := T.toFeedback_superpose i laws
  slide := Proofs.Feedback.reduced_slide i T laws

end Silmaril.Calco2019.Guardedness.FourInterfaceTrace
