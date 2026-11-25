module

public import Silmaril.Semantics.Calco2019.Trace.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace

/-! # Equations for the guarded feedback formula of Remark 15 -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- Forming feedback from a fixpoint operator and extracting the dagger recovers that operator. -/
theorem feedback_recovers (F : G.Fixpoints) {U B : K} (f : U ⟶ P.sum B U) (hf : G.guarded f) :
    Feedback.iterate F.feedback f hf = F.iterate f hf :=
  Proofs.Feedback.recover F f hf

theorem tighten_feedbackGuard {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (hf : G.FeedbackGuard f) :
    G.FeedbackGuard (tighten f a b) :=
  Proofs.Feedback.tighten_guard f a b hf

/-- Feedback is natural in its entry and result interfaces. -/
theorem feedback_tighten (F : G.Conway) {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (hf : G.FeedbackGuard f) :
    F.toFixpoints.feedback (tighten f a b) (tighten_feedbackGuard f a b hf) =
      a ≫ F.toFixpoints.feedback f hf ≫ b :=
  Proofs.Feedback.tighten F f a b hf

theorem slide_feedbackGuard {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U)
    (hf : G.guarded (P.inr ≫ f) ∨ G.guarded (q ≫ (P.inr : U ⟶ P.sum B U))) :
    G.FeedbackGuard (f ≫ P.map (𝟙 B) q) ∧ G.FeedbackGuard (P.map (𝟙 A) q ≫ f) :=
  Proofs.Feedback.slide_guards f q hf

/-- Sliding is available when the recursive branch of the body or the adapter is guarded. -/
theorem feedback_slide (F : G.Conway) {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U)
    (hf : G.guarded (P.inr ≫ f) ∨ G.guarded (q ≫ (P.inr : U ⟶ P.sum B U))) :
    F.toFixpoints.feedback (f ≫ P.map (𝟙 B) q) (slide_feedbackGuard f q hf).1 =
      F.toFixpoints.feedback (P.map (𝟙 A) q ≫ f) (slide_feedbackGuard f q hf).2 :=
  Proofs.Feedback.slide F f q hf _ _

/-- The interchange of two copies of the state feeds back to the identity. -/
theorem feedback_yank (F : G.Fixpoints) (U : K) :
    F.feedback (P.swap (X := U) (Y := U)) (by
      change G.guarded (P.inr ≫ P.swap (X := U) (Y := U))
      simpa [Coproducts.swap] using G.trivial (X := U) (Y := U) (Z := U) (𝟙 U)) = 𝟙 U :=
  Proofs.Feedback.yanking F U

theorem initial_feedbackGuard {A B I : K} (i : IsInitial I)
    (f : P.sum A I ⟶ P.sum B I) : G.FeedbackGuard f :=
  Proofs.Feedback.vanishing_initial_guard i f

/-- Feedback over the initial object is the transport along the coproduct unitors. -/
theorem feedback_vanish_initial (F : G.Fixpoints) {A B I : K} (i : IsInitial I)
    (f : P.sum A I ⟶ P.sum B I) :
    F.feedback f (initial_feedbackGuard i f) = P.inl ≫ f ≫ P.desc (𝟙 B) (i.to B) :=
  Proofs.Feedback.vanishing_initial F i f _

theorem superpose_feedbackGuard {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (g : A' ⟶ B') (hf : G.FeedbackGuard f) : G.FeedbackGuard (superpose f g) :=
  Proofs.Feedback.superpose_guard f g hf

/-- An independent computation can be carried through feedback unchanged. -/
theorem feedback_superpose (F : G.Conway) {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (g : A' ⟶ B') (hf : G.FeedbackGuard f) :
    F.toFixpoints.feedback (superpose f g) (superpose_feedbackGuard f g hf) =
      P.map (F.toFixpoints.feedback f hf) g :=
  Proofs.Feedback.superpose F f g hf _

end Silmaril.Calco2019.Guardedness
