module

public import Silmaril.Semantics.Calco2019.Trace.Sliding.Thms

/-! # Feedback laws with the coproduct branches displayed -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.Feedback

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- Apply feedback to a copairing whose entry and recursive branches are given separately. -/
def onBranches (trace : G.Feedback) {A B U : K}
    (entry : A ⟶ P.sum B U) (body : U ⟶ P.sum B U) (guard : G.guarded body) : A ⟶ B :=
  trace (P.desc entry body) (by
    change G.guarded (P.inr ≫ P.desc entry body)
    rw [P.inr_desc]
    exact guard)

/-- Tightening, superposition and shared-result sliding for coproduct feedback.
The unit and two-state vanishing laws can be imposed separately. -/
structure LocalLaws (trace : G.Feedback) : Prop where
  tighten {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (hf : G.FeedbackGuard f) :
    trace (Guardedness.tighten f a b) (tighten_feedbackGuard f a b hf) = a ≫ trace f hf ≫ b
  superpose {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (g : A' ⟶ B') (hf : G.FeedbackGuard f) :
    trace (Guardedness.superpose f g) (superpose_feedbackGuard f g hf) =
      P.map (trace f hf) g
  slide {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (h : V ⟶ P.sum B U)
    (guard : G.guarded (P.inr ≫ f) ∨ G.guarded h) :
    trace (slideAfter f h) (slideAfter_guard f h guard) =
      trace (slideBefore f h) (slideBefore_guard f h guard)

/-- Conway feedback satisfies the three displayed local laws. -/
theorem localLaws_ofConway (F : G.Conway) : LocalLaws F.toFixpoints.feedback where
  tighten := feedback_tighten F
  superpose := feedback_superpose F
  slide f h guard := feedback_slide_shared f h F guard

end Silmaril.Calco2019.Guardedness.Feedback
