module

public import Silmaril.Semantics.Calco2019.Trace.Sliding.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Sliding

/-! # Sliding with an adapter that can return immediately -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (h : V ⟶ P.sum B U)

theorem slideAfter_guard (guard : G.guarded (P.inr ≫ f) ∨ G.guarded h) :
    G.FeedbackGuard (slideAfter f h) :=
  Proofs.Feedback.slideAfter_guard f h guard

theorem slideBefore_guard (guard : G.guarded (P.inr ≫ f) ∨ G.guarded h) :
    G.FeedbackGuard (slideBefore f h) :=
  Proofs.Feedback.slideBefore_guard f h guard

/-- Slide an adapter with a shared result across the cut of a feedback loop.
Either the body or the adapter may supply the guard. -/
theorem feedback_slide_shared (F : G.Conway) (guard : G.guarded (P.inr ≫ f) ∨ G.guarded h) :
    F.toFixpoints.feedback (slideAfter f h) (slideAfter_guard f h guard) =
      F.toFixpoints.feedback (slideBefore f h) (slideBefore_guard f h guard) :=
  Proofs.Feedback.slide_shared f h guard F _ _

end Silmaril.Calco2019.Guardedness
