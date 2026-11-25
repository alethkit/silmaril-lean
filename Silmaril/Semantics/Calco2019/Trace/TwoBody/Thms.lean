module

public import Silmaril.Semantics.Calco2019.Trace.TwoBody.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.TwoBody

/-! # Guarded sliding on two separately visible bodies -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoBody

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A E B D U V : K} (c : TwoBody P A E B D U V)

theorem cuts_guarded (guard : G.guarded (P.inr ≫ c.first) ∨ G.guarded (P.inr ≫ c.second)) :
    G.FeedbackGuard c.cutFirst ∧ G.FeedbackGuard c.cutSecond :=
  Proofs.Feedback.cuts_guarded c guard

/-- Sliding the cut leaves the computation on both external interfaces unchanged.
Either body may supply the guard on the feedback path. -/
theorem slide {trace : G.Feedback} [HasInitial K] (laws : Feedback.Lawful trace)
    (guard : G.guarded (P.inr ≫ c.first) ∨ G.guarded (P.inr ≫ c.second)) :
    trace c.cutFirst (c.cuts_guarded guard).1 = trace c.cutSecond (c.cuts_guarded guard).2 :=
  Proofs.Feedback.slideTwoBodies_lawful c guard laws

end Silmaril.Calco2019.Guardedness.TwoBody
