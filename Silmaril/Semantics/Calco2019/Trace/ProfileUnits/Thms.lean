module

public import Silmaril.Semantics.Calco2019.Trace.ProfileUnits.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileUnits

/-! # Four-interface yanking and vanishing over the unit -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

theorem traceInterchange_guard {I U : K} (i : IsInitial I) :
    G.TraceGuard (traceInterchange (P := P) (U := U) i) :=
  Proofs.Feedback.traceInterchange_guard i

/-- Yanking connects the two visible copies via the unitors. -/
theorem guardedTrace_yank (F : G.Conway) {I U : K} (i : IsInitial I) :
    F.toFixpoints.guardedTrace (traceInterchange_guard (G := G) (U := U) i) =
      P.desc (i.to U) (𝟙 U) ≫ (P.inl : U ⟶ P.sum U I) :=
  Proofs.Feedback.profile_yank F i

/-- Vanishing I for the four-interface profile, with the coproduct unit maps displayed. -/
theorem guardedTrace_vanish_initial (F : G.Fixpoints) {A B C D I : K} (i : IsInitial I)
    {f : P.sum (P.sum A I) B ⟶ P.sum C (P.sum D I)} (hf : G.TraceGuard f) :
    F.guardedTrace hf = deleteInitialFeedback i f :=
  Proofs.Feedback.profile_vanish_initial F i hf

end Silmaril.Calco2019.Guardedness
