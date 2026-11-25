module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Thms

/-! # Unit feedback and yanking at the marked trace interfaces -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- Interchange the two copies of the state. Both marked external interfaces
are the initial object, so the remaining external leg may enter feedback. -/
def traceInterchange {I U : K} (i : IsInitial I) :
    P.sum (P.sum I U) U ⟶ P.sum U (P.sum I U) :=
  restoreTraceBody (tighten (P.swap (X := U) (Y := U))
    (P.desc (i.to U) (𝟙 U)) (P.inl : U ⟶ P.sum U I))

/-- Delete an initial feedback port using the coproduct unit maps. -/
def deleteInitialFeedback {A B C D I : K} (i : IsInitial I)
    (f : P.sum (P.sum A I) B ⟶ P.sum C (P.sum D I)) :
    P.sum A B ⟶ P.sum C D :=
  P.desc (P.inl ≫ P.inl) P.inr ≫ f ≫ P.map (𝟙 C) (P.desc (𝟙 D) (i.to D))

end Silmaril.Calco2019.Guardedness
