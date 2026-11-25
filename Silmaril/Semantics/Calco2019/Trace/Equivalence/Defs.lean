module

public import Silmaril.Semantics.Calco2019.Trace.Converse.Thms

/-! # The two-state vanishing law for coproduct feedback -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.Feedback

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- Feedback over a jointly guarded pair equals its staged execution.
The inner trace takes the second-state feedback and leaves the first state as a result. -/
def PairVanishing (trace : G.Feedback) : Prop :=
  ∀ {A B U V : K} (D : TwoStateBody G A B U V)
    (h : G.guarded (D.first ≫ P.desc (𝟙 _) (iterate trace D.second D.second_guard))),
    let finish := P.desc (𝟙 _) (iterate trace D.second D.second_guard)
    onBranches trace (D.entry ≫ P.assoc) (P.desc D.first D.second ≫ P.assoc) D.guarded =
      onBranches trace (D.entry ≫ finish) (D.first ≫ finish) h

/-- Coproduct feedback with the laws used in the Conway correspondence. -/
structure Lawful (trace : G.Feedback) : Prop extends LocalLaws trace where
  vanishPair : PairVanishing trace

end Silmaril.Calco2019.Guardedness.Feedback
