module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs
public import Silmaril.SSA.Isotope.LetIter.Effects.Thms

/-! # Native iteration driven by a sum-returning request -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback

universe u v

variable {ν : Type u} {Φ : Type v}

/-- A left reply returns. A right reply supplies the next request's state. -/
abbrev loop {n : Nat} (f : Φ) (init : Tm ν Φ n) : Tm ν Φ n :=
  .iter init (.op f (.bv 0))

/-- Project the request state and put a unit field back on the repeat edge. -/
abbrev paddedBody (f : Φ) (n : Nat) : Tm ν Φ (n + 1) :=
  .case (.op f (.let₂ (.bv 0) (.bv 1))) (.inl (.bv 0)) (.inr (.pair (.bv 0) .unit))

/-- Evaluate the initializer once and carry its value paired with unit. -/
abbrev padded {n : Nat} (f : Φ) (init : Tm ν Φ n) : Tm ν Φ n :=
  .iter (.let₁ init (.pair (.bv 0) .unit)) (paddedBody f n)

end Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback
