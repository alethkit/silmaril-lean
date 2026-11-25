module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Defs

/-! # A native iterate that requests a choice at every step -/

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

universe u

/-- For a nullary sum primitive, return the left payload and repeat on the
right. Each iteration uses the same unit state and makes its own request. -/
def repeatOnRight {Φ Ψ : Type u} (g : Ψ) (n : Nat) : Tm Empty (Φ ⊕ Ψ) n :=
  .iter .unit (.case (.op (.inr g) .unit) (.inl (.bv 0)) (.inr .unit))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
