module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs

/-! # Constructor representatives of singleton state changes -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A state change represented in the quotient by a branch on a constructor value. -/
def ConstructorReturn : MorphismProperty (TypeCategory (τ := τ) Φ) :=
  fun A D h => ∃ (a : Tm Φ) (ha : Tm.BranchValue [show τ from A] a (show τ from D)),
    h = ofRegion (.br (ℓ := 0) rfl ha)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
