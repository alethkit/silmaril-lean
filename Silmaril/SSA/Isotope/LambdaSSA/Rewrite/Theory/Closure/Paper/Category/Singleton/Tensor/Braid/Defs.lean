module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms

/-! # The guarded swap representative in the Paper quotient -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Unpack the input and return the two components in reverse order. -/
def braidRegion {Φ : Type v} : Region Φ :=
  .let₂ (.var 0) (.br 0 (.pair (.var 0) (.var 1)))

theorem braidBranches (A B : τ) :
    ValueBranches [product A B] (braidRegion : Region Φ) [product B A] :=
  .let₂ (.var rfl) (.br rfl (.pair (.var rfl) (.var rfl)))

/-- The swap of the two factors as an arrow of the singleton category. -/
def braid (A B : τ) :
    ofType (Φ := Φ) (product A B) ⟶ ofType (product B A) :=
  ofRegion (braidBranches A B)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
