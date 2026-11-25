module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs

/-! # Diagonal and sequential pairing in the Paper singleton category -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Return two copies of the single input as a constructor pair. -/
def diagonalArrow (X : τ) : ofType (Φ := Φ) X ⟶ ofType (product X X) :=
  ofRegion (Paper.RetainedLet.diagonal_typed X)

/-- Copy the input, evaluate the left arrow, then evaluate the right arrow. -/
def pairArrows {X A B : τ} (f : ofType (Φ := Φ) X ⟶ ofType A) (g : ofType (Φ := Φ) X ⟶ ofType B) :
    ofType (Φ := Φ) X ⟶ ofType (product A B) :=
  diagonalArrow (Φ := Φ) X ≫ whiskerRight f (ofType X) ≫ whiskerLeft (ofType A) g

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
