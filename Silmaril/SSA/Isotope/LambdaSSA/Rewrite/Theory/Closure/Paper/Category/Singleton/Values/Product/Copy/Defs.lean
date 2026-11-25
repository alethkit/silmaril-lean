module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Defs

/-! # Copying under sequential pairing in the Paper singleton category -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

/-- Evaluating twice agrees with evaluating once and copying the result. -/
def PreservesDiagonal : MorphismProperty Comp := fun _ A f =>
  pairArrows (τ := τ) f f = f ≫ diagonalArrow (show τ from A)

/-- The arrows that preserve diagonal and interchange with every computation. -/
def CentralCopies : MorphismProperty Comp := fun _ _ f =>
  WhiskerCentral f ∧ PreservesDiagonal f

/-- Each marked primitive preserves the diagonal. -/
def PrimitiveReturnsCopy {ε : Type w} [HasEff Φ ε] (pe : ε) : Prop :=
  ∀ p : Φ, IsPure pe p → PreservesDiagonal (primitiveReturn (τ := τ) p)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
