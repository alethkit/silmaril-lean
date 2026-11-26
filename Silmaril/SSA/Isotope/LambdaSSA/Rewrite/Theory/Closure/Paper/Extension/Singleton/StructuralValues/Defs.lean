module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Defs

/-! # Central arrows preserving copy and discard in the computation quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- Membership uses the three equations in the quotient itself. -/
def HomProperty : MorphismProperty (TypeCategory Seed) := fun X Y f =>
  CentralCopies Seed f ∧ f ≫ discardArrow Seed Y.as = discardArrow Seed X.as

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
