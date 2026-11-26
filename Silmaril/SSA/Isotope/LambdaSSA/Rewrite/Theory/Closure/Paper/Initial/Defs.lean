module

public import Silmaril.SSA.Isotope.Types.Defs

/-! # Structurally empty types -/

public section

universe u

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ]

/-- Empty, a sum of empty types, or a product with an empty component. -/
inductive StructurallyEmpty : τ → Prop
  | empty : StructurallyEmpty (Silmaril.empty : τ)
  | sum {A B : τ} : StructurallyEmpty A → StructurallyEmpty B → StructurallyEmpty (Silmaril.coprod A B)
  | left {A B : τ} : StructurallyEmpty A → StructurallyEmpty (Silmaril.product A B)
  | right {A B : τ} : StructurallyEmpty B → StructurallyEmpty (Silmaril.product A B)

end Silmaril.Isotope.LambdaSSA.Region.Paper
