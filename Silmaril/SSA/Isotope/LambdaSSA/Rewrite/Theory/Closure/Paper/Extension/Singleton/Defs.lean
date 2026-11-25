module

public import Mathlib.CategoryTheory.Quotient
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs

/-! # Quotient of the Paper singleton category by an extended relation -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory
open Silmaril.Isotope.LambdaSSA (VCtx LCtx)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- Relate old singleton arrows using any constructor-branch representatives
that are equivalent in the contextual extension. -/
def homRel : HomRel (Paper.TypeCategory (τ := τ) Φ) := fun X Y f g =>
  ∃ (r s : Region Φ) (hr : ValueBranches [show τ from X] r [show τ from Y])
    (hs : ValueBranches [show τ from X] s [show τ from Y]),
      f = Paper.TypeCategory.ofRegion hr ∧ g = Paper.TypeCategory.ofRegion hs ∧
        Extension.Eqv Seed [show τ from X] r s [show τ from Y]

/-- Reuse the objects and composition of the Paper singleton category. -/
abbrev TypeCategory := CategoryTheory.Quotient (homRel Seed)

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory Seed :=
  CategoryTheory.Quotient.functor (homRel Seed)

abbrev ofType (A : τ) : TypeCategory Seed :=
  (projection Seed).obj (Paper.TypeCategory.ofType (Φ := Φ) A)

abbrev ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    ofType Seed A ⟶ ofType Seed B :=
  (projection Seed).map (Paper.TypeCategory.ofRegion hr)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
