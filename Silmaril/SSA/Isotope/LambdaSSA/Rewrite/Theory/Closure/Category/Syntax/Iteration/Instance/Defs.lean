module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms
public import Silmaril.Semantics.Categories.Thms

/-! # The category iteration operation on LambdaSSA type arrows -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- Iterate by converting the chosen coproduct exit to the syntax sum and
applying native CFG feedback. -/
noncomputable instance nativeIteration : CategoryTheory.Iteration (SyntacticCategory Φ Γ) where
  iterate {A B} f := SyntacticCategory.iterate (Φ := Φ) (Γ := Γ) (A := (A : τ)) (B := (B : τ))
    (f ≫ (sumIso (Φ := Φ) (Γ := Γ) (B : τ) (A : τ)).inv)

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
