module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Thms

/-! # Type-former coproducts in the native LambdaSSA type category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The two injections into the native sum type. -/
@[expose] def sumCofan (A B : τ) :
    BinaryCofan (ofType (Φ := Φ) (Γ := Γ) A) (ofType B) :=
  let X := (ContinuationContext.single A : ContinuationContext Φ Γ)
  let Y := (ContinuationContext.single B : ContinuationContext Φ Γ)
  BinaryCofan.mk
    (InducedCategory.homMk (Y := ofType (Silmaril.coprod A B)) (X.appendInl Y ≫ ContinuationContext.sumTag A B))
    (InducedCategory.homMk (X.appendInr Y ≫ ContinuationContext.sumTag A B))

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
