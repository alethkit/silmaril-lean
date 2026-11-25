module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Coproducts.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CategoryCoproducts

/-! # Coproducts of typed exit interfaces in the paper quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- Paper arrows out of the concatenation agree when they agree on each injection. -/
theorem append_hom_ext (X Y : ContinuationContext Φ Γ) {Z : Interface Φ Γ}
    {f g : fromNative.obj (X.append Y) ⟶ Z}
    (hl : fromNative.map (X.appendInl Y) ≫ f = fromNative.map (X.appendInl Y) ≫ g)
    (hr : fromNative.map (X.appendInr Y) ≫ f = fromNative.map (X.appendInr Y) ≫ g) : f = g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CategoryCoproducts.append_hom_ext X Y hl hr

/-- Concatenation with the native index injections gives a coproduct in the paper quotient. -/
noncomputable def appendIsColimit (X Y : ContinuationContext Φ Γ) :
    IsColimit (appendCofan X Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CategoryCoproducts.appendIsColimit X Y

/-- The singleton containing a sum type gives a coproduct of the two singleton interfaces. -/
noncomputable def singletonSumIsColimit (A B : τ) :
    IsColimit (singletonSumCofan (Φ := Φ) (Γ := Γ) A B) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CategoryCoproducts.singletonSumIsColimit A B

end Silmaril.Isotope.LambdaSSA.Region.Paper
