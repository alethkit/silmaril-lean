module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Instance.Defs

/-! # Agreement of category iteration with the syntactic sum operator -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The coproduct comparison cancels when iteration starts from a native sum exit. -/
theorem iterate_comp_sumIso {A B : τ}
    (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType (Silmaril.coprod B A)) :
    CategoryTheory.iterate (f ≫ (sumIso B A).hom) = SyntacticCategory.iterate f := by
  change SyntacticCategory.iterate ((f ≫ (sumIso B A).hom) ≫ (sumIso B A).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
