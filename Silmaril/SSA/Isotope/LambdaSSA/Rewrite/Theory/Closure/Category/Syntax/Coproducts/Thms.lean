module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Coproducts.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Exact native sum and empty type comparisons -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The coproduct property of the sum type reflects along the singleton inclusion. -/
noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan (Φ := Φ) (Γ := Γ) A B) :=
  isColimitOfReflects (toContinuation Φ Γ) (BinaryCofan.isColimitMapCoconeEquiv.symm
    (ContinuationContext.singletonSumIsColimit (Φ := Φ) (Γ := Γ) A B))

/-- Compare the syntactic sum type with the category's chosen coproduct. -/
noncomputable def sumIso (A B : τ) :
    (ofType (Φ := Φ) (Γ := Γ) (Silmaril.coprod A B)) ≅ ofType A ⨿ ofType B :=
  (sumCofanIsColimit A B).coconePointUniqueUpToIso (colimit.isColimit (pair (ofType A) (ofType B)))

@[reassoc (attr := simp)] theorem sumCofan_inl_sumIso_hom (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inl ≫ (sumIso A B).hom = coprod.inl :=
  (sumCofanIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem sumCofan_inr_sumIso_hom (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inr ≫ (sumIso A B).hom = coprod.inr :=
  (sumCofanIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.right⟩

/-- The syntactic empty type is initial in the type category. -/
noncomputable def emptyIsInitial :
    IsInitial (ofType (Φ := Φ) (Γ := Γ) (Silmaril.empty : τ)) :=
  let initial := ContinuationContext.singletonEmptyIsInitial (Φ := Φ) (Γ := Γ)
  IsInitial.ofUniqueHom (fun _ => InducedCategory.homMk (initial.to _))
    (fun _ f => InducedCategory.hom_ext (initial.hom_ext f.hom _))

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
