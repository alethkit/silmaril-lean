module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Coproducts.Thms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Binary coproducts in the paper singleton category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan (Φ := Φ) A B) :=
  isColimitOfReflects (toInterface Φ)
    (BinaryCofan.isColimitMapCoconeEquiv.symm (singletonSumIsColimit (Γ := []) A B))

instance hasBinaryCoproduct (X Y : TypeCategory (τ := τ) Φ) : HasBinaryCoproduct X Y :=
  ⟨⟨⟨_, sumCofanIsColimit (Φ := Φ) (show τ from X) (show τ from Y)⟩⟩⟩

instance hasBinaryCoproducts : HasBinaryCoproducts (TypeCategory (τ := τ) Φ) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- Compare the exact sum type with the chosen categorical coproduct. -/
noncomputable def sumIso (A B : τ) :
    ofType (Φ := Φ) (Silmaril.coprod A B) ≅ ofType A ⨿ ofType B :=
  (sumCofanIsColimit A B).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)] theorem sumCofan_inl_sumIso_hom (A B : τ) :
    (sumCofan (Φ := Φ) A B).inl ≫ (sumIso A B).hom = coprod.inl :=
  (sumCofanIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem sumCofan_inr_sumIso_hom (A B : τ) :
    (sumCofan (Φ := Φ) A B).inr ≫ (sumIso A B).hom = coprod.inr :=
  (sumCofanIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.right⟩

theorem sumCofan_inl (A B : τ) :
    (sumCofan (Φ := Φ) A B).inl =
      ofRegion (r := .br 0 (.inl (.var 0))) (.br rfl (.inl (.var rfl))) :=
  InducedCategory.hom_ext (congrArg fromNative.map (ContinuationContext.appendInl_sumTag A B))

theorem sumCofan_inr (A B : τ) :
    (sumCofan (Φ := Φ) A B).inr =
      ofRegion (r := .br 0 (.inr (.var 0))) (.br rfl (.inr (.var rfl))) :=
  InducedCategory.hom_ext (congrArg fromNative.map (ContinuationContext.appendInr_sumTag A B))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
