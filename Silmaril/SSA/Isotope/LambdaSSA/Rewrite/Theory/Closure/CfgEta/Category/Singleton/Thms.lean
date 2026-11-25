module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # The exact coproduct of singleton types in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan (Φ := Φ) (Γ := Γ) A B) :=
  isColimitOfReflects (toInterface Φ Γ)
    (BinaryCofan.isColimitMapCoconeEquiv.symm (CfgEta.singletonSumIsColimit A B))

instance hasBinaryCoproduct (X Y : TypeCategory Φ Γ) : HasBinaryCoproduct X Y :=
  ⟨⟨⟨_, sumCofanIsColimit (Φ := Φ) (Γ := Γ) (show τ from X) (show τ from Y)⟩⟩⟩

instance hasBinaryCoproducts : HasBinaryCoproducts (TypeCategory Φ Γ) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- Compare the exact sum type with the chosen categorical coproduct. -/
noncomputable def sumIso (A B : τ) :
    ofType (Φ := Φ) (Γ := Γ) (Silmaril.coprod A B) ≅ ofType A ⨿ ofType B :=
  (sumCofanIsColimit A B).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)] theorem sumCofan_inl_sumIso_hom (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inl ≫ (sumIso A B).hom = coprod.inl :=
  (sumCofanIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem sumCofan_inr_sumIso_hom (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inr ≫ (sumIso A B).hom = coprod.inr :=
  (sumCofanIsColimit A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.right⟩

theorem sumCofan_inl (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inl =
      ofRegion (r := .br 0 (.inl (.var 0))) (.br rfl (.inl (.var rfl))) :=
  InducedCategory.hom_ext (congrArg fromNative.map (ContinuationContext.appendInl_sumTag A B))

theorem sumCofan_inr (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) A B).inr =
      ofRegion (r := .br 0 (.inr (.var 0))) (.br rfl (.inr (.var rfl))) :=
  InducedCategory.hom_ext (congrArg fromNative.map (ContinuationContext.appendInr_sumTag A B))

/-- The empty type is initial among singleton interfaces. -/
noncomputable def emptyIsInitial : IsInitial (ofType (Φ := Φ) (Γ := Γ) (Silmaril.empty : τ)) :=
  let initial := CfgEta.singletonEmptyIsInitial (Φ := Φ) (Γ := Γ)
  IsInitial.ofUniqueHom (fun _ => InducedCategory.homMk (initial.to _))
    (fun _ f => InducedCategory.hom_ext (initial.hom_ext f.hom _))

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
