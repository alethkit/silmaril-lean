module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionFiniteCoproducts

/-! # Finite coproducts in the extended singleton category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- The two projected constructor injections exhibit the syntactic sum as a coproduct. -/
noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan Seed A B) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionFiniteCoproducts.sumCofanIsColimit Seed A B

/-- The projection of the guarded empty type is initial. -/
noncomputable def emptyIsInitial : IsInitial (ofType Seed (Silmaril.empty : τ)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionFiniteCoproducts.emptyIsInitial Seed

instance hasBinaryCoproducts : HasBinaryCoproducts (TypeCategory Seed) :=
  haveI (X Y : TypeCategory Seed) : HasBinaryCoproduct X Y :=
    ⟨⟨⟨_, sumCofanIsColimit Seed (show τ from X.as) (show τ from Y.as)⟩⟩⟩
  hasBinaryCoproducts_of_hasColimit_pair _

instance hasInitial : HasInitial (TypeCategory Seed) :=
  (emptyIsInitial Seed).hasInitial

instance hasFiniteCoproducts : HasFiniteCoproducts (TypeCategory Seed) :=
  hasFiniteCoproducts_of_has_binary_and_initial

instance projection_preservesFiniteCoproducts : PreservesFiniteCoproducts (projection Seed) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionFiniteCoproducts.projection_preservesFiniteCoproducts Seed

/-- Compare the exact syntax sum with the category's chosen coproduct. -/
noncomputable def sumIso (A B : τ) :
    ofType Seed (Silmaril.coprod A B) ≅ ofType Seed A ⨿ ofType Seed B :=
  (sumCofanIsColimit Seed A B).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)] theorem sumCofan_inl_sumIso_hom (A B : τ) :
    (sumCofan Seed A B).inl ≫ (sumIso Seed A B).hom = coprod.inl :=
  (sumCofanIsColimit Seed A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem sumCofan_inr_sumIso_hom (A B : τ) :
    (sumCofan Seed A B).inr ≫ (sumIso Seed A B).hom = coprod.inr :=
  (sumCofanIsColimit Seed A B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.right⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
