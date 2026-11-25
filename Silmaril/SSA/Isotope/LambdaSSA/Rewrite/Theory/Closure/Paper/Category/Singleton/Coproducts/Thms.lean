module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Coproducts.Thms
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
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

set_option backward.isDefEq.respectTransparency false in
/-- A typed impossible input makes all arrows out of the empty type agree. -/
theorem emptyHom_ext {Y : TypeCategory (τ := τ) Φ}
    (f g : ofType (Silmaril.empty : τ) ⟶ Y) : f = g := by
  obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
  obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
  exact (ofRegion_eq_iff _ _).2 (.cfgEta (.native (.initial (.var (i := 0) rfl) hf.hasType hg.hasType)))

/-- The guarded decoder supplies an initial object in the Paper singleton category. -/
noncomputable def emptyIsInitial : IsInitial (ofType (Φ := Φ) (Silmaril.empty : τ)) :=
  IsInitial.ofUniqueHom (fun Y => ofRegion (emptyRegion_typed (show τ from Y)))
    (fun _ f => emptyHom_ext f _)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
