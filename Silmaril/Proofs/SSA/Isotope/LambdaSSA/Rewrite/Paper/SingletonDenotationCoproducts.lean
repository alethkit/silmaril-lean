module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Finite.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Finite coproduct preservation for guarded singleton denotation -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DenotationCoproducts

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Region Region.Paper.TypeCategory
open Semantics.Categorical

set_option backward.isDefEq.respectTransparency false
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "F" => denoteFunctor (Φ := Φ) J M shared

include shared in
theorem exactInl (A B : τ) :
    (F).map (sumCofan (Φ := Φ) A B).inl =
      J.map (coprod.inl ≫ (M.coprodIso A B).inv) := by
  change denoteArrow J M _ = _
  rw [sumCofan_inl, denoteArrow_ofRegion J M shared,
    denoteSingletonRegion_br J M (.inl (.var (i := 0) rfl))]
  simp only [lookup, ← J.map_comp]
  change J.map ((λ_ (M.obj A)).inv ≫
      CartesianMonoidalCategory.snd (𝟙_ V) (M.obj A) ≫ coprod.inl ≫
        (M.coprodIso A B).inv) = _
  rw [CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]

include shared in
theorem exactInr (A B : τ) :
    (F).map (sumCofan (Φ := Φ) A B).inr =
      J.map (coprod.inr ≫ (M.coprodIso A B).inv) := by
  change denoteArrow J M _ = _
  rw [sumCofan_inr, denoteArrow_ofRegion J M shared,
    denoteSingletonRegion_br J M (.inr (.var (i := 0) rfl))]
  simp only [lookup, ← J.map_comp]
  change J.map ((λ_ (M.obj B)).inv ≫
      CartesianMonoidalCategory.snd (𝟙_ V) (M.obj B) ≫ coprod.inr ≫
        (M.coprodIso A B).inv) = _
  rw [CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]

include shared in
theorem mapInl (A B : τ) :
    (F).map (coprod.inl : ofType A ⟶ ofType A ⨿ ofType B) ≫
      (denoteCoprodIso J M shared A B).hom = coprod.inl := by
  rw [← sumCofan_inl_sumIso_hom, Functor.map_comp]
  simp only [denoteCoprodIso, denoteExactSumIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [exactInl J M shared]
  change J.map (coprod.inl ≫ (M.coprodIso A B).inv) ≫ J.map (M.coprodIso A B).hom ≫
    (asIso (coprodComparison J (M.obj A) (M.obj B))).inv = _
  rw [← J.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact map_inl_inv_coprodComparison J

include shared in
theorem mapInr (A B : τ) :
    (F).map (coprod.inr : ofType B ⟶ ofType A ⨿ ofType B) ≫
      (denoteCoprodIso J M shared A B).hom = coprod.inr := by
  rw [← sumCofan_inr_sumIso_hom, Functor.map_comp]
  simp only [denoteCoprodIso, denoteExactSumIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [exactInr J M shared]
  change J.map (coprod.inr ≫ (M.coprodIso A B).inv) ≫ J.map (M.coprodIso A B).hom ≫
    (asIso (coprodComparison J (M.obj A) (M.obj B))).inv = _
  rw [← J.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact map_inr_inv_coprodComparison J

include shared in
theorem comparison (A B : τ) :
    coprodComparison (F) (ofType A) (ofType B) = (denoteCoprodIso J M shared A B).inv := by
  apply (cancel_mono (denoteCoprodIso J M shared A B).hom).mp
  rw [Iso.inv_hom_id]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, mapInl, Category.comp_id]
  · rw [inr_coprodComparison_assoc, mapInr, Category.comp_id]

include shared in
theorem mapDesc {A B D : τ} (f : ofType A ⟶ ofType D) (g : ofType B ⟶ ofType D) :
    (F).map (coprod.desc f g) = (denoteCoprodIso J M shared A B).hom ≫
      coprod.desc ((F).map f) ((F).map g) := by
  apply (cancel_epi (denoteCoprodIso J M shared A B).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, ← comparison]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, ← (F).map_comp, coprod.inl_desc, coprod.inl_desc]
  · rw [inr_coprodComparison_assoc, ← (F).map_comp, coprod.inr_desc, coprod.inr_desc]

include shared in
theorem preservesBinary : PreservesColimitsOfShape (Discrete WalkingPair) (F) := by
  have : ∀ {X Y : Paper.TypeCategory (τ := τ) Φ}, IsIso (coprodComparison (F) X Y) := fun {X Y} => by
    change IsIso (coprodComparison (F) (ofType (show τ from X)) (ofType (show τ from Y)))
    rw [comparison]
    infer_instance
  exact preservesBinaryCoproducts_of_isIso_coprodComparison (F)

include shared in
theorem preservesFinite : PreservesFiniteCoproducts (F) where
  preserves n := by
    have := preservesBinary (Φ := Φ) J M shared
    have : PreservesColimit (Functor.empty.{0} (Paper.TypeCategory (τ := τ) Φ)) (F) :=
      preservesColimit_of_preserves_colimit_cocone
        (emptyIsInitial (Φ := Φ) (τ := τ))
        ((isColimitMapCoconeEmptyCoconeEquiv (F) _).symm
          ((isColimitMapCoconeEmptyCoconeEquiv J _) (isColimitOfPreserves J M.emptyIsInitial)))
    have := preservesColimitsOfShape_pempty_of_preservesInitial (F)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (F) (Fin n)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DenotationCoproducts
