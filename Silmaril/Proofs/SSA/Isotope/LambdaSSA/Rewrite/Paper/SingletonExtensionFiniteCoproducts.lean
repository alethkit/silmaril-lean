module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Colimits of projected constructor injections -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionFiniteCoproducts

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (TypeCategory projection ofType sumCofan projection_map_desc_congr)
open Paper.TypeCategory (sumIso sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "Base" => Paper.TypeCategory (τ := τ) Φ
set_option hygiene false in
local notation "F" => projection Seed

set_option backward.isDefEq.respectTransparency false in
noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan Seed A B) := by
  let lift {Z : TypeCategory Seed} (f : ofType Seed A ⟶ Z) (g : ofType Seed B ⟶ Z) :
      ofType Seed (Silmaril.coprod A B) ⟶ Z :=
    (F).map ((sumIso A B).hom ≫ coprod.desc ((F).preimage (Y := Z.as) f) ((F).preimage (Y := Z.as) g))
  refine BinaryCofan.IsColimit.mk _ lift ?_ ?_ ?_
  · intro Z f g
    change (F).map (Paper.TypeCategory.sumCofan A B).inl ≫ (F).map _ = f
    rw [← Functor.map_comp, ← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc, Functor.map_preimage]
  · intro Z f g
    change (F).map (Paper.TypeCategory.sumCofan A B).inr ≫ (F).map _ = g
    rw [← Functor.map_comp, ← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc, Functor.map_preimage]
  · intro Z f g m hl hr
    obtain ⟨k, rfl⟩ := (F).map_surjective (Y := Z.as) m
    let cf := Paper.TypeCategory.sumCofan (Φ := Φ) A B
    have h : (sumIso A B).hom ≫ coprod.desc (cf.inl ≫ k) (cf.inr ≫ k) = k := by
      apply BinaryCofan.IsColimit.hom_ext (Paper.TypeCategory.sumCofanIsColimit A B)
      · rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]
      · rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]
    refine (congrArg (F).map h.symm).trans ?_
    change _ = (F).map ((sumIso A B).hom ≫ coprod.desc
      ((F).preimage (Y := Z.as) f) ((F).preimage (Y := Z.as) g))
    rw [Functor.map_comp, Functor.map_comp]
    congr 1
    apply projection_map_desc_congr Seed
    · change (F).map cf.inl ≫ (F).map k = f at hl
      rw [Functor.map_comp, Functor.map_preimage]
      exact hl
    · change (F).map cf.inr ≫ (F).map k = g at hr
      rw [Functor.map_comp, Functor.map_preimage]
      exact hr

set_option backward.isDefEq.respectTransparency false in
noncomputable def emptyIsInitial : IsInitial (ofType Seed (Silmaril.empty : τ)) :=
  IsInitial.ofUniqueHom (fun Y => (F).map (Paper.TypeCategory.emptyIsInitial.to Y.as))
    (fun Y f => by
      obtain ⟨g, rfl⟩ := (F).map_surjective (Y := Y.as) f
      exact congrArg (F).map (Paper.TypeCategory.emptyHom_ext g _))

private theorem projection_preservesBinary :
    PreservesColimitsOfShape (Discrete WalkingPair) (F) where
  preservesColimit {K} := by
    let A : τ := K.obj ⟨WalkingPair.left⟩
    let B : τ := K.obj ⟨WalkingPair.right⟩
    have := preservesColimit_of_preserves_colimit_cocone
      (Paper.TypeCategory.sumCofanIsColimit (Φ := Φ) A B)
      (BinaryCofan.isColimitMapCoconeEquiv.symm (sumCofanIsColimit Seed A B))
    exact preservesColimit_of_iso_diagram (F) (diagramIsoPair K).symm

private theorem projection_preservesInitial : PreservesColimit (Functor.empty.{0} Base) (F) :=
  preservesColimit_of_preserves_colimit_cocone
    (Paper.TypeCategory.emptyIsInitial (Φ := Φ) (τ := τ))
    ((isColimitMapCoconeEmptyCoconeEquiv (F) _).symm (emptyIsInitial Seed))

theorem projection_preservesFiniteCoproducts : PreservesFiniteCoproducts (F) where
  preserves n := by
    have := projection_preservesBinary Seed
    have := projection_preservesInitial Seed
    have := preservesColimitsOfShape_pempty_of_preservesInitial (F)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (F) (Fin n)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionFiniteCoproducts
