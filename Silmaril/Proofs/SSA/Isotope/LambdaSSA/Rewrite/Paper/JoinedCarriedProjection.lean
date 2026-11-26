module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Diagonal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Thms

/-! # Value product naturality at the actual joined capture prefix -/

public section

universe u v w u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton
open Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.SingletonReification (packedWhiskerRight)
open Paper.SingletonReification.SingleCfg.Model (reindexHom)
open CfgEta.TypeCategory.ConstructorReification (fstMap sndMap)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)
set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory (Seed) pe
set_option hygiene false in
local notation "Val" => fun (A : τ) => (⟨Obj A⟩ : Values)
set_option hygiene false in
local notation "I" => wideSubcategoryInclusion (DiscardPreservingReturn (Seed) pe)
set_option hygiene false in
local notation "fan" => discardPreservingFan (Seed) pe (fun h => Or.inl h)
set_option hygiene false in
local notation "limit" => fun (A B : τ) =>
  discardPreservingBinaryFanIsLimit (Seed) pe A B (fun h => Or.inl h)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (K : V ⥤ Values) (M : TypeModel τ V)
  (J : V ⥤ Comp) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem reindex_eq_iff_value_square {A B : τ} (f : M.obj A ⟶ M.obj B)
    (q : K ⋙ (I) ≅ J)
    (a : K.obj (M.obj A) ⟶ Val A) (b : K.obj (M.obj B) ⟶ Val B) (g : Val A ⟶ Val B)
    (source : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map a)
    (target : (objIso B).hom = (q.app (M.obj B)).inv ≫ (I).map b) :
    reindexHom J M objIso (J.map f) = (I).map g ↔ K.map f ≫ b = a ≫ g := by
  rw [← cancel_epi (objIso A).hom]
  change (objIso A).hom ≫ (objIso A).inv ≫ J.map f ≫ (objIso B).hom =
      (objIso A).hom ≫ (I).map g ↔ _
  rw [Iso.hom_inv_id_assoc, target, source]
  have h := q.inv.naturality f
  change J.map f ≫ (q.app (M.obj B)).inv =
    (q.app (M.obj A)).inv ≫ (I).map (K.map f) at h
  rw [reassoc_of% h, Category.assoc, cancel_epi, ← Functor.map_comp, ← Functor.map_comp]
  exact ⟨fun h => (I).map_injective h, congrArg (I).map⟩

set_option backward.isDefEq.respectTransparency false in
theorem fst_eq_iff_value_product_leg (A B : τ) (q : K ⋙ (I) ≅ J)
    (e : K.obj (M.obj A) ≅ Val A) (p : K.obj (M.obj (product A B)) ⟶ Val (product A B))
    (first : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map e.hom)
    (productCoord : (objIso (product A B)).hom = (q.app (M.obj (product A B))).inv ≫ (I).map p) :
    reindexHom J M objIso (J.map (fstMap M A B)) = productFst (Seed) A B ↔
      p ≫ ((fan) A B).fst = K.map (fstMap M A B) ≫ e.hom :=
  (reindex_eq_iff_value_square pe K M J objIso (fstMap M A B) q p e.hom
    ((fan) A B).fst productCoord first).trans eq_comm

noncomputable def valueWhiskerRight {A B : τ} (R : τ) (f : Val A ⟶ Val B) :
    Val (product A R) ⟶ Val (product B R) :=
  BinaryFan.IsLimit.lift ((limit) B R) (((fan) A R).fst ≫ f) ((fan) A R).snd

set_option backward.isDefEq.respectTransparency false in
theorem valueWhiskerRight_map {A B : τ} (R : τ) (f : Val A ⟶ Val B) :
    (I).map (valueWhiskerRight pe R f) = whiskerRight (Seed) ((I).map f) (Obj R) := by
  let G := StructuralValues.fromPureReturns (Seed) pe
  let I₀ := StructuralValues.inclusion (Seed)
  let := StructuralValues.cartesian (Seed) (fun h => Or.inr h)
  let R₀ : StructuralValues.ValueCategory (Seed) := ⟨Obj R⟩
  have equal : G.map (valueWhiskerRight pe R f) = G.map f ▷ R₀ := by
    refine CartesianMonoidalCategory.hom_ext
      (X := (⟨Obj B⟩ : StructuralValues.ValueCategory (Seed))) (Y := R₀) _ _ ?_ ?_
    · rw [CartesianMonoidalCategory.whiskerRight_fst]
      apply WideSubcategory.hom_ext
      exact congrArg (·.hom) (BinaryFan.IsLimit.lift_fst ((limit) B R) (((fan) A R).fst ≫ f) ((fan) A R).snd)
    · trans SemiCartesianMonoidalCategory.snd (G.obj (Val A)) R₀
      · apply WideSubcategory.hom_ext
        exact congrArg (·.hom) (BinaryFan.IsLimit.lift_snd ((limit) B R) (((fan) A R).fst ≫ f) ((fan) A R).snd)
      · exact (CartesianMonoidalCategory.whiskerRight_snd (G.map f) R₀).symm
  exact (congrArg I₀.map equal).trans
    (StructuralValues.map_whiskerRight (Seed) (fun h => Or.inr h) R (G.map f))

set_option backward.isDefEq.respectTransparency false in
theorem chosenBinaryValueProductMap_naturality_right {A B R : τ} (f : M.obj A ⟶ M.obj B)
    (a : K.obj (M.obj A) ≅ Val A) (b : K.obj (M.obj B) ≅ Val B) (r : K.obj (M.obj R) ≅ Val R) :
    K.map (packedWhiskerRight M R A B f) ≫ chosenBinaryValueProductMap pe K M B R b r =
      chosenBinaryValueProductMap pe K M A R a r ≫ valueWhiskerRight pe R (a.inv ≫ K.map f ≫ b.hom) := by
  have left : packedWhiskerRight M R A B f ≫ fstMap M B R = fstMap M A R ≫ f := by
    simp [packedWhiskerRight, fstMap, CartesianMonoidalCategory.whiskerRight_fst]
  have right : packedWhiskerRight M R A B f ≫ sndMap M B R = sndMap M A R := by
    simp [packedWhiskerRight, sndMap, CartesianMonoidalCategory.whiskerRight_snd]
  let g := a.inv ≫ K.map f ≫ b.hom
  let inputMap := chosenBinaryValueProductMap pe K M A R a r
  let outputMap := chosenBinaryValueProductMap pe K M B R b r
  let w := valueWhiskerRight pe R g
  have fromF : inputMap ≫ ((fan) A R).fst = K.map (fstMap M A R) ≫ a.hom :=
    BinaryFan.IsLimit.lift_fst ((limit) A R) _ _
  have fromS : inputMap ≫ ((fan) A R).snd = K.map (sndMap M A R) ≫ r.hom :=
    BinaryFan.IsLimit.lift_snd ((limit) A R) _ _
  have toF : outputMap ≫ ((fan) B R).fst = K.map (fstMap M B R) ≫ b.hom :=
    BinaryFan.IsLimit.lift_fst ((limit) B R) _ _
  have toS : outputMap ≫ ((fan) B R).snd = K.map (sndMap M B R) ≫ r.hom :=
    BinaryFan.IsLimit.lift_snd ((limit) B R) _ _
  have whiskerF : w ≫ ((fan) B R).fst = ((fan) A R).fst ≫ g :=
    BinaryFan.IsLimit.lift_fst ((limit) B R) _ _
  have whiskerS : w ≫ ((fan) B R).snd = ((fan) A R).snd :=
    BinaryFan.IsLimit.lift_snd ((limit) B R) _ _
  change K.map (packedWhiskerRight M R A B f) ≫ outputMap = inputMap ≫ w
  apply BinaryFan.IsLimit.hom_ext ((limit) B R)
  · rw [Category.assoc, toF, Category.assoc, whiskerF, ← Category.assoc inputMap, fromF]
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc, ← K.map_comp_assoc, left]
  · rw [Category.assoc, toS, Category.assoc, whiskerS, fromS, ← K.map_comp_assoc, right]


set_option backward.isDefEq.respectTransparency false in
theorem reindexPackedWhiskerRight_eq_iff_targetProduct {A B R : τ} (f : M.obj A ⟶ M.obj B)
    (q : K ⋙ (I) ≅ J)
    (a : K.obj (M.obj A) ≅ Val A) (b : K.obj (M.obj B) ≅ Val B) (r : K.obj (M.obj R) ≅ Val R)
    (src : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map a.hom)
    (dst : (objIso B).hom = (q.app (M.obj B)).inv ≫ (I).map b.hom)
    (sourceProduct : (objIso (product A R)).hom =
      (q.app (M.obj (product A R))).inv ≫ (I).map (chosenBinaryValueProductMap pe K M A R a r)) :
    (reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
      whiskerRight (Seed) (reindexHom J M objIso (J.map f)) (Obj R)) ↔
    J.map (packedWhiskerRight M R A B f) ≫ (objIso (product B R)).hom =
      J.map (packedWhiskerRight M R A B f) ≫ (q.app (M.obj (product B R))).inv ≫
        (I).map (chosenBinaryValueProductMap pe K M B R b r) := by
  let g := a.inv ≫ K.map f ≫ b.hom
  let w := packedWhiskerRight M R A B f
  have value := (reindex_eq_iff_value_square pe K M J objIso f q a.hom b.hom g src dst).2
    (by simp only [g, Iso.hom_inv_id_assoc])
  have computes := (valueWhiskerRight_map pe R g).trans (congrArg (whiskerRight (Seed) · (Obj R)) value.symm)
  have commute := q.inv.naturality w
  change J.map w ≫ (q.app (M.obj (product B R))).inv =
    (q.app (M.obj (product A R))).inv ≫ (I).map (K.map w) at commute
  have normalized :
      (objIso (product A R)).hom ≫ whiskerRight (Seed) (reindexHom J M objIso (J.map f)) (Obj R) =
        J.map w ≫ (q.app (M.obj (product B R))).inv ≫
          (I).map (chosenBinaryValueProductMap pe K M B R b r) := by
    have square := chosenBinaryValueProductMap_naturality_right pe K M f a b r
    have included := congrArg (fun h => (q.app (M.obj (product A R))).inv ≫ (I).map h) square.symm
    simpa only [sourceProduct, ← computes, Category.assoc, Functor.map_comp,
      reassoc_of% commute] using! included
  rw [← cancel_epi (objIso (product A R)).hom]
  change (objIso (product A R)).hom ≫ (objIso (product A R)).inv ≫
      J.map w ≫ (objIso (product B R)).hom =
    (objIso (product A R)).hom ≫ whiskerRight (Seed) (reindexHom J M objIso (J.map f)) (Obj R) ↔ _
  rw [Iso.hom_inv_id_assoc, normalized]

set_option backward.isDefEq.respectTransparency false in
theorem reindexPackedWhiskerRight_of_valueProductMaps {A B R : τ} (f : M.obj A ⟶ M.obj B)
    (q : K ⋙ (I) ≅ J)
    (a : K.obj (M.obj A) ≅ Val A) (b : K.obj (M.obj B) ≅ Val B) (r : K.obj (M.obj R) ≅ Val R)
    (src : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map a.hom)
    (dst : (objIso B).hom = (q.app (M.obj B)).inv ≫ (I).map b.hom)
    (sourceProduct : (objIso (product A R)).hom =
      (q.app (M.obj (product A R))).inv ≫ (I).map (chosenBinaryValueProductMap pe K M A R a r))
    (targetProduct : (objIso (product B R)).hom =
      (q.app (M.obj (product B R))).inv ≫ (I).map (chosenBinaryValueProductMap pe K M B R b r)) :
    reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
      whiskerRight (Seed) (reindexHom J M objIso (J.map f)) (Obj R) :=
  (reindexPackedWhiskerRight_eq_iff_targetProduct pe K M J objIso f q a b r src dst sourceProduct).2
    (by rw [targetProduct])


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection
