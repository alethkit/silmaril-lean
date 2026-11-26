module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Diagonal.Defs

/-! # Compare the carried diagonal in the value category before including it -/

public section

universe u v w u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton
open Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.SingletonReification (packedDiagonal packedPair)
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
local notation "fanLimit" => fun (P : τ) => discardPreservingBinaryFanIsLimit (Seed) pe P P (fun h => Or.inl h)

set_option backward.isDefEq.respectTransparency false in
private theorem eq_chosenValueDiagonal (P : τ) (f : Val P ⟶ Val (product P P))
    (left : f.1 ≫ productFst (Seed) P P = 𝟙 (Obj P))
    (right : f.1 ≫ productSnd (Seed) P P = 𝟙 (Obj P)) :
    f = chosenValueDiagonal pe P := by
  apply BinaryFan.IsLimit.hom_ext ((fanLimit) P)
  · trans 𝟙 (Val P)
    · apply WideSubcategory.hom_ext
      exact left
    · exact (BinaryFan.IsLimit.lift_fst ((fanLimit) P) _ _).symm
  · trans 𝟙 (Val P)
    · apply WideSubcategory.hom_ext
      exact right
    · exact (BinaryFan.IsLimit.lift_snd ((fanLimit) P) _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem chosenValueDiagonal_map (P : τ) :
    (I).map (chosenValueDiagonal (Φ := Φ) pe P) = diagonalArrow (Seed) (Obj P) := by
  let d : Obj P ⟶ Obj (product P P) := diagonalArrow (Seed) (Obj P)
  have pairId : pairArrows (Seed) (𝟙 (Obj P)) (𝟙 (Obj P)) = d := by
    have h := congrArg₂ (fun (f g : Obj (product P P) ⟶ Obj (product P P)) => d ≫ f ≫ g)
      ((whiskerRightFunctor (Seed) (Obj P)).map_id (Obj P))
      ((whiskerLeftFunctor (Seed) (Obj P)).map_id (Obj P))
    refine h.trans ?_
    change d ≫ 𝟙 (Obj (product P P)) ≫ 𝟙 (Obj (product P P)) = d
    simp only [Category.comp_id]
  have left : d ≫ productFst (Seed) P P = 𝟙 (Obj P) :=
    (congrArg (· ≫ productFst (Seed) P P) pairId.symm).trans
      (pairing_fst_of_discard (Seed) (𝟙 (Obj P)) (𝟙 (Obj P)) (Category.id_comp _))
  have right : d ≫ productSnd (Seed) P P = 𝟙 (Obj P) :=
    (congrArg (· ≫ productSnd (Seed) P P) pairId.symm).trans
      (pairing_snd_of_discard (Seed) (𝟙 (Obj P)) (𝟙 (Obj P)) (Category.id_comp _))
  have copies : ProjectedCopyingReturn (Seed) pe d :=
    projected_branchValue_mem (Seed) pe
      (Tm.BranchValue.pair (.var (i := 0) rfl) (.var (i := 0) rfl) :
        Tm.BranchValue [P] (Tm.pair (.var 0) (.var 0)) (product P P))
  have discard : d ≫ discardArrow (Seed) (product P P) = discardArrow (Seed) P := by
    rw [← fst_discard (Seed) P P, ← Category.assoc, left, Category.id_comp]
  let guarded : Val P ⟶ Val (product P P) := ⟨d, copies, discard⟩
  exact congrArg (I).map (eq_chosenValueDiagonal pe P guarded left right).symm


variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (K : V ⥤ Values) (M : TypeModel τ V)

set_option backward.isDefEq.respectTransparency false in
theorem eq_chosenValueProductMap_iff (P : τ) (e : K.obj (M.obj P) ≅ Val P)
    (p : K.obj (M.obj (product P P)) ⟶ Val (product P P)) :
    p = chosenValueProductMap pe K M P e ↔
      p ≫ (discardPreservingFan (Seed) pe (fun h => Or.inl h) P P).fst = K.map (fstMap M P P) ≫ e.hom ∧
      p ≫ (discardPreservingFan (Seed) pe (fun h => Or.inl h) P P).snd = K.map (sndMap M P P) ≫ e.hom := by
  have left := BinaryFan.IsLimit.lift_fst ((fanLimit) P) (K.map (fstMap M P P) ≫ e.hom)
    (K.map (sndMap M P P) ≫ e.hom)
  have right := BinaryFan.IsLimit.lift_snd ((fanLimit) P) (K.map (fstMap M P P) ≫ e.hom)
    (K.map (sndMap M P P) ≫ e.hom)
  constructor
  · rintro rfl
    exact ⟨left, right⟩
  · intro h
    exact BinaryFan.IsLimit.hom_ext ((fanLimit) P) (h.1.trans left.symm) (h.2.trans right.symm)

set_option backward.isDefEq.respectTransparency false in
theorem reindexDiagonal_chosenValueProductMap (P : τ) (e : K.obj (M.obj P) ≅ Val P) :
    e.inv ≫ K.map (packedDiagonal M P) ≫ chosenValueProductMap pe K M P e =
      chosenValueDiagonal pe P := by
  have left : packedDiagonal M P ≫ fstMap M P P = 𝟙 _ := by
    simp [packedDiagonal, packedPair, fstMap]
  have right : packedDiagonal M P ≫ sndMap M P P = 𝟙 _ := by
    simp [packedDiagonal, packedPair, sndMap]
  apply BinaryFan.IsLimit.hom_ext ((fanLimit) P)
  · simp only [chosenValueProductMap, chosenBinaryValueProductMap, chosenValueDiagonal, Category.assoc, BinaryFan.IsLimit.lift_fst,
      ← K.map_comp_assoc, left]
    rw [K.map_id, Category.id_comp, Iso.inv_hom_id]
  · simp only [chosenValueProductMap, chosenBinaryValueProductMap, chosenValueDiagonal, Category.assoc, BinaryFan.IsLimit.lift_snd,
      ← K.map_comp_assoc, right]
    rw [K.map_id, Category.id_comp, Iso.inv_hom_id]

variable (J : V ⥤ Comp) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_eq_of_valueProductMap (P : τ) (e : K.obj (M.obj P) ≅ Val P)
    (q : K ⋙ (I) ≅ J)
    (source : (objIso P).hom = (q.app (M.obj P)).inv ≫ (I).map e.hom)
    (target : (objIso (product P P)).hom =
      (q.app (M.obj (product P P))).inv ≫ (I).map (chosenValueProductMap pe K M P e)) :
    reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P) := by
  let f := packedDiagonal M P
  have sourceInv : (objIso P).inv = (I).map e.inv ≫ (q.app (M.obj P)).hom := by
    apply (cancel_mono (objIso P).hom).mp
    rw [Iso.inv_hom_id, source]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rfl
  have commute := q.hom.naturality f
  change (I).map (K.map f) ≫ (q.app (M.obj (product P P))).hom =
    (q.app (M.obj P)).hom ≫ J.map f at commute
  change (objIso P).inv ≫ J.map f ≫ (objIso (product P P)).hom = _
  rw [sourceInv, target]
  have value := congrArg (I).map (reindexDiagonal_chosenValueProductMap pe K M P e)
  rw [chosenValueDiagonal_map] at value
  simpa only [Functor.map_comp, Category.assoc, ← reassoc_of% commute, Iso.hom_inv_id_assoc, f] using value

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_eq_iff_projectedCopying (P : τ)
    (fstAgrees : reindexHom J M objIso (J.map (fstMap M P P)) = productFst (Seed) P P)
    (sndAgrees : reindexHom J M objIso (J.map (sndMap M P P)) = productSnd (Seed) P P) :
    reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P) ↔
      ProjectedCopyingReturn (Seed) pe (reindexHom J M objIso (J.map (packedDiagonal M P))) := by
  let d := reindexHom J M objIso (J.map (packedDiagonal M P))
  have left : d ≫ productFst (Seed) P P = 𝟙 (Obj P) := by
    rw [← fstAgrees]
    have beta : packedDiagonal M P ≫ fstMap M P P = 𝟙 _ := by
      simp [packedDiagonal, packedPair, fstMap]
    simp only [d, reindexHom, Category.assoc, Iso.hom_inv_id_assoc, ← J.map_comp_assoc, beta]
    rw [J.map_id, Category.id_comp, Iso.inv_hom_id]
  have right : d ≫ productSnd (Seed) P P = 𝟙 (Obj P) := by
    rw [← sndAgrees]
    have beta : packedDiagonal M P ≫ sndMap M P P = 𝟙 _ := by
      simp [packedDiagonal, packedPair, sndMap]
    simp only [d, reindexHom, Category.assoc, Iso.hom_inv_id_assoc, ← J.map_comp_assoc, beta]
    rw [J.map_id, Category.id_comp, Iso.inv_hom_id]
  constructor
  · intro h
    rw [h, ← chosenValueDiagonal_map (Φ := Φ) pe P]
    exact (chosenValueDiagonal (Φ := Φ) pe P).2.1
  · intro copies
    have discard : d ≫ discardArrow (Seed) (product P P) = discardArrow (Seed) P := by
      rw [← fst_discard (Seed) P P, ← Category.assoc, left, Category.id_comp]
    let lowered : Val P ⟶ Val (product P P) := ⟨d, copies, discard⟩
    have equal := eq_chosenValueDiagonal pe P lowered left right
    exact (congrArg (I).map equal).trans (chosenValueDiagonal_map pe P)


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal
