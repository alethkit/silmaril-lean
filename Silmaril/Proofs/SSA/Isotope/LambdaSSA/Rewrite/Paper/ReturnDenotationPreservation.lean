module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Producer.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationWhisker
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Iteration.Thms

import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Model coordinates for a sound singleton quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservation

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

open Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton (ofType ofRegion projection iterateSum productFst productSnd discardArrow
  diagonalArrow sumCofan whiskerLeftFunctor whiskerRightFunctor whiskerLeft_map braidIso braid_naturality_left
  iterateSum_map denoteFunctor_map_ofRegion)
open Paper.Extension.Singleton.Generation
open CfgEta.TypeCategory (returnRegion_typed)

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  (sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M)

set_option hygiene false in
local notation "F" => Paper.Extension.Singleton.denoteFunctor J M shared sound
set_option hygiene false in
local notation "T" => Coordinates.ofModel J M
set_option hygiene false in
local notation "exactObj" => (fun A : τ => Iso.refl (J.obj (M.obj A)))


open CartesianMonoidalCategory (lift)
open CfgEta.TypeCategory (productFstBranches productSndBranches)
open CfgEta.TypeCategory.ConstructorReification (fstMap sndMap unitMap)
open Paper.SingletonReification (packedDiagonal packedSwap)
open Silmaril.Isotope.LetIter.Semantics.Categorical (pair_maps_eq_map_lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open SingletonDispatcher (labelInject_payload)

local notation "Obj" => ofType (Seed)
local notation "map" => mapInCoordinates (Seed) (F) (exactObj)

set_option backward.isDefEq.respectTransparency false in
theorem map_coordinates {A B : τ} (f : Obj A ⟶ Obj B) : map f = (F).map f := by
  change 𝟙 _ ≫ (F).map f ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem map_discard (A : τ) : map (discardArrow (Seed) A) = (T).discard A := by
  rw [map_coordinates]
  change (F).map (ofRegion (Seed) (.br (ℓ := 0) rfl (.unit (Γ := [A])))) = J.map (unitMap M A)
  rw [denoteFunctor_map_ofRegion J M shared sound, denoteSingletonRegion_br J M Denotes.unit, ← J.map_comp]
  congr 1
  rw [unitMap, ← Category.assoc]
  congr 1
  exact Subsingleton.elim _ _

theorem map_fst (A B : τ) : map (productFst (Seed) A B) = (T).fst A B := by
  rw [map_coordinates, productFst, denoteFunctor_map_ofRegion J M shared sound]
  exact Paper.SingletonReification.denoteSingleton_productFst J M A B

theorem map_snd (A B : τ) : map (productSnd (Seed) A B) = (T).snd A B := by
  rw [map_coordinates, productSnd, denoteFunctor_map_ofRegion J M shared sound]
  exact ReturnDenotationWhisker.denoteSingleton_productSnd J M A B

set_option backward.isDefEq.respectTransparency false in
theorem map_copy (A : τ) : map (diagonalArrow (Seed) (Obj A)) = (T).copy A := by
  rw [map_coordinates]
  change (F).map (ofRegion (Seed) (Paper.RetainedLet.diagonal_typed A)) = J.map (packedDiagonal M A)
  rw [denoteFunctor_map_ofRegion J M shared sound, denoteSingletonRegion_br J M (.pair (.var (i := 0) rfl) (.var (i := 0) rfl))]
  rw [pair_maps_eq_map_lift, ← J.map_comp_assoc, ← J.map_comp]
  congr 1
  simp only [lookup, ctxObj, CartesianMonoidalCategory.comp_lift,
    CartesianMonoidalCategory.leftUnitor_inv_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem map_inl (A B : τ) : map (sumCofan (Seed) A B).inl =
    coprod.inl ≫ ((T).sumIso A B).inv := by
  rw [map_coordinates]
  change (F).map ((projection (Seed)).map (Paper.TypeCategory.sumCofan A B).inl) = _
  rw [Paper.TypeCategory.sumCofan_inl]
  rw [denoteFunctor_map_ofRegion J M shared sound, denoteSingletonRegion_br J M (.inl (.var (i := 0) rfl))]
  simp only [lookup, ctxObj, ← J.map_comp, CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]
  change J.map (coprod.inl ≫ (M.coprodIso A B).inv) =
    coprod.inl ≫ ((PreservesColimitPair.iso J (M.obj A) (M.obj B)).hom ≫ J.map (M.coprodIso A B).inv)
  rw [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, ← J.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem map_inr (A B : τ) : map (sumCofan (Seed) A B).inr =
    coprod.inr ≫ ((T).sumIso A B).inv := by
  rw [map_coordinates]
  change (F).map ((projection (Seed)).map (Paper.TypeCategory.sumCofan A B).inr) = _
  rw [Paper.TypeCategory.sumCofan_inr]
  rw [denoteFunctor_map_ofRegion J M shared sound, denoteSingletonRegion_br J M (.inr (.var (i := 0) rfl))]
  simp only [lookup, ctxObj, ← J.map_comp, CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]
  change J.map (coprod.inr ≫ (M.coprodIso A B).inv) =
    coprod.inr ≫ ((PreservesColimitPair.iso J (M.obj A) (M.obj B)).hom ≫ J.map (M.coprodIso A B).inv)
  rw [PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, ← J.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem map_primitive (p : Φ) : map (primitive (Seed) p) = InstructionModel.denote (J := J) (M := M) p := by
  rw [map_coordinates]
  let ha : Tm.HasType [(instrSrc p : τ)] (.op p (.var 0)) (instrTrg p : τ) := .op (.var rfl)
  change (F).map (ofRegion (Seed) (Paper.RetainedLet.returnOnce_typed ha)) = _
  rw [denoteFunctor_map_ofRegion J M shared sound, Paper.RetainedLet.returnOnce_denotation J M ha (.op (.var (i := 0) rfl))]
  simp only [lookup, ctxObj, ← J.map_comp_assoc, CartesianMonoidalCategory.leftUnitor_inv_snd, J.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem map_left (Y : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    map ((whiskerLeftFunctor (Seed) (Obj Y)).map f) =
      ((T).tensorIso Y A).hom ≫ (J.obj (M.obj Y) ◁ map f) ≫ ((T).tensorIso Y B).inv := by
  rw [map_coordinates, map_coordinates]
  refine Quot.inductionOn f fun (g : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B) => ?_
  obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
  change (F).map ((whiskerLeftFunctor (Seed) (Obj Y)).map
    ((projection (Seed)).map (Paper.TypeCategory.ofRegion hr))) = _
  rw [whiskerLeft_map, Paper.TypeCategory.whiskerLeft_ofRegion Y hr,
    denoteFunctor_map_ofRegion J M shared sound (CfgEta.TypeCategory.whiskerLeftRegion_typed Y hr)]
  change _ = ((T).tensorIso Y A).hom ≫ (J.obj (M.obj Y) ◁ (F).map (ofRegion (Seed) hr)) ≫ ((T).tensorIso Y B).inv
  rw [denoteFunctor_map_ofRegion J M shared sound hr,
    ReturnDenotationWhisker.denoteSingleton_whiskerLeft J M shared Y hr]
  simp only [Coordinates.ofModel, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, retainLeft, PremonoidalCategory.leftTensor,
    PremonoidalCategory.id_whiskerRight, Category.id_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem map_braid (A B : τ) :
    (F).map (braidIso (Seed) (Obj A) (Obj B)).hom =
      ((T).tensorIso A B).hom ≫ (BraidedPremonoidalCategory.braiding (J.obj (M.obj A)) (J.obj (M.obj B))).hom ≫
        ((T).tensorIso B A).inv := by
  change (F).map (ofRegion (Seed) (Paper.TypeCategory.braidBranches A B)) = _
  rw [denoteFunctor_map_ofRegion J M shared sound, Paper.SingletonReification.denoteSingleton_braid J M]
  simp only [packedSwap, J.map_comp, Coordinates.ofModel, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  rw [← reassoc_of% (Functor.StrongSymmetricPremonoidal.braiding (J := J) (M.obj A) (M.obj B)),
    Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem map_right (Y : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    map ((whiskerRightFunctor (Seed) (Obj Y)).map f) =
      ((T).tensorIso A Y).hom ≫ (map f ▷ J.obj (M.obj Y)) ≫ ((T).tensorIso B Y).inv := by
  rw [map_coordinates, map_coordinates]
  apply (cancel_mono ((F).map (braidIso (Seed) (Obj B) (Obj Y)).hom)).mp
  change (F).map ((whiskerRightFunctor (Seed) (Obj Y)).map f) ≫
    (F).map (braidIso (Seed) (Obj B) (Obj Y)).hom = _
  rw [← (F).map_comp, braid_naturality_left, (F).map_comp]
  have left := map_left J M shared sound Y f
  simp only [map_coordinates] at left
  rw [map_braid, left, map_braid]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, BraidedPremonoidalCategory.naturality_left_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The lifted interpretation preserves guarded iteration on the exact
result-or-state sum used by the generation theorem. -/
theorem map_iterate {A B : τ}
    (f : ofType (Seed) A ⟶ ofType (Seed) (coprod B A)) :
    (F).map (iterateSum (Seed) f) =
      CategoryTheory.iterate ((F).map f ≫ ((T).sumIso B A).hom) :=
  Quot.inductionOn f (fun g => by
    change (F).map (iterateSum (Seed) ((projection (Seed)).map g)) = _
    rw [iterateSum_map]
    let base := Paper.TypeCategory.denoteFunctor (Φ := Φ) J M shared
    change base.map (Paper.TypeCategory.iterateSum g) =
      CategoryTheory.iterate (base.map g ≫ ((T).sumIso B A).hom)
    have comparison :
        PreservesColimitPair.iso J (M.obj B) (M.obj A) =
          asIso (coprodComparison J (M.obj B) (M.obj A)) :=
      Iso.ext (PreservesColimitPair.iso_hom J (M.obj B) (M.obj A))
    simpa only [Coordinates.ofModel, comparison, Paper.TypeCategory.denoteExactSumIso]
      using Paper.TypeCategory.denoteFunctor_map_iterateSum J M shared (A := A) (B := B) g)

set_option backward.isDefEq.respectTransparency false in
theorem preserves : Preserves (Seed) (F) (exactObj) (T) where
  discard := map_discard J M shared sound
  fst := map_fst J M shared sound
  snd := map_snd J M shared sound
  copy := map_copy J M shared sound
  inl := map_inl J M shared sound
  inr := map_inr J M shared sound
  left := map_left J M shared sound
  right := map_right J M shared sound
  iterate f := by
    rw [map_coordinates, map_coordinates]
    exact map_iterate J M shared sound f

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservation
