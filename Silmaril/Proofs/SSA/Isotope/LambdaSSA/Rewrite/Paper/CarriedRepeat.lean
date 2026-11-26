module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

/-! # Routing the interpreted repeat arm of a packed block -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedRepeat

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.SingletonReification.SingleCfg (blockComputation carriedIso labelPayloadIso)
open CfgEta.TypeCategory.ConstructorReification (sndMap inlMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel contextualStep retainEnvironment)
open CartesianMonoidalCategory (fst snd)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
  (labelAppendSplit_zero route_inr payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (retainEnvironment_map retainEnvironment_comp)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

set_option backward.isDefEq.respectTransparency false in
theorem contextualStep_repeat_of_packed {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (payload : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj S))
    (tagged : denoteSingletonRegion J M hb.hasType =
      payload ≫ J.map (inlMap M S (coprod D Silmaril.empty))) :
    let E := ctxObj M [X]
    let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
    contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      retainEnvironment J (fst E (labelObj M [S])) f ≫ coprod.inr := by
  let E := ctxObj M [X]
  let repeatIn : labelObj M [S] ⟶ labelObj M [D] ⨿ labelObj M [S] := coprod.inr
  let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
  have decode : inlMap M S (coprod D Silmaril.empty) ≫ unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D] =
      labelInject M 0 (L := [S]) rfl ≫ repeatIn := by
    simp only [inlMap, packedExitType, unpackLabel, Category.assoc, Iso.inv_hom_id_assoc, coprod.inl_desc_assoc]
    exact labelAppendSplit_zero M S [D]
  dsimp only
  unfold contextualStep blockComputation
  have split : J.map (carriedIso M X S).hom ≫ denoteSingletonRegion J M hb.hasType ≫
      J.map (unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D]) = f ≫ J.map repeatIn := by
    simp only [tagged, f, Category.assoc, ← J.map_comp, decode]
  rw [split, retainEnvironment_comp]
  have retain : retainLeft J (R := E) (J.map repeatIn) = J.map (E ◁ repeatIn) := by
    simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
  rw [Category.assoc, retain, route_inr J]

set_option backward.isDefEq.respectTransparency false in
theorem contextualStep_identityRepeat_of_packed {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (pureRepeat : denoteSingletonRegion J M hb.hasType =
      J.map (sndMap M X S ≫ inlMap M S (coprod D Silmaril.empty))) :
    contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      coprod.inr := by
  let p := J.map (sndMap M X S)
  have step := contextualStep_repeat_of_packed J M hb p
    (by rw [pureRepeat, Functor.map_comp])
  dsimp only at step
  have pureSnd : (carriedIso M X S).hom ≫ sndMap M X S ≫ labelInject M 0 (L := [S]) rfl =
      snd (ctxObj M [X]) (labelObj M [S]) := by
    simp only [carriedIso, sndMap, Iso.trans_hom, MonoidalCategory.whiskerLeftIso_hom,
      MonoidalCategory.whiskerRightIso_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      CartesianMonoidalCategory.whiskerRight_snd_assoc]
    change (ctxObj M [X] ◁ singletonLabelPayload M S) ≫ snd (ctxObj M [X]) (M.obj S) ≫
      labelInject M 0 (L := [S]) rfl = _
    rw [CartesianMonoidalCategory.whiskerLeft_snd_assoc, payload_labelInject, Category.comp_id]
  rw [step]
  simp only [p, ← J.map_comp, pureSnd, retainEnvironment_map,
    CartesianMonoidalCategory.lift_fst_snd, J.map_id, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedRepeat
