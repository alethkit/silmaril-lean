module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Model.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Reification.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Thms

/-! # One-block actual carried reification in the joined quotient -/

public section

universe u v u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open scoped Paper.WithProjectionReturnsAndUnitEta.Reification
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (TypeCategory projection ofType ofRegion ofRegion_eq_iff
  sumIso whiskerRight whiskerLeft whiskerRight_map whiskerLeft_map diagonalArrow iterateSum_map
  sumCofan whiskerLeftFunctor sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom sumCofan_inl_sumIso_hom_assoc sumCofan_inr_sumIso_hom_assoc sumCofanIsColimit emptyIsInitial)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (denoteSingleton_firstTerm packedWhiskerRight packedWhiskerLeft)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
  (guardedCfg_typed realizePackedStep_typed retagPacked_typed duplicateCapture_arrow retagPacked_distributor
    duplicateCapture_typed realizePackedStep_arrow canonicalRegion_eq_guardedCfg_realize exitSum exitDecoder_typed exitDecoder_inl exitDecoder_inr_inl)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model
  (reindexHom carrier carriedStep capturePrefix carriedRoute carriedRoute_factor reindexCoprod_of_injections
    carriedStep_factor_retained packedPair_id_right packedTensorIso reindexRetainLeft_tensorIso
    reindexPackedWhiskerRight_tensorIso exitSum_inl exitSum_inr_inl)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained (packedDistributor packedDistributor_inl packedDistributor_inr distributorRegion_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap inlMap inrMap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (fstTerm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft splitMapCoprod)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Seed)
set_option hygiene false in
local notation "Lit" => Paper.Extension.Singleton.ofRegion (Seed)
set_option hygiene false in
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

theorem fstReturn_eq (X S : τ) :
    Lit (returnOnce_typed (fstTerm (Φ := Φ) X S)) = Lit (productFstBranches X S) :=
  (ofRegion_eq_iff (Seed) _ _).2
    (.extra (returnOnce_typed (fstTerm X S)).hasType (productFstBranches X S).hasType
      (Or.inl (Paper.WithProjectionReturns.Step.fst X S)))

theorem canonicalAssembly_ofRegion {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    canonicalAssembly (Lit he) (Lit (realizePackedStep_typed hb)) = Lit (guardedCfg_typed he hb) := by
  change (F).map (Paper.SingletonReification.SingleCfg.canonicalAssembly
    (Paper.TypeCategory.ofRegion he) (Paper.TypeCategory.ofRegion (realizePackedStep_typed hb) ≫
      (Paper.TypeCategory.sumIso (product X D) (product X S)).hom)) = _
  rw [Paper.SingletonReification.SingleCfg.canonicalAssembly_ofRegion]
  exact (ofRegion_eq_iff (Seed) _ _).2 (.paper (canonicalRegion_eq_guardedCfg_realize he hb))

section Retained

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  (J : V ⥤ Comp) [DistributiveFreydCategory J] (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem reindexPackedWhiskerRight_of_tensorIso {R A B : τ} (f : M.obj A ⟶ M.obj B)
    (source : (packedTensorIso J M objIso A R).hom =
      (J.obj (M.obj A) ◁ (objIso R).hom) ≫ ((objIso A).hom ▷ Obj R))
    (target : (packedTensorIso J M objIso B R).hom =
      (J.obj (M.obj B) ◁ (objIso R).hom) ≫ ((objIso B).hom ▷ Obj R)) :
    reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
      reindexHom J M objIso (J.map f) ▷ Obj R := by
  rw [reindexPackedWhiskerRight_tensorIso]
  apply (cancel_epi (packedTensorIso J M objIso A R).hom).mp
  rw [Iso.hom_inv_id_assoc, source, target]
  unfold reindexHom
  have swap := (FreydCategory.image_central J f).1 (objIso R).hom
  change (J.map f ▷ J.obj (M.obj R)) ≫ (J.obj (M.obj B) ◁ (objIso R).hom) =
    (J.obj (M.obj A) ◁ (objIso R).hom) ≫ (J.map f ▷ Obj R) at swap
  have cancel : ((objIso A).hom ▷ Obj R) ≫
      ((objIso A).inv ≫ J.map f ≫ (objIso B).hom) ▷ Obj R =
      (J.map f ≫ (objIso B).hom) ▷ Obj R := by
    rw [← PremonoidalCategory.comp_whiskerRight, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (J.map f ▷ J.obj (M.obj R)), swap]
  simp only [Category.assoc]
  rw [cancel, PremonoidalCategory.comp_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
private theorem reindexRetainLeft_from_payload {R A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B))
    (payload : J.obj (M.obj A) ≅ Obj A) (out : J.obj (M.obj B) ≅ Obj B)
    (source : (packedTensorIso J M objIso R A).hom =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ payload.hom))
    (target : (packedTensorIso J M objIso R B).hom =
      ((objIso R).hom ▷ J.obj (M.obj B)) ≫ (Obj R ◁ out.hom))
    (swap : (J.obj (M.obj R) ◁ f) ≫ ((objIso R).hom ▷ J.obj (M.obj B)) =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ f)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) f ≫
      J.map (M.productIso R B).inv) =
      Obj R ◁ (payload.inv ≫ f ≫ out.hom) := by
  rw [reindexRetainLeft_tensorIso]
  apply (cancel_epi (packedTensorIso J M objIso R A).hom).mp
  rw [Iso.hom_inv_id_assoc, source, target]
  have cancel : (Obj R ◁ payload.hom) ≫
      Obj R ◁ (payload.inv ≫ f ≫ out.hom) =
      Obj R ◁ (f ≫ out.hom) := by
    rw [← PremonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (J.obj (M.obj R) ◁ f), swap]
  simp only [Category.assoc]
  rw [cancel, PremonoidalCategory.whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
theorem reindexRetainLeft_of_tensorIso {R A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B))
    (source : (packedTensorIso J M objIso R A).hom =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ (objIso A).hom))
    (target : (packedTensorIso J M objIso R B).hom =
      ((objIso R).hom ▷ J.obj (M.obj B)) ≫ (Obj R ◁ (objIso B).hom))
    (swap : (J.obj (M.obj R) ◁ f) ≫ ((objIso R).hom ▷ J.obj (M.obj B)) =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ f)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) f ≫
      J.map (M.productIso R B).inv) =
      Obj R ◁ reindexHom J M objIso f :=
  reindexRetainLeft_from_payload J M objIso f (objIso A) (objIso B) source target swap


theorem reindexRetainLeft_of_valueMap {R A B : τ} (f : M.obj A ⟶ M.obj B)
    (out : J.obj (M.obj B) ≅ Obj B)
    (source : RetainedTensorAgrees J M objIso R A)
    (target : (packedTensorIso J M objIso R B).hom =
      ((objIso R).hom ▷ J.obj (M.obj B)) ≫ (Obj R ◁ out.hom)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) (J.map f) ≫
      J.map (M.productIso R B).inv) =
      Obj R ◁ ((objIso A).inv ≫ J.map f ≫ out.hom) :=
  reindexRetainLeft_from_payload J M objIso (J.map f) (objIso A) out source target
    ((FreydCategory.image_central J f).2 (objIso R).hom).symm

set_option backward.isDefEq.respectTransparency false in
private theorem carriedRoute_eq_iff_of_distributor_injections (X S D : τ)
    (outputInl :
      reindexHom J M objIso (J.map (inlMap M (product X D) (product X S))) =
        (sumCofan (Seed) (product X D) (product X S)).inl)
    (outputInr :
      reindexHom J M objIso (J.map (inrMap M (product X D) (product X S))) =
        (sumCofan (Seed) (product X D) (product X S)).inr)
    (inputInl :
      (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inl ≫
          reindexHom J M objIso (J.map (packedDistributor M X D S)) =
        (sumCofan (Seed) (product X D) (product X S)).inl)
    (inputInr :
      (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inr ≫
          reindexHom J M objIso (J.map (packedDistributor M X D S)) =
        (sumCofan (Seed) (product X D) (product X S)).inr) :
    (carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom) ↔
    reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) =
      whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) := by
  let outputs := sumIso (Seed) (product X D) (product X S)
  have distributor := (Paper.RetainedCase.Chosen.projectedDistributor_eq_iff (Seed) X D S _).2 ⟨inputInl, inputInr⟩
  have output := reindexCoprod_of_injections J M objIso (product X D) (product X S) outputs
    (by simpa only [outputs, sumCofan_inl_sumIso_hom] using congrArg (· ≫ outputs.hom) outputInl)
    (by simpa only [outputs, sumCofan_inr_sumIso_hom] using congrArg (· ≫ outputs.hom) outputInr)
  let distributorIso := (F).mapIso (Paper.RetainedCase.distributorIso (Φ := Φ) X D S)
  have distributorHom : distributorIso.hom = Lit (distributorRegion_typed X D S) := by
    change (F).map (Paper.RetainedCase.distributorIso (Φ := Φ) X D S).hom = _
    rw [Paper.RetainedCase.distributorIso_hom]
  let finish := distributorIso.hom ≫ outputs.hom
  let : IsIso finish := inferInstanceAs (IsIso (distributorIso.hom ≫ outputs.hom))
  have model :
      carriedRoute J M objIso X S D =
        reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) ≫ finish :=
    (carriedRoute_factor J M objIso X S D outputs output).trans
      (congrArg (fun g => reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) ≫
        g ≫ outputs.hom) (distributor.trans distributorHom.symm))
  have guarded :
      whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) ≫ finish =
        Lit (retagPacked_typed X S D) ≫ outputs.hom := by
    dsimp only [finish]
    rw [distributorHom]
    have h := congrArg (fun f => (F).map f ≫ outputs.hom)
      (retagPacked_distributor (Φ := Φ) X S D)
    simpa only [Functor.map_comp, ← whiskerLeft_map, Category.assoc] using! h
  constructor
  · intro agrees
    exact (cancel_mono finish).mp (model.symm.trans (agrees.trans guarded.symm))
  · intro agrees
    exact model.trans ((congrArg (· ≫ finish) agrees).trans guarded)

set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_of_distributor_injections (X S D : τ)
    (outputInl :
      reindexHom J M objIso (J.map (inlMap M (product X D) (product X S))) =
        (sumCofan (Seed) (product X D) (product X S)).inl)
    (outputInr :
      reindexHom J M objIso (J.map (inrMap M (product X D) (product X S))) =
        (sumCofan (Seed) (product X D) (product X S)).inr)
    (decoder :
      reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) =
        whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)))
    (inputInl :
      (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inl ≫
          reindexHom J M objIso (J.map (packedDistributor M X D S)) =
        (sumCofan (Seed) (product X D) (product X S)).inl)
    (inputInr :
      (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inr ≫
          reindexHom J M objIso (J.map (packedDistributor M X D S)) =
        (sumCofan (Seed) (product X D) (product X S)).inr) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom :=
  (carriedRoute_eq_iff_of_distributor_injections J M objIso X S D outputInl outputInr inputInl inputInr).2 decoder

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [DistributiveFreydCategory J] in
private theorem reindexValue_comp {A B C : τ} (f : M.obj A ⟶ M.obj B) (g : M.obj B ⟶ M.obj C) :
    reindexHom J M objIso (J.map f) ≫ reindexHom J M objIso (J.map g) =
      reindexHom J M objIso (J.map (f ≫ g)) := by
  simp only [reindexHom, J.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem reindexPackedWhiskerLeft_from_payload {X A B : τ} (f : M.obj A ⟶ M.obj B)
    (payload : J.obj (M.obj A) ≅ Obj A)
    (source : (packedTensorIso J M objIso X A).hom =
      ((objIso X).hom ▷ J.obj (M.obj A)) ≫ (Obj X ◁ payload.hom))
    (target : RetainedTensorAgrees J M objIso X B) :
    reindexHom J M objIso (J.map (packedWhiskerLeft M X A B f)) =
      whiskerLeft (Seed) (Obj X) (payload.inv ≫ J.map f ≫ (objIso B).hom) := by
  have h := reindexRetainLeft_from_payload J M objIso (J.map f) payload (objIso B) source target
    ((FreydCategory.image_central J f).2 (objIso X).hom).symm
  have retain : retainLeft J (R := M.obj X) (J.map f) = J.map (M.obj X ◁ f) := by
    simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
  simpa only [retain, packedWhiskerLeft, J.map_comp] using! h

set_option backward.isDefEq.respectTransparency false in
private theorem reindexPackedWhiskerLeft {X A B : τ} (f : M.obj A ⟶ M.obj B)
    (source : RetainedTensorAgrees J M objIso X A) (target : RetainedTensorAgrees J M objIso X B) :
    reindexHom J M objIso (J.map (packedWhiskerLeft M X A B f)) =
      whiskerLeft (Seed) (Obj X) (reindexHom J M objIso (J.map f)) :=
  reindexPackedWhiskerLeft_from_payload J M objIso f (objIso A) source target


set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_eq_iff_retainedDecoder (X S D : τ)
    (coordinates : CarriedDistributorCoordinates J M objIso X S D) :
    (carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom) ↔
    reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) =
      whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) := by
  let distrib := packedDistributor M X D S
  apply carriedRoute_eq_iff_of_distributor_injections J M objIso X S D
    coordinates.carriedSum.1 coordinates.carriedSum.2
  · have h := reindexPackedWhiskerLeft J M objIso (inlMap M D S)
      coordinates.tensorResult coordinates.tensorExitSum
    have whisker : reindexHom J M objIso (J.map (packedWhiskerLeft M X D (coprod D S) (inlMap M D S))) =
        (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inl :=
      h.trans (congrArg (whiskerLeft (Seed) (Obj X)) coordinates.exitSum.1)
    refine (congrArg (· ≫ reindexHom J M objIso (J.map distrib)) whisker.symm).trans ?_
    rw [reindexValue_comp]
    simpa only [packedWhiskerLeft, Category.assoc, distrib] using
      (congrArg (fun f => reindexHom J M objIso (J.map f)) (packedDistributor_inl M X D S)).trans coordinates.carriedSum.1
  · have h := reindexPackedWhiskerLeft J M objIso (inrMap M D S)
      coordinates.tensorState coordinates.tensorExitSum
    have whisker : reindexHom J M objIso (J.map (packedWhiskerLeft M X S (coprod D S) (inrMap M D S))) =
        (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inr :=
      h.trans (congrArg (whiskerLeft (Seed) (Obj X)) coordinates.exitSum.2)
    refine (congrArg (· ≫ reindexHom J M objIso (J.map distrib)) whisker.symm).trans ?_
    rw [reindexValue_comp]
    simpa only [packedWhiskerLeft, Category.assoc, distrib] using
      (congrArg (fun f => reindexHom J M objIso (J.map f)) (packedDistributor_inr M X D S)).trans coordinates.carriedSum.2

set_option backward.isDefEq.respectTransparency false in
@[reassoc] private theorem interpretedSumIso_inl (A B : τ)
    (left : J.obj (M.obj A) ≅ Obj A) (right : J.obj (M.obj B) ≅ Obj B) :
    (sumCofan (Seed) A B).inl ≫ (interpretedSumIso J M A B left right).inv =
      left.inv ≫ J.map (inlMap M A B) := by
  simp only [interpretedSumIso, Iso.trans_inv, Iso.symm_inv, asIso_hom, coprod.mapIso_inv,
    Functor.mapIso_inv, Category.assoc, inlMap, J.map_comp]
  rw [← Category.assoc, sumCofan_inl_sumIso_hom (Seed) A B, coprod.inl_map_assoc,
    inl_coprodComparison_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] private theorem interpretedSumIso_inr (A B : τ)
    (left : J.obj (M.obj A) ≅ Obj A) (right : J.obj (M.obj B) ≅ Obj B) :
    (sumCofan (Seed) A B).inr ≫ (interpretedSumIso J M A B left right).inv =
      right.inv ≫ J.map (inrMap M A B) := by
  simp only [interpretedSumIso, Iso.trans_inv, Iso.symm_inv, asIso_hom, coprod.mapIso_inv,
    Functor.mapIso_inv, Category.assoc, inrMap, J.map_comp]
  rw [← Category.assoc, sumCofan_inr_sumIso_hom (Seed) A B, coprod.inr_map_assoc,
    inr_coprodComparison_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem packedExitIso_resultTag (S D : τ) :
    J.map (inlMap M D Silmaril.empty ≫ inrMap M S (coprod D Silmaril.empty)) ≫
        (packedExitIso J M objIso S D).hom =
      (objIso D).hom ≫ (sumCofan (Seed) D Silmaril.empty).inl ≫
        (sumCofan (Seed) S (coprod D Silmaril.empty)).inr := by
  apply (cancel_mono (packedExitIso J M objIso S D).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc, Category.assoc]
  unfold packedExitIso
  rw [interpretedSumIso_inr, interpretedSumIso_inl_assoc, Iso.hom_inv_id_assoc, J.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem retainedPackedExitsAgree_of_injections (X S D : τ)
    (packedSum : SumInjectionsAgree J M objIso S (coprod D Silmaril.empty))
    (resultTag : reindexHom J M objIso (J.map (inlMap M D Silmaril.empty)) =
      (sumCofan (Seed) D Silmaril.empty).inl)
    (packedTensor : RetainedTensorAgrees J M objIso X (packedExitType [S, D])) :
    RetainedPackedExitsAgree J M objIso X S D := by
  have invert {A B : τ} (f : M.obj A ⟶ M.obj B) (i : Obj A ⟶ Obj B)
      (agrees : reindexHom J M objIso (J.map f) = i) :
      i ≫ (objIso B).inv = (objIso A).inv ≫ J.map f := by
    rw [← agrees]
    simp only [reindexHom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have head := invert _ _ packedSum.1
  have rest := invert _ _ packedSum.2
  have result := invert _ _ resultTag
  have inverse : (packedExitIso J M objIso S D).inv = (objIso (coprod S (coprod D Silmaril.empty))).inv := by
    unfold packedExitIso
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Seed) S (coprod D Silmaril.empty))
    · rw [interpretedSumIso_inl]
      exact head.symm
    · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Seed) D Silmaril.empty)
      · rw [interpretedSumIso_inr, rest, interpretedSumIso_inl_assoc,
          ← Category.assoc ((sumCofan (Seed) D Silmaril.empty).inl), result, Category.assoc]
      · exact (emptyIsInitial (Seed)).hom_ext _ _
  have payload : (packedExitIso J M objIso S D).hom = (objIso (coprod S (coprod D Silmaril.empty))).hom := by
    apply (cancel_mono (objIso (coprod S (coprod D Silmaril.empty))).inv).mp
    rw [Iso.hom_inv_id, ← inverse, Iso.hom_inv_id]
  unfold RetainedPackedExitsAgree
  rw [payload]
  exact packedTensor

set_option backward.isDefEq.respectTransparency false in
private theorem exitDecoder_eq_of_sumIso (S D : τ)
    (out : J.obj (M.obj (coprod D S)) ≅ Obj (coprod D S))
    (left : (objIso D).inv ≫ J.map (inlMap M D S) ≫ out.hom = (sumCofan (Seed) D S).inl)
    (right : (objIso S).inv ≫ J.map (inrMap M D S) ≫ out.hom = (sumCofan (Seed) D S).inr) :
    (packedExitIso J M objIso S D).inv ≫ J.map (exitSum M S D) ≫ out.hom =
      Lit (exitDecoder_typed S D) := by
  let tail := coprod D (Silmaril.empty : τ)
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Seed) S tail)
  · trans (sumCofan (Seed) D S).inr
    · rw [packedExitIso, interpretedSumIso_inl_assoc, ← J.map_comp_assoc, exitSum_inl]
      exact right
    · simpa only [Functor.map_comp] using! (congrArg (F).map (exitDecoder_inl (Φ := Φ) S D)).symm
  · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Seed) D Silmaril.empty)
    · trans (sumCofan (Seed) D S).inl
      · rw [packedExitIso, interpretedSumIso_inr_assoc, interpretedSumIso_inl_assoc,
          ← J.map_comp_assoc, ← J.map_comp_assoc, Category.assoc, exitSum_inr_inl]
        exact left
      · simpa only [Functor.map_comp] using! (congrArg (F).map (exitDecoder_inr_inl (Φ := Φ) S D)).symm
    · exact (emptyIsInitial (Seed)).hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
theorem retainedExitDecoder_eq_of_packedExitIso (X S D : τ)
    (exits : SumInjectionsAgree J M objIso D S)
    (target : RetainedTensorAgrees J M objIso X (coprod D S))
    (packed : RetainedPackedExitsAgree J M objIso X S D) :
    reindexHom J M objIso (J.map (packedWhiskerLeft M X (packedExitType [S, D]) (coprod D S) (exitSum M S D))) =
      whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) := by
  have retained := reindexPackedWhiskerLeft_from_payload J M objIso (exitSum M S D)
    (packedExitIso J M objIso S D) packed target
  exact retained.trans (congrArg (whiskerLeft (Seed) (Obj X))
    (exitDecoder_eq_of_sumIso J M objIso S D (objIso (coprod D S)) exits.1 exits.2))


set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_eq_of_coordinates (X S D : τ)
    (coordinates : CarriedDistributorCoordinates J M objIso X S D)
    (packedSum : SumInjectionsAgree J M objIso S (coprod D Silmaril.empty))
    (resultTag :
      reindexHom J M objIso (J.map (inlMap M D Silmaril.empty)) = (sumCofan (Seed) D Silmaril.empty).inl)
    (packedTensor : RetainedTensorAgrees J M objIso X (packedExitType [S, D])) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom := by
  apply (carriedRoute_eq_iff_retainedDecoder J M objIso X S D coordinates).2
  exact retainedExitDecoder_eq_of_packedExitIso J M objIso X S D coordinates.exitSum coordinates.tensorExitSum
    (retainedPackedExitsAgree_of_injections J M objIso X S D packedSum resultTag packedTensor)

set_option backward.isDefEq.respectTransparency false in
private theorem retainedValue_square {X A B : τ} (f : M.obj A ⟶ M.obj B)
    (a : J.obj (M.obj A) ≅ Obj A) (b : J.obj (M.obj B) ≅ Obj B) :
    (J.obj (M.obj X) ◁ J.map f) ≫ ((objIso X).hom ▷ J.obj (M.obj B)) ≫ (Obj X ◁ b.hom) =
      ((objIso X).hom ▷ J.obj (M.obj A)) ≫ (Obj X ◁ a.hom) ≫
        (Obj X ◁ (a.inv ≫ J.map f ≫ b.hom)) := by
  have swap : (J.obj (M.obj X) ◁ J.map f) ≫ ((objIso X).hom ▷ J.obj (M.obj B)) =
      ((objIso X).hom ▷ J.obj (M.obj A)) ≫ (Obj X ◁ J.map f) :=
    ((FreydCategory.image_central J f).2 (objIso X).hom).symm
  rw [← Category.assoc, swap, Category.assoc,
    ← PremonoidalCategory.whiskerLeft_comp, ← PremonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_eq_of_carrierTensor (X S D : τ)
    (tensorState : RetainedTensorAgrees J M objIso X S)
    (tensorResult : RetainedTensorAgrees J M objIso X D)
    (packed : RetainedPackedExitsAgree J M objIso X S D) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom := by
  let K := packedExitType [S, D]
  let U := coprod D S
  let A := product X D
  let B := product X S
  let exactOut := sumIso (Seed) A B
  let modelOut := interpretedSumIso J M A B (objIso A) (objIso B)
  let output := (objIso (coprod A B)).symm ≪≫ modelOut ≪≫ exactOut
  let exitIso := interpretedSumIso J M D S (objIso D) (objIso S)
  let mid := (PremonoidalCategory.whiskerRightIso (objIso X) (J.obj (M.obj U))) ≪≫
    PremonoidalCategory.whiskerLeftIso (Obj X) exitIso
  let T := packedTensorIso J M objIso
  let distrib := J.map (packedDistributor M X D S)
  let split := mid.inv ≫ (T X U).hom ≫ (objIso (product X U)).inv ≫ distrib ≫ modelOut.hom
  have inl : (objIso D).inv ≫ J.map (inlMap M D S) ≫ exitIso.hom = (sumCofan (Seed) D S).inl := by
    simpa only [exitIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using!
      (congrArg (fun (f : Obj D ⟶ _) => f ≫ exitIso.hom)
        (interpretedSumIso_inl J M D S (objIso D) (objIso S))).symm
  have inr : (objIso S).inv ≫ J.map (inrMap M D S) ≫ exitIso.hom = (sumCofan (Seed) D S).inr := by
    simpa only [exitIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using!
      (congrArg (fun (f : Obj S ⟶ _) => f ≫ exitIso.hom)
        (interpretedSumIso_inr J M D S (objIso D) (objIso S))).symm
  have transport {C : τ} (f : M.obj C ⟶ M.obj U) (payload : J.obj (M.obj C) ≅ Obj C)
      (source : (T X C).hom =
        ((objIso X).hom ▷ J.obj (M.obj C)) ≫ (Obj X ◁ payload.hom)) :
      reindexHom J M objIso (J.map (packedWhiskerLeft M X C U f)) ≫ (T X U).inv ≫ mid.hom =
        whiskerLeft (Seed) (Obj X) (payload.inv ≫ J.map f ≫ exitIso.hom) := by
    have retain : retainLeft J (R := M.obj X) (J.map f) = J.map (M.obj X ◁ f) := by
      simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
    have eq := reindexRetainLeft_tensorIso J M objIso (R := X) (J.map f)
    simp only [retain, packedWhiskerLeft, J.map_comp] at eq ⊢
    rw [eq, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    apply (cancel_epi (T X C).hom).mp
    rw [Iso.hom_inv_id_assoc, source]
    simpa only [Category.assoc] using! retainedValue_square J M objIso f payload exitIso
  have guardedDistributor : split = Lit (distributorRegion_typed X D S) := by
    apply (Paper.RetainedCase.Chosen.projectedDistributor_eq_iff (Seed) X D S split).2
    constructor
    · change whiskerLeft (Seed) (Obj X) (sumCofan (Seed) D S).inl ≫ split = _
      rw [← inl, ← transport (inlMap M D S) (objIso D) tensorResult]
      simp only [split, reindexHom, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
        distrib, ← J.map_comp_assoc]
      have law : packedWhiskerLeft M X D U (inlMap M D S) ≫ packedDistributor M X D S = inlMap M A B := by
        simpa only [packedWhiskerLeft, Category.assoc] using packedDistributor_inl M X D S
      rw [law]
      apply (cancel_mono modelOut.inv).mp
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact (interpretedSumIso_inl J M A B (objIso A) (objIso B)).symm
    · change whiskerLeft (Seed) (Obj X) (sumCofan (Seed) D S).inr ≫ split = _
      rw [← inr, ← transport (inrMap M D S) (objIso S) tensorState]
      simp only [split, reindexHom, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
        distrib, ← J.map_comp_assoc]
      have law : packedWhiskerLeft M X S U (inrMap M D S) ≫ packedDistributor M X D S = inrMap M A B := by
        simpa only [packedWhiskerLeft, Category.assoc] using packedDistributor_inr M X D S
      rw [law]
      apply (cancel_mono modelOut.inv).mp
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact (interpretedSumIso_inr J M A B (objIso A) (objIso B)).symm
  have decoder :
      reindexHom J M objIso (J.map (packedWhiskerLeft M X K U (exitSum M S D))) ≫ (T X U).inv ≫ mid.hom =
        whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) := by
    rw [transport (exitSum M S D) (packedExitIso J M objIso S D) packed,
      exitDecoder_eq_of_sumIso J M objIso S D exitIso inl inr]
  have outputAgrees :
      J.map (M.coprodIso A B).inv ≫ (objIso (coprod A B)).hom ≫ output.hom =
        splitMapCoprod J (M.obj A) (M.obj B) ≫ coprod.map (objIso A).hom (objIso B).hom := by
    simp only [output, modelOut, interpretedSumIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Functor.mapIso_hom, ← J.map_comp_assoc,
      J.map_id, Category.id_comp, asIso_inv, coprod.mapIso_hom, splitMapCoprod, exactOut, Category.comp_id]
  rw [carriedRoute_factor J M objIso X S D output outputAgrees]
  have paste :
      (reindexHom J M objIso (J.map (packedWhiskerLeft M X K U (exitSum M S D))) ≫ (T X U).inv ≫ mid.hom) ≫
        split ≫ exactOut.hom =
      reindexHom J M objIso (J.map (packedWhiskerLeft M X K U (exitSum M S D))) ≫
        reindexHom J M objIso distrib ≫ output.hom := by
    simp only [split, reindexHom, output, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc, A, B]
  rw [← paste, decoder, guardedDistributor]
  have h := congrArg (fun f => (F).map f ≫ exactOut.hom) (retagPacked_distributor (Φ := Φ) X S D)
  simpa only [Functor.map_comp, ← whiskerLeft_map, Category.assoc] using! h


set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_eq_of_packedExitIso (X S D : τ)
    (_exits : SumInjectionsAgree J M objIso D S)
    (tensorState : RetainedTensorAgrees J M objIso X S)
    (tensorResult : RetainedTensorAgrees J M objIso X D)
    (_tensorExits : RetainedTensorAgrees J M objIso X (coprod D S))
    (packed : RetainedPackedExitsAgree J M objIso X S D) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom :=
  carriedRoute_eq_of_carrierTensor J M objIso X S D tensorState tensorResult packed

end Retained

section Model

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

theorem fstProducer_denote_iff [RegionTypingCoherent (Φ := Φ) J M] (X S : τ) :
    (reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) X S)).hasType) =
      Lit (returnOnce_typed (fstTerm X S))) ↔
    reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S) := by
  rw [denoteSingleton_firstTerm J M, fstReturn_eq]

set_option backward.isDefEq.respectTransparency false in
private theorem capturePrefix_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    capturePrefix J M objIso X S = Lit (duplicateCapture_typed X S) := by
  let P := product X S
  let f := fstMap M X S
  change reindexHom J M objIso (J.map (Paper.SingletonReification.packedPair M P X P f (𝟙 _))) = _
  rw [packedPair_id_right, J.map_comp]
  have reindex_comp :
      reindexHom J M objIso (J.map (Paper.SingletonReification.packedDiagonal M P) ≫
        J.map (Paper.SingletonReification.packedWhiskerRight M P P X f)) =
        reindexHom J M objIso (J.map (Paper.SingletonReification.packedDiagonal M P)) ≫
        reindexHom J M objIso (J.map (Paper.SingletonReification.packedWhiskerRight M P P X f)) := by
    unfold reindexHom
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reindex_comp, cmp.diagonal, cmp.fstWhisker, cmp.fstProducer]
  have eq := congrArg (fun f => (F).map f) (duplicateCapture_arrow (Φ := Φ) X S)
  simpa only [Functor.map_comp, ← whiskerRight_map, diagonalArrow] using! eq

set_option backward.isDefEq.respectTransparency false in
theorem actualCarriedStep_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    actualCarriedStep J M objIso hb =
      Lit (realizePackedStep_typed hb) ≫ (sumIso (Seed) (product X D) (product X S)).hom := by
  unfold actualCarriedStep
  rw [carriedStep_factor_retained, capturePrefix_eq J M objIso cmp, cmp.block, cmp.route]
  have h := congrArg (fun f => (F).map f ≫ (sumIso (Seed) (product X D) (product X S)).hom)
    (realizePackedStep_arrow hb)
  simpa only [Functor.map_comp, ← whiskerLeft_map, Category.assoc] using! h

set_option backward.isDefEq.respectTransparency false in
theorem canonicalIterate_actual_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    canonicalIterate (actualCarriedStep J M objIso hb) =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) := by
  rw [actualCarriedStep_eq J M objIso cmp]
  let exits := sumIso (Seed) (product X D) (product X S)
  change Paper.Extension.Singleton.iterateSum (Seed) ((Lit (realizePackedStep_typed hb) ≫ exits.hom) ≫ exits.inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, iterateSum_map, Paper.TypeCategory.iterateSum_ofRegion]

theorem actualCarriedIteration_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb)
    (iteration : TransportedIterationAgrees J M objIso hb) :
    let actual := contextualStep J (Paper.SingletonReification.SingleCfg.blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X D
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  iteration.trans (canonicalIterate_actual_eq J M objIso cmp)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalAssembly_actual_eq {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    canonicalAssembly (Lit he)
      (actualCarriedStep J M objIso hb ≫ (sumIso (Seed) (product X D) (product X S)).inv) =
      Lit (guardedCfg_typed he hb) := by
  rw [actualCarriedStep_eq J M objIso cmp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact canonicalAssembly_ofRegion he hb

end Model

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration
