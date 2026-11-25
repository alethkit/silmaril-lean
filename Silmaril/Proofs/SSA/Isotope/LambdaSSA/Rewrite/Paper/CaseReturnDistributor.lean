module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Distributor.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Interchange.Thms
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms

/-! # Value witnesses for the guarded distributor -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton (DiscardPreservingReturn ProjectedPureReturn projected_branchValue_mem
  projectedPureReturn_pairArrows productFst productSnd fst_discard snd_discard discardArrow pairArrows
  map_pairArrows pairing_fst_of_discard sumCofan sumCofanIsColimit whiskerLeftFunctor whiskerLeft_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair exactCopair_mem_iff sum_inl_mem sum_inr_mem)
open Paper.RetainedCase (distributorIso distributorIso_hom)
open Paper.RetainedCase.Chosen (projectedDistributor_eq_iff)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open CategoryTheory CategoryTheory.Limits

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseReturnDistributor

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns (guardedDistributorIso valueCartesian distributorTerm
  distributorTerm_typed distributorTerm_pure)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Φ := Φ) Seed
set_option hygiene false in
local notation "P" => Paper.WithCaseReturns.projection (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Values" => Paper.WithCaseReturns.ValueCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Q" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "W" => whiskerLeftFunctor Seed
set_option hygiene false in
local notation "cf" => sumCofan Seed
set_option hygiene false in
local notation "Mem" => DiscardPreservingReturn Seed pe
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

private theorem branch_mem {A B : τ} {a : Tm Φ} (ha : Tm.BranchValue [A] a B) :
    Mem (Paper.Extension.Singleton.ofRegion Seed (.br (ℓ := 0) rfl ha)) :=
  ⟨projected_branchValue_mem Seed pe ha,
    (Functor.map_comp (P) _ _).symm.trans
      (congrArg (P).map (Paper.TypeCategory.discard_comp_branchValue ha))⟩

private theorem fst_mem (A B : τ) : Mem (productFst Seed A B) :=
  ⟨Paper.WithProjectionReturns.fst_mem pe Seed (Paper.WithCaseReturns.includeProjection pe) A B,
    fst_discard Seed A B⟩

private theorem snd_mem (A B : τ) : Mem (productSnd Seed A B) :=
  ⟨Paper.WithProjectionReturns.snd_mem pe Seed (Paper.WithCaseReturns.includeProjection pe) A B,
    snd_discard Seed A B⟩

set_option backward.isDefEq.respectTransparency false in
private theorem pair_mem {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : Mem f) (hg : Mem g) : Mem (pairArrows Seed f g) := by
  refine ⟨⟨projectedPureReturn_pairArrows Seed pe hf.1.1 hg.1.1, ?_⟩, ?_⟩
  · obtain ⟨f₀, hf₀, rfl⟩ := hf.1.2
    obtain ⟨g₀, hg₀, rfl⟩ := hg.1.2
    exact ⟨_, Paper.TypeCategory.centralCopies_pair hf₀ hg₀, map_pairArrows Seed f₀ g₀⟩
  · change pairArrows Seed f g ≫ discardArrow Seed (A ×ₜ B) = discardArrow Seed X
    rw [← fst_discard Seed A B, ← Category.assoc, pairing_fst_of_discard Seed f g hg.2]
    exact hf.2

set_option backward.isDefEq.respectTransparency false in
private theorem base_whisker_pair (X : τ) {A B : τ}
    (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B) :
    Paper.TypeCategory.whiskerLeft (Paper.TypeCategory.ofType X) f =
      Paper.TypeCategory.pairArrows (Paper.TypeCategory.ofRegion (CfgEta.TypeCategory.productFstBranches X A))
        (Paper.TypeCategory.ofRegion (CfgEta.TypeCategory.productSndBranches X A) ≫ f) := by
  let fst := Paper.TypeCategory.ofRegion (Φ := Φ) (CfgEta.TypeCategory.productFstBranches X A)
  let snd := Paper.TypeCategory.ofRegion (Φ := Φ) (CfgEta.TypeCategory.productSndBranches X A)
  have h : Paper.TypeCategory.pairArrows fst (snd ≫ f) =
      Paper.TypeCategory.pairArrows fst snd ≫ Paper.TypeCategory.whiskerLeft (Paper.TypeCategory.ofType X) f := by
    simp only [Paper.TypeCategory.pairArrows, Paper.TypeCategory.whiskerLeft_comp, Category.assoc]
  rw [h, Paper.TypeCategory.pairArrows_projections, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem whisker_pair (X : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    (W (Obj X)).map f = pairArrows Seed (productFst Seed X A) (productSnd Seed X A ≫ f) := by
  obtain ⟨f₀, rfl⟩ := (P).map_surjective (Y := Paper.TypeCategory.ofType B) f
  rw [whiskerLeft_map, base_whisker_pair X f₀, map_pairArrows, Functor.map_comp]

private theorem whisker_mem (X : τ) {A B : τ} {f : Obj A ⟶ Obj B} (h : Mem f) :
    Mem ((W (Obj X)).map f) := by
  rw [whisker_pair pe X f]
  exact pair_mem pe (fst_mem pe X A) ((Mem).comp_mem _ _ (snd_mem pe X A) h)

private theorem copair_mem {A B : τ} {D : Q} {f : Obj A ⟶ D} {g : Obj B ⟶ D}
    (hf : Mem f) (hg : Mem g) : Mem (exactCopair Seed f g) :=
  (exactCopair_mem_iff Seed pe hf hg).2 (Paper.WithCaseReturns.copairPure pe hf hg)

set_option backward.isDefEq.respectTransparency false in
private theorem delta_legs (X A B : τ) :
    (W (Obj X)).map (cf A B).inl ≫ (guardedDistributorIso pe X A B).hom = (cf (X ×ₜ A) (X ×ₜ B)).inl ∧
    (W (Obj X)).map (cf A B).inr ≫ (guardedDistributorIso pe X A B).hom = (cf (X ×ₜ A) (X ×ₜ B)).inr := by
  have h := (projectedDistributor_eq_iff Seed X A B _).1 rfl
  simpa only [guardedDistributorIso, Functor.mapIso_hom, distributorIso_hom] using h

set_option backward.isDefEq.respectTransparency false in
theorem forward_mem (X A B : τ) : Mem (guardedDistributorIso pe X A B).inv := by
  let l := (W (Obj X)).map (cf A B).inl
  let r := (W (Obj X)).map (cf A B).inr
  have h : (guardedDistributorIso pe X A B).inv = exactCopair Seed l r := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed (X ×ₜ A) (X ×ₜ B))
    · have hl : (cf (X ×ₜ A) (X ×ₜ B)).inl ≫ exactCopair Seed l r = l :=
        (sumCofanIsColimit Seed (X ×ₜ A) (X ×ₜ B)).fac (BinaryCofan.mk l r) ⟨WalkingPair.left⟩
      rw [hl, ← (delta_legs (Φ := Φ) pe X A B).1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · have hl : (cf (X ×ₜ A) (X ×ₜ B)).inr ≫ exactCopair Seed l r = r :=
        (sumCofanIsColimit Seed (X ×ₜ A) (X ×ₜ B)).fac (BinaryCofan.mk l r) ⟨WalkingPair.right⟩
      rw [hl, ← (delta_legs (Φ := Φ) pe X A B).2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  exact copair_mem pe (whisker_mem pe X (sum_inl_mem Seed pe A B)) (whisker_mem pe X (sum_inr_mem Seed pe A B))

open Paper.Extension.Singleton (leftUnitIsoOfEta unit_eta_of_include leftUnit_naturality)

private def unitIso (A : τ) : Obj (U ×ₜ A) ≅ Obj A :=
  leftUnitIsoOfEta Seed (unit_eta_of_include Seed (Paper.WithCaseReturns.includeUnit pe)) (Obj A)

private theorem unit_projection_mem (A : τ) : Mem (unitIso pe A).hom :=
  snd_mem pe U A

private theorem unit_section_mem (A : τ) : Mem (unitIso pe A).inv :=
  branch_mem pe (.pair .unit (.var (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
theorem inverse_mem_at_unit (A B : τ) : Mem (guardedDistributorIso pe U A B).hom := by
  let l := (unitIso pe A).inv ≫ (cf (U ×ₜ A) (U ×ₜ B)).inl
  let r := (unitIso pe B).inv ≫ (cf (U ×ₜ A) (U ×ₜ B)).inr
  let d := exactCopair Seed l r
  have hl : (cf A B).inl ≫ d = l :=
    (sumCofanIsColimit Seed A B).fac (BinaryCofan.mk l r) ⟨WalkingPair.left⟩
  have hr : (cf A B).inr ≫ d = r :=
    (sumCofanIsColimit Seed A B).fac (BinaryCofan.mk l r) ⟨WalkingPair.right⟩
  have eq : (unitIso pe (A ⊕ₜ B)).hom ≫ d = (guardedDistributorIso pe U A B).hom := by
    rw [Functor.mapIso_hom, distributorIso_hom]
    apply (projectedDistributor_eq_iff Seed U A B _).2
    constructor
    · have n : (W (Obj U)).map (cf A B).inl ≫ (unitIso pe (A ⊕ₜ B)).hom =
          (unitIso pe A).hom ≫ (cf A B).inl := leftUnit_naturality Seed (cf A B).inl
      rw [← Category.assoc, n, Category.assoc, hl]
      exact Iso.hom_inv_id_assoc _ _
    · have n : (W (Obj U)).map (cf A B).inr ≫ (unitIso pe (A ⊕ₜ B)).hom =
          (unitIso pe B).hom ≫ (cf A B).inr := leftUnit_naturality Seed (cf A B).inr
      rw [← Category.assoc, n, Category.assoc, hr]
      exact Iso.hom_inv_id_assoc _ _
  rw [← eq]
  exact (Mem).comp_mem _ _ (unit_projection_mem pe _)
    (copair_mem pe
      ((Mem).comp_mem _ _ (unit_section_mem pe A) (sum_inl_mem Seed pe _ _))
      ((Mem).comp_mem _ _ (unit_section_mem pe B) (sum_inr_mem Seed pe _ _)))

/-- Lift the exact guarded comparison once its inverse is certified as a value. -/
noncomputable def valueDistributorOfInverse (X A B : τ) (h : Mem (guardedDistributorIso pe X A B).hom) :
    (⟨Obj ((X ×ₜ A) ⊕ₜ (X ×ₜ B))⟩ : Values) ≅ ⟨Obj (X ×ₜ (A ⊕ₜ B))⟩ where
  hom := ⟨_, forward_mem pe X A B⟩
  inv := ⟨_, h⟩
  hom_inv_id := (Paper.WithCaseReturns.values pe).map_injective (guardedDistributorIso pe X A B).inv_hom_id
  inv_hom_id := (Paper.WithCaseReturns.values pe).map_injective (guardedDistributorIso pe X A B).hom_inv_id

noncomputable def valueDistributorAtUnit (A B : τ) :
    (⟨Obj ((U ×ₜ A) ⊕ₜ (U ×ₜ B))⟩ : Values) ≅ ⟨Obj (U ×ₜ (A ⊕ₜ B))⟩ :=
  valueDistributorOfInverse pe U A B (inverse_mem_at_unit pe A B)

theorem map_valueDistributorOfInverse (X A B : τ) (h : Mem (guardedDistributorIso pe X A B).hom) :
    (Paper.WithCaseReturns.values pe).mapIso (valueDistributorOfInverse pe X A B h) =
      (guardedDistributorIso pe X A B).symm :=
  Iso.ext rfl

theorem map_valueDistributorAtUnit (A B : τ) :
    (Paper.WithCaseReturns.values (Φ := Φ) pe).mapIso (valueDistributorAtUnit pe A B) =
      (guardedDistributorIso pe U A B).symm :=
  map_valueDistributorOfInverse pe U A B _

open Paper.Extension.Singleton (pairing_snd_of_discard)
open Paper.Extension.Singleton.ValueCoproducts (valueSumCofan valueSumIsColimit)

attribute [local instance] valueCartesian
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
theorem value_whisker (X : τ) {A B : τ}
    (f : (⟨Obj A⟩ : Values) ⟶ ⟨Obj B⟩) :
    (Paper.WithCaseReturns.values pe).map ((⟨Obj X⟩ : Values) ◁ f) =
      (W (Obj X)).map f.hom := by
  have h := whisker_mem pe X f.property
  let g : (⟨Obj (X ×ₜ A)⟩ : Values) ⟶ ⟨Obj (X ×ₜ B)⟩ := ⟨_, h⟩
  have e : (⟨Obj X⟩ : Values) ◁ f = g :=
    CartesianMonoidalCategory.hom_ext ((⟨Obj X⟩ : Values) ◁ f) g ?_ ?_
  · exact congrArg (Paper.WithCaseReturns.values pe).map e
  · rw [CartesianMonoidalCategory.whiskerLeft_fst]
    apply (Paper.WithCaseReturns.values pe).map_injective
    change productFst Seed X A = (W (Obj X)).map f.hom ≫ productFst Seed X B
    rw [whisker_pair]
    exact (pairing_fst_of_discard Seed _ _ ((Mem).comp_mem _ _ (snd_mem pe X A) f.property).2).symm
  · rw [CartesianMonoidalCategory.whiskerLeft_snd]
    apply (Paper.WithCaseReturns.values pe).map_injective
    change productSnd Seed X A ≫ f.hom = (W (Obj X)).map f.hom ≫ productSnd Seed X B
    rw [whisker_pair]
    exact (pairing_snd_of_discard Seed _ _ (fst_mem pe X A).2).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def whiskeredValueSumIsColimit (X A B : τ) (h : Mem (guardedDistributorIso pe X A B).hom) :
    IsColimit (BinaryCofan.map (MonoidalCategory.tensorLeft (⟨Obj X⟩ : Values))
      (valueSumCofan Seed pe A B)) := by
  apply (valueSumIsColimit Seed pe (Paper.WithCaseReturns.copairPure pe) (X ×ₜ A) (X ×ₜ B)).ofIsoColimit
  refine BinaryCofan.ext (valueDistributorOfInverse pe X A B h) ?_ ?_
  · apply (Paper.WithCaseReturns.values pe).map_injective
    change (cf (X ×ₜ A) (X ×ₜ B)).inl =
      (Paper.WithCaseReturns.values pe).map ((⟨Obj X⟩ : Values) ◁ (valueSumCofan Seed pe A B).inl) ≫
        (guardedDistributorIso pe X A B).hom
    rw [value_whisker]
    exact (delta_legs (Φ := Φ) pe X A B).1.symm
  · apply (Paper.WithCaseReturns.values pe).map_injective
    change (cf (X ×ₜ A) (X ×ₜ B)).inr =
      (Paper.WithCaseReturns.values pe).map ((⟨Obj X⟩ : Values) ◁ (valueSumCofan Seed pe A B).inr) ≫
        (guardedDistributorIso pe X A B).hom
    rw [value_whisker]
    exact (delta_legs (Φ := Φ) pe X A B).2.symm

set_option backward.isDefEq.respectTransparency false in
private theorem valueWhiskerPreservesBinary (X : τ) (h : ∀ A B : τ, Mem (guardedDistributorIso pe X A B).hom) :
    PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft (⟨Obj X⟩ : Values)) where
  preservesColimit {K} := by
    let A : τ := (K.obj ⟨WalkingPair.left⟩).obj.as
    let B : τ := (K.obj ⟨WalkingPair.right⟩).obj.as
    let F := MonoidalCategory.tensorLeft (⟨Obj X⟩ : Values)
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) F :=
      preservesColimit_of_preserves_colimit_cocone
        (valueSumIsColimit Seed pe (Paper.WithCaseReturns.copairPure pe) A B)
        (BinaryCofan.isColimitMapCoconeEquiv.symm (whiskeredValueSumIsColimit pe X A B (h A B)))
    exact preservesColimit_of_iso_diagram F (diagramIsoPair K).symm

theorem valueWhiskerUnitPreservesBinary :
    PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft (⟨Obj U⟩ : Values)) :=
  valueWhiskerPreservesBinary pe U (inverse_mem_at_unit pe)

private theorem valueDistributive (h : ∀ X A B : τ, Mem (guardedDistributorIso pe X A B).hom) :
    DistributiveTensor Values where
  left_isIso X A B := by
    have : PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft X) :=
      valueWhiskerPreservesBinary (τ := τ) (Φ := Φ) pe X.obj.as (h X.obj.as)
    change IsIso (coprodComparison (MonoidalCategory.tensorLeft X) A B)
    infer_instance


open Paper.TypeCategory
  (CentralCopies WhiskerCentral centralCopies_productFst centralCopies_productSnd
    pairArrows_comp_common pairArrows_copy_comp whiskerCentral_ofRegion_branchValue
    pairArrows_copy_branchValue whiskerLeft_comp whiskerRight_comp whiskerLeft_id whiskerRight_id)
open Paper.Extension.Singleton.ValueCoproducts (centralCopies_exactCopair)

local notation "BaseObj" => Paper.TypeCategory.ofType (Φ := Φ)
local notation "BW" => Paper.TypeCategory.whiskerLeft
local notation "BR" => Paper.TypeCategory.whiskerRight

set_option backward.isDefEq.respectTransparency false in
private theorem base_whisker_copies (X : τ) {A B : τ} {f : BaseObj A ⟶ BaseObj B}
    (hf : CentralCopies f) : CentralCopies (BW (BaseObj X) f) := by
  let q := Paper.TypeCategory.ofRegion (Φ := Φ) (CfgEta.TypeCategory.productSndBranches X A)
  have hq : CentralCopies q := centralCopies_productSnd X A
  rw [base_whisker_pair X f]
  apply Paper.TypeCategory.centralCopies_pair (centralCopies_productFst X A)
  exact ⟨Paper.TypeCategory.WhiskerCentral.comp hq.1 hf.1, pairArrows_copy_comp q f hq.1 hq.2 hf.2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem base_distributor_forward_copies (X A B : τ) :
    CentralCopies (distributorIso (Φ := Φ) X A B).inv := by
  let e := distributorIso (Φ := Φ) X A B
  let c := Paper.TypeCategory.sumCofan (Φ := Φ) (X ×ₜ A) (X ×ₜ B)
  let d := Paper.TypeCategory.sumCofan (Φ := Φ) A B
  let l := BW (BaseObj X) d.inl
  let r := BW (BaseObj X) d.inr
  let s := Paper.TypeCategory.sumIso (Φ := Φ) (X ×ₜ A) (X ×ₜ B)
  have left : l ≫ e.hom = c.inl :=
    (congrArg (l ≫ ·) (distributorIso_hom X A B)).trans (Paper.RetainedCase.left_distributor_inl X A B)
  have right : r ≫ e.hom = c.inr :=
    (congrArg (r ≫ ·) (distributorIso_hom X A B)).trans (Paper.RetainedCase.left_distributor_inr X A B)
  have eq : e.inv = s.hom ≫ coprod.desc l r := by
    apply BinaryCofan.IsColimit.hom_ext (Paper.TypeCategory.sumCofanIsColimit _ _)
    · change c.inl ≫ e.inv = c.inl ≫ s.hom ≫ coprod.desc l r
      have hi : c.inl ≫ s.hom = coprod.inl := Paper.TypeCategory.sumCofan_inl_sumIso_hom _ _
      rw [← Category.assoc c.inl s.hom, hi, coprod.inl_desc,
        ← left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change c.inr ≫ e.inv = c.inr ≫ s.hom ≫ coprod.desc l r
      have hi : c.inr ≫ s.hom = coprod.inr := Paper.TypeCategory.sumCofan_inr_sumIso_hom _ _
      rw [← Category.assoc c.inr s.hom, hi, coprod.inr_desc,
        ← right, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change CentralCopies e.inv
  rw [eq]
  apply centralCopies_exactCopair
  · apply base_whisker_copies X
    change CentralCopies (Paper.TypeCategory.sumCofan (Φ := Φ) A B).inl
    rw [Paper.TypeCategory.sumCofan_inl]
    exact ⟨whiskerCentral_ofRegion_branchValue (.inl (.var rfl)), pairArrows_copy_branchValue (.inl (.var rfl))⟩
  · apply base_whisker_copies X
    change CentralCopies (Paper.TypeCategory.sumCofan (Φ := Φ) A B).inr
    rw [Paper.TypeCategory.sumCofan_inr]
    exact ⟨whiskerCentral_ofRegion_branchValue (.inr (.var rfl)), pairArrows_copy_branchValue (.inr (.var rfl))⟩

private theorem iso_hom_square {C : Type u} [CategoryTheory.Category C] {X X' Y Y' : C}
    (e : X ≅ X') (f : Y ≅ Y') (g : X ⟶ Y) (g' : X' ⟶ Y')
    (h : e.inv ≫ g = g' ≫ f.inv) : e.hom ≫ g' = g ≫ f.hom := by
  calc
    e.hom ≫ g' = e.hom ≫ (g' ≫ f.inv) ≫ f.hom := by simp
    _ = g ≫ f.hom := by rw [← h]; simp

set_option backward.isDefEq.respectTransparency false in
private theorem base_iso_copies {A B : τ} (e : BaseObj A ≅ BaseObj B)
    (h : CentralCopies e.inv) : CentralCopies e.hom := by
  refine ⟨?_, ?_⟩
  · intro S T g
    exact ⟨iso_hom_square ((Paper.TypeCategory.whiskerRightFunctor S).mapIso e)
        ((Paper.TypeCategory.whiskerRightFunctor T).mapIso e) _ _ (h.1 g).1,
      iso_hom_square ((Paper.TypeCategory.whiskerLeftFunctor S).mapIso e)
        ((Paper.TypeCategory.whiskerLeftFunctor T).mapIso e) _ _ (h.1 g).2⟩
  · change Paper.TypeCategory.pairArrows e.hom e.hom = e.hom ≫ Paper.TypeCategory.diagonalArrow B
    apply (cancel_epi e.inv).1
    rw [← pairArrows_comp_common _ _ _ h, Iso.inv_hom_id, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simp only [Paper.TypeCategory.pairArrows, whiskerLeft_id, whiskerRight_id, Category.comp_id]
    exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
theorem inverse_mem_iff_pure (X A B : τ) :
    Mem (guardedDistributorIso pe X A B).hom ↔ ProjectedPureReturn Seed pe (guardedDistributorIso pe X A B).hom := by
  let e := guardedDistributorIso (Φ := Φ) pe X A B
  refine ⟨fun h => h.1.1, fun h => ⟨⟨h, ?_⟩, ?_⟩⟩
  · exact ⟨(distributorIso (Φ := Φ) X A B).hom,
      base_iso_copies _ (base_distributor_forward_copies X A B), rfl⟩
  · change e.hom ≫ discardArrow Seed ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) = discardArrow Seed (X ×ₜ (A ⊕ₜ B))
    apply (cancel_epi e.inv).1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (forward_mem pe X A B).2.symm


open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open CfgEta.TypeCategory.Retained (distributorRegion)

theorem inverse_mem_of_distributor_return (X A B : τ)
    (eq : Paper.WithCaseReturns.Eqv pe [X ×ₜ (A ⊕ₜ B)] (returnRegion distributorTerm)
      (distributorRegion : Region Φ) [(X ×ₜ A) ⊕ₜ (X ×ₜ B)]) :
    Mem (guardedDistributorIso pe X A B).hom := by
  apply (inverse_mem_iff_pure pe X A B).2
  refine ⟨_, ⟨distributorTerm, distributorTerm_typed X A B, distributorTerm_pure pe, rfl⟩, ?_⟩
  rw [Functor.mapIso_hom, distributorIso_hom]
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (returnRegion_typed (distributorTerm_typed X A B)) (distributorRegion_typed X A B)).2 eq

set_option backward.isDefEq.respectTransparency false in
private theorem inverse_mem_of_valueDistributive [DistributiveTensor Values] (X A B : τ) :
    Mem (guardedDistributorIso pe X A B).hom := by
  let F := MonoidalCategory.tensorLeft (⟨Obj X⟩ : Values)
  have : ∀ {Y Z : Values}, IsIso (coprodComparison F Y Z) := fun {Y Z} =>
    DistributiveTensor.left_isIso (⟨Obj X⟩ : Values) Y Z
  have : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryCoproducts_of_isIso_coprodComparison F
  let c := valueSumCofan Seed pe A B
  let d := valueSumCofan Seed pe (X ×ₜ A) (X ×ₜ B)
  let hc := valueSumIsColimit Seed pe (Paper.WithCaseReturns.copairPure pe) A B
  let hd := valueSumIsColimit Seed pe (Paper.WithCaseReturns.copairPure pe) (X ×ₜ A) (X ×ₜ B)
  let hcF : IsColimit (BinaryCofan.map F c) :=
    BinaryCofan.isColimitMapCoconeEquiv (isColimitOfPreserves F hc)
  let v := hcF.coconePointUniqueUpToIso hd
  let J := Paper.WithCaseReturns.values (τ := τ) (Φ := Φ) pe
  have eq : J.map v.hom = (guardedDistributorIso pe X A B).hom := by
    rw [Functor.mapIso_hom, distributorIso_hom]
    apply (projectedDistributor_eq_iff Seed X A B _).2
    constructor
    · have hl := congrArg J.map (hcF.comp_coconePointUniqueUpToIso_hom hd ⟨WalkingPair.left⟩)
      change J.map (((⟨Obj X⟩ : Values) ◁ c.inl) ≫ v.hom) = (cf (X ×ₜ A) (X ×ₜ B)).inl at hl
      rw [Functor.map_comp, value_whisker] at hl
      exact hl
    · have hr := congrArg J.map (hcF.comp_coconePointUniqueUpToIso_hom hd ⟨WalkingPair.right⟩)
      change J.map (((⟨Obj X⟩ : Values) ◁ c.inr) ≫ v.hom) = (cf (X ×ₜ A) (X ×ₜ B)).inr at hr
      rw [Functor.map_comp, value_whisker] at hr
      exact hr
  rw [← eq]
  exact v.hom.property

theorem valueDistributive_iff :
    DistributiveTensor Values ↔ ∀ X A B : τ, ProjectedPureReturn Seed pe (guardedDistributorIso pe X A B).hom :=
  ⟨fun _ X A B => (inverse_mem_iff_pure pe X A B).1 (inverse_mem_of_valueDistributive pe X A B),
   fun h => valueDistributive pe (fun X A B => (inverse_mem_iff_pure pe X A B).2 (h X A B))⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseReturnDistributor
