module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Thms

/-! # Distributive Freyd structure of the structural value inclusion -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton
open Paper.RetainedCase.Chosen (projectedDistributor_eq_iff)
open Paper.RetainedCase (distributorIso_hom)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues (valueCartesian valueBraided computationPremonoidal computationSymmetric)

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueFreyd

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Val" => Paper.WithCaseReturns.StructuralValues.ValueCategory (τ := τ) (Φ := Φ) pe
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed
set_option hygiene false in
local notation "valueObj" => Paper.WithCaseReturns.StructuralValues.ofSyntaxType (Φ := Φ) pe
set_option hygiene false in
local notation "inc" => Paper.WithCaseReturns.StructuralValues.inclusion (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "unitStep" => Paper.WithCaseReturns.includeUnit (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "proj" => Paper.WithCaseReturns.projection (τ := τ) (Φ := Φ) pe
local notation "cartPair" => CartesianMonoidalCategory.lift
local notation "Fst" => CartesianMonoidalCategory.fst
local notation "Snd" => CartesianMonoidalCategory.snd
local notation "F" => productFst Seed
local notation "S" => productSnd Seed
local notation "Pa" => pairArrows Seed
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric

set_option backward.isDefEq.respectTransparency false in
noncomputable def whiskeredSumIsColimit (X A B : τ) :
    IsColimit (BinaryCofan.map (MonoidalCategory.tensorLeft (valueObj X)) (StructuralValues.sum Seed A B)) := by
  apply (StructuralValues.sumIsColimit Seed (X ×ₜ A) (X ×ₜ B)).ofIsoColimit
  let e := Paper.WithCaseReturns.StructuralValues.distributor (Φ := Φ) pe X A B
  have hi : (inc).map e.inv = (Paper.WithCaseReturns.guardedDistributorIso pe X A B).hom :=
    congrArg Iso.inv (Paper.WithCaseReturns.StructuralValues.inclusion_mapIso_distributor pe X A B)
  have hj : (Paper.WithCaseReturns.guardedDistributorIso pe X A B).hom =
      Paper.Extension.Singleton.ofRegion Seed (CfgEta.TypeCategory.Retained.distributorRegion_typed X A B) :=
    congrArg (proj).map (distributorIso_hom X A B)
  have legs := (projectedDistributor_eq_iff Seed X A B _).1 hj
  refine BinaryCofan.ext e ?_ ?_
  · apply (inc).map_injective
    change (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inl =
      (inc).map ((valueObj X) ◁ (StructuralValues.sum Seed A B).inl) ≫ (inc).map e.inv
    rw [hi, StructuralValues.map_whiskerLeft Seed unitStep]
    exact legs.1.symm
  · apply (inc).map_injective
    change (sumCofan Seed (X ×ₜ A) (X ×ₜ B)).inr =
      (inc).map ((valueObj X) ◁ (StructuralValues.sum Seed A B).inr) ≫ (inc).map e.inv
    rw [hi, StructuralValues.map_whiskerLeft Seed unitStep]
    exact legs.2.symm

set_option backward.isDefEq.respectTransparency false in
private theorem whiskerPreservesBinary (X : τ) :
    PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft (valueObj X)) where
  preservesColimit {K} := by
    let A : τ := (K.obj ⟨WalkingPair.left⟩).obj.as
    let B : τ := (K.obj ⟨WalkingPair.right⟩).obj.as
    let L := MonoidalCategory.tensorLeft (valueObj X)
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) L :=
      preservesColimit_of_preserves_colimit_cocone (StructuralValues.sumIsColimit Seed A B)
        (BinaryCofan.isColimitMapCoconeEquiv.symm (whiskeredSumIsColimit pe X A B))
    exact preservesColimit_of_iso_diagram L (diagramIsoPair K).symm

theorem valueDistributive : DistributiveTensor Val where
  left_isIso X A B := by
    have : PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft X) :=
      whiskerPreservesBinary (τ := τ) (Φ := Φ) pe X.obj.as
    change IsIso (coprodComparison (MonoidalCategory.tensorLeft X) A B)
    infer_instance

theorem computationDistributive : DistributivePremonoidalCategory Comp where
  toDistributiveTensor :=
    CoproductDistributivity.distributiveTensor_of_whisker Seed (fun X => ⟨Iso.refl (whiskerLeftFunctor Seed X)⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem map_lift {X A B : τ} (f : valueObj X ⟶ valueObj A) (g : valueObj X ⟶ valueObj B) :
    (inc).map (cartPair f g) = Pa f.hom g.hom := by
  have hl : (inc).map (cartPair f g) ≫ F A B = f.hom :=
    congrArg (inc).map (CartesianMonoidalCategory.lift_fst f g)
  have hr : (inc).map (cartPair f g) ≫ S A B = g.hom :=
    congrArg (inc).map (CartesianMonoidalCategory.lift_snd f g)
  have e : Pa ((inc).map (cartPair f g) ≫ F A B) ((inc).map (cartPair f g) ≫ S A B) =
      (inc).map (cartPair f g) :=
    StructuralValues.reconstruct Seed (X := X) (A := A) (B := B) (cartPair f g).property
  rw [hl, hr] at e
  exact e.symm

set_option backward.isDefEq.respectTransparency false in
private theorem associatePair (A B C : τ) :
    (associateIso Seed (Obj A) (Obj B) (Obj C)).hom =
      Pa (F (A ×ₜ B) C ≫ F A B) (Pa (F (A ×ₜ B) C ≫ S A B) (S (A ×ₜ B) C)) := by
  have h := congrArg (proj).map (Paper.TypeCategory.associate_eq_pair (Φ := Φ) A B C)
  simp only [map_pairArrows, Functor.map_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem braidPair (A B : τ) :
    (braidIso Seed (Obj A) (Obj B)).hom = Pa (S A B) (F A B) := by
  have h := congrArg (proj).map (Paper.TypeCategory.braid_eq_pair (Φ := Φ) A B)
  rw [map_pairArrows] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem map_associator (A B C : τ) :
    (inc).map (α_ (valueObj A) (valueObj B) (valueObj C)).hom =
      (α_ (Obj A) (Obj B) (Obj C)).hom := by
  let p := Fst (valueObj A ⊗ valueObj B) (valueObj C)
  let q := Snd (valueObj A ⊗ valueObj B) (valueObj C)
  have h : (α_ (valueObj A) (valueObj B) (valueObj C)).hom =
      cartPair (p ≫ Fst (valueObj A) (valueObj B)) (cartPair (p ≫ Snd (valueObj A) (valueObj B)) q) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [p]
    · rw [CartesianMonoidalCategory.lift_snd]
      apply CartesianMonoidalCategory.hom_ext <;> simp [p, q, Category.assoc]
  rw [h, map_lift]
  change Pa (F (A ×ₜ B) C ≫ F A B) ((inc).map (cartPair _ _)) = _
  rw [map_lift]
  exact (associatePair pe A B C).symm

set_option backward.isDefEq.respectTransparency false in
private theorem map_braid (A B : τ) :
    (inc).map (BraidedCategory.braiding (valueObj A) (valueObj B)).hom =
      (BraidedPremonoidalCategory.braiding (Obj A) (Obj B)).hom := by
  rw [← CartesianMonoidalCategory.lift_snd_fst, map_lift]
  exact (braidPair pe A B).symm

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
def freyd : FreydCategory (inc) where
  unitIso := Iso.refl _
  tensorIso _ _ := Iso.refl _
  tensor_naturality_left {X Y} f Z := by
    change whiskerRight Seed f.hom Z.obj ≫ 𝟙 _ = 𝟙 _ ≫ (inc).map (f ▷ Z)
    rw [Category.comp_id, Category.id_comp]
    exact (StructuralValues.map_whiskerRight Seed unitStep Z.obj.as f).symm
  tensor_naturality_right X {Y Z} f := by
    change whiskerLeft Seed X.obj f.hom ≫ 𝟙 _ = 𝟙 _ ≫ (inc).map (X ◁ f)
    rw [Category.comp_id, Category.id_comp]
    exact (StructuralValues.map_whiskerLeft Seed unitStep X.obj.as f).symm
  associativity X Y Z := by
    dsimp only [Iso.refl_hom]
    simp only [PremonoidalCategory.whiskerLeft_id, PremonoidalCategory.id_whiskerRight, Category.id_comp,
      Category.comp_id]
    exact (map_associator (τ := τ) (Φ := Φ) pe X.obj.as Y.obj.as Z.obj.as).symm
  left_unitality X := by
    simp only [Iso.refl_hom, PremonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl
  right_unitality X := by
    simp only [Iso.refl_hom, PremonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl
  map_central f :=
    ⟨fun g => (f.property.1.1 g).1, fun g => (f.property.1.1 g).2.symm⟩
  braiding X Y := by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact map_braid (τ := τ) (Φ := Φ) pe X.obj.as Y.obj.as
  obj_bijective := ⟨fun {_ _} h => WideSubcategory.ext h, fun X => ⟨⟨X⟩, rfl⟩⟩

theorem centralUnit :
    letI := freyd (τ := τ) (Φ := Φ) pe
    FreydCategory.CentralUnit (inc) := by
  let := freyd (τ := τ) (Φ := Φ) pe
  exact ⟨PremonoidalCategory.isCentral_id _⟩

theorem sharedTensor (X Y : Val) :
    letI := freyd (τ := τ) (Φ := Φ) pe
    ∃ h : (inc).obj X ⊗ (inc).obj Y = (inc).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := (inc)) X Y = eqToIso h :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueFreyd
