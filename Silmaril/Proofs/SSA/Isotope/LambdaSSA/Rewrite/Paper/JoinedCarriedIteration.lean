module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Model.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Reification.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms

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
  sumIso whiskerRight whiskerLeft whiskerRight_map whiskerLeft_map diagonalArrow iterateSum_map)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (denoteSingleton_firstTerm packedWhiskerRight)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg (guardedCfg_typed realizePackedStep_typed retagPacked_typed
  duplicateCapture_arrow duplicateCapture_typed realizePackedStep_arrow canonicalRegion_eq_guardedCfg_realize)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model (reindexHom carrier carriedStep capturePrefix
  carriedStep_factor_retained packedPair_id_right packedTensorIso
  reindexRetainLeft_tensorIso reindexPackedWhiskerRight_tensorIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (fstTerm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => fun (Γ : VCtx τ) (r s : Region Φ) (K : LCtx τ) =>
  Paper.WithProjectionReturns.Step Γ r s K ∨ Paper.WithUnitEta.Step Γ r s K
set_option hygiene false in
local notation "Comp" => Paper.Extension.Singleton.TypeCategory (Seed)
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Seed)
set_option hygiene false in
local notation "Lit" => Paper.Extension.Singleton.ofRegion (Seed)
set_option hygiene false in
local notation "F" => projection (Seed)

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
theorem reindexRetainLeft_of_tensorIso {R A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B))
    (source : (packedTensorIso J M objIso R A).hom =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ (objIso A).hom))
    (target : (packedTensorIso J M objIso R B).hom =
      ((objIso R).hom ▷ J.obj (M.obj B)) ≫ (Obj R ◁ (objIso B).hom))
    (swap : (J.obj (M.obj R) ◁ f) ≫ ((objIso R).hom ▷ J.obj (M.obj B)) =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ f)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) f ≫
      J.map (M.productIso R B).inv) =
      Obj R ◁ reindexHom J M objIso f := by
  rw [reindexRetainLeft_tensorIso]
  apply (cancel_epi (packedTensorIso J M objIso R A).hom).mp
  rw [Iso.hom_inv_id_assoc, source, target]
  unfold reindexHom
  have cancel : (Obj R ◁ (objIso A).hom) ≫
      Obj R ◁ ((objIso A).inv ≫ f ≫ (objIso B).hom) =
      Obj R ◁ (f ≫ (objIso B).hom) := by
    rw [← PremonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (J.obj (M.obj R) ◁ f), swap]
  simp only [Category.assoc]
  rw [cancel, PremonoidalCategory.whiskerLeft_comp]

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
