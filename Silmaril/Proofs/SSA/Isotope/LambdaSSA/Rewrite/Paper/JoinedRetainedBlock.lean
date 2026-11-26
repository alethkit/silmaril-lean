module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms

/-! # Retained interpretation of constructor result blocks -/

public section

universe u v u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRetainedBlock

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.Extension.Singleton (ofType ofRegion whiskerLeft sumCofan)
open Paper.SingletonReification
  (denoteSingleton_let₂_resultTag exists_denoteSingleton_let₂_var_branch
    denoteSingleton_productFst denoteSingleton_braid packedSwap)
open Paper.SingletonReification.SingleCfg.Model (reindexHom)
open CfgEta.TypeCategory (productFstBranches)
open CfgEta.TypeCategory.ConstructorReification (inlMap inrMap fstMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open scoped Paper.WithProjectionReturnsAndUnitEta.Reification

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)
set_option hygiene false in
local notation "Lit" => ofRegion (Seed)
set_option hygiene false in
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

set_option backward.isDefEq.respectTransparency false in
private theorem constructorResultBlock_arrow {X S D : τ} {a : Tm Φ}
    (ha : Tm.BranchValue [S, X, product X S] a D) :
    Lit (constructorResultBlock ha) =
      Lit (unpackedConstructorReturn ha) ≫ (sumCofan (Seed) D Silmaril.empty).inl ≫
        (sumCofan (Seed) S (coprod D Silmaril.empty)).inr := by
  have base : Paper.TypeCategory.ofRegion (τ := τ) (constructorResultBlock ha) =
      Paper.TypeCategory.ofRegion (τ := τ) (unpackedConstructorReturn ha) ≫
        (Paper.TypeCategory.sumCofan (Φ := Φ) D Silmaril.empty).inl ≫
          (Paper.TypeCategory.sumCofan S (coprod D Silmaril.empty)).inr := by
    rw [Paper.TypeCategory.sumCofan_inl, Paper.TypeCategory.sumCofan_inr]
    rfl
  simpa only [Functor.map_comp] using! congrArg (F).map base

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem retainedConstructorResult_eq {X S D : τ} {a : Tm Φ}
    (ha : Tm.BranchValue [S, X, product X S] a D)
    (payload : reindexHom J M objIso (denoteSingletonRegion J M (unpackedConstructorReturn ha).hasType) =
      Lit (unpackedConstructorReturn ha))
    (input : RetainedTensorAgrees J M objIso X (product X S))
    (output : RetainedPackedExitsAgree J M objIso X S D) :
    reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M (constructorResultBlock ha).hasType) ≫
      J.map (M.productIso X (packedExitType [S, D])).inv) =
        whiskerLeft (Seed) (Obj X) (Lit (constructorResultBlock ha)) := by
  obtain ⟨f, denotes⟩ := exists_denoteSingleton_let₂_var_branch J M X S D ha
  rw [denotes] at payload
  let tag := inlMap M D Silmaril.empty ≫ inrMap M S (coprod D Silmaril.empty)
  have graph : denoteSingletonRegion J M (constructorResultBlock ha).hasType = J.map (f ≫ tag) := by
    rw [denoteSingleton_let₂_resultTag J M X S D ha, denotes, ← J.map_comp]
  have retained := reindexRetainLeft_of_valueMap J M objIso (f ≫ tag)
    (packedExitIso J M objIso S D) input output
  have computed : (objIso (product X S)).inv ≫ J.map (f ≫ tag) ≫ (packedExitIso J M objIso S D).hom =
      Lit (constructorResultBlock ha) := by
    rw [J.map_comp_assoc, packedExitIso_resultTag J M objIso S D, constructorResultBlock_arrow ha]
    simpa only [reindexHom, Category.assoc] using! congrArg
      (· ≫ (sumCofan (Seed) D Silmaril.empty).inl ≫ (sumCofan (Seed) S (coprod D Silmaril.empty)).inr) payload
  rw [graph]
  exact retained.trans (congrArg (whiskerLeft (Seed) (Obj X)) computed)

set_option backward.isDefEq.respectTransparency false in
theorem retainedCaptureResult_eq (X S : τ)
    (projection : reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S))
    (input : RetainedTensorAgrees J M objIso X (product X S))
    (output : RetainedPackedExitsAgree J M objIso X S X) :
    reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType) ≫
      J.map (M.productIso X (packedExitType [S, X])).inv) =
        whiskerLeft (Seed) (Obj X) (Lit (captureResultBlock X S)) :=
  retainedConstructorResult_eq J M objIso (.var (i := 1) rfl)
    (by simpa only [denoteSingleton_productFst J M X S] using projection) input output

set_option backward.isDefEq.respectTransparency false in
theorem retainedSwapResult_eq (X S : τ)
    (swap : reindexHom J M objIso (J.map (packedSwap M X S)) = Lit (Paper.TypeCategory.braidBranches X S))
    (input : RetainedTensorAgrees J M objIso X (product X S))
    (output : RetainedPackedExitsAgree J M objIso X S (product S X)) :
    reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M (swapResultBlock (Φ := Φ) X S).hasType) ≫
      J.map (M.productIso X (packedExitType [S, product S X])).inv) =
        whiskerLeft (Seed) (Obj X) (Lit (swapResultBlock X S)) :=
  retainedConstructorResult_eq J M objIso (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))
    (by simpa only [denoteSingleton_braid J M X S] using swap) input output

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRetainedBlock
