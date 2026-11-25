module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Factor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification

/-! # Reify a guarded one-block CFG with its explicit carried step -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso whiskerRight braid)
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (projection)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
  (ModelComparisons packedWhiskerRight reindexValueHom)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)

universe u v u₁ v₁ w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V]
  [DistributivePremonoidalCategory Comp] [Iteration Comp] [ElgotCategory Comp]
  (J : V ⥤ Comp) [StrongElgotFreydCategory J] (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}

/-- The retained exit distributor and exact-sum decoder realize the carried result routing. -/
theorem carriedRoute_compare (cmp : ModelComparisons J M objIso pe) (X S D : τ) :
    carriedRoute J M objIso X S D = ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) ≫
      (sumIso (product X D) (product X S)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification.carriedRoute_compare
    J M objIso cmp X S D

/-- One right-whiskering comparison at the first projection identifies the capture prefix. -/
theorem capturePrefix_of_rightFst (cmp : ModelComparisons J M objIso pe) (X S : τ)
    (localRight :
      let P := product X S
      reindexValueHom J M objIso (product P P) (product X P) (packedWhiskerRight M P P X (fstMap M X S)) =
        whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P)) :
    capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification.capturePrefix_of_rightFst
    J M objIso cmp X S localRight

/-- The mixed output swap suffices to identify the capture prefix.
Duplicating the input absorbs the swap of its equal copies. -/
theorem capturePrefix_of_braid (cmp : ModelComparisons J M objIso pe) (X S : τ)
    (outputBraid : let P := product X S
      reindexValueHom J M objIso (product P X) (product X P)
        ((M.productIso P X).hom ≫ (BraidedCategory.braiding (M.obj P) (M.obj X)).hom ≫
          (M.productIso X P).inv) = braid P X) :
    capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification.capturePrefix_of_braid
    J M objIso cmp X S outputBraid

/-- The carried step of the reconstructed block arrow has the explicit guarded representative. -/
theorem carriedStep_reconstructed_realize {X S D : τ} {b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (rightFst :
      let P := product X S
      reindexValueHom J M objIso (product P P) (product X P) (packedWhiskerRight M P P X (fstMap M X S)) =
        whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P)) :
    carriedStep J M objIso X S D ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
      ofRegion (τ := τ) (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification.carriedStep_reconstructed_realize
    J M objIso cmp hb rightFst

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

/-- The explicit carried step represents the projected model step and reifies
the guarded CFG at the same canonical region. The last conjunct is a typed
rewrite in the existing Paper relation. -/
theorem reify_guardedCfg_realize {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (rightFst :
      let P := product X S
      reindexValueHom J M objIso (product P P) (product X P) (packedWhiskerRight M P P X (fstMap M X S)) =
        whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P))
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    let hs := realizePackedStep_typed hb
    (projection Seed).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (projection Seed).map (ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) ∧
    (projection Seed).map (reindexHom J M objIso
      (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
      Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) ∧
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification.reify_guardedCfg_realize
    J M objIso cmp Seed he hb rightFst choice entryIH blockIH

/-- Reify with the same explicit carried step using only the mixed output
swap comparison for the structural prefix. -/
theorem reify_guardedCfg_realize_of_braid {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (outputBraid : let P := product X S
      reindexValueHom J M objIso (product P X) (product X P)
        ((M.productIso P X).hom ≫ (BraidedCategory.braiding (M.obj P) (M.obj X)).hom ≫
          (M.productIso X P).inv) = braid P X)
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    let hs := realizePackedStep_typed hb
    (projection Seed).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (projection Seed).map (ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) ∧
    (projection Seed).map (reindexHom J M objIso
      (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
      Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) ∧
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification.reify_guardedCfg_realize_of_braid
    J M objIso cmp Seed he hb outputBraid choice entryIH blockIH

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
