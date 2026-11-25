module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Extensionality.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct

/-! # Copying and product comparisons for packed singleton reification -/

public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap sndMap)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)

/-- The packed diagonal is the source duplicate followed by product reindexing. -/
theorem packedDiagonal_eq_duplicate (X : τ) :
    packedDiagonal M X = duplicate (M.obj X) ≫ (M.productIso X X).inv := rfl

/-- The reindexed value map preserves composition by functoriality and cancellation of the object isomorphism. -/
theorem reindexValueHom_comp {X A B : τ} (f : M.obj X ⟶ M.obj A) (g : M.obj A ⟶ M.obj B) :
    reindexValueHom J M objIso X B (f ≫ g) =
      reindexValueHom J M objIso X A f ≫ reindexValueHom J M objIso A B g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct.reindexValueHom_comp J M objIso f g

/-- Diagonal and the two whiskering comparisons transport an exact Cartesian pairing. -/
theorem reindexValueHom_pair {X A B : τ} (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B)
    (diagonal : reindexValueHom J M objIso X (product X X) (packedDiagonal M X) =
      diagonalArrow (Φ := Φ) X)
    (right : reindexValueHom J M objIso (product X X) (product A X) (packedWhiskerRight M X X A f) =
      whiskerRight (reindexValueHom J M objIso X A f) (ofType X))
    (left : reindexValueHom J M objIso (product A X) (product A B) (packedWhiskerLeft M A X B g) =
      whiskerLeft (ofType A) (reindexValueHom J M objIso X B g)) :
    reindexValueHom J M objIso X (product A B) (packedPair M X A B f g) =
      pairArrows (reindexValueHom J M objIso X A f) (reindexValueHom J M objIso X B g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct.reindexValueHom_pair J M objIso f g diagonal right left

/-- Transport source copying when both endpoint diagonals and the two local whiskerings agree. -/
theorem reindexValueHom_preservesDiagonal {X A : τ} (f : M.obj X ⟶ M.obj A)
    (sourceDiagonal : reindexValueHom J M objIso X (product X X) (packedDiagonal M X) =
      diagonalArrow (Φ := Φ) X)
    (targetDiagonal : reindexValueHom J M objIso A (product A A) (packedDiagonal M A) =
      diagonalArrow (Φ := Φ) A)
    (right : reindexValueHom J M objIso (product X X) (product A X) (packedWhiskerRight M X X A f) =
      whiskerRight (reindexValueHom J M objIso X A f) (ofType X))
    (left : reindexValueHom J M objIso (product A X) (product A A) (packedWhiskerLeft M A X A f) =
      whiskerLeft (ofType A) (reindexValueHom J M objIso X A f)) :
    PreservesDiagonal (τ := τ) (reindexValueHom J M objIso X A f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct.reindexValueHom_preservesDiagonal J M objIso f sourceDiagonal targetDiagonal right left

/-- After comparing the projections and components, the constructor pair comparison is equivalent to copying of its source image. -/
theorem compare_pair_iff_source_copy {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B)
    (fstAgrees : reindexValueHom J M objIso (product A B) A (fstMap M A B) =
      ofRegion (productFstBranches A B))
    (sndAgrees : reindexValueHom J M objIso (product A B) B (sndMap M A B) =
      ofRegion (productSndBranches A B))
    (hf : reindexValueHom J M objIso X A f = ofRegion (.br (ℓ := 0) rfl ha))
    (hg : reindexValueHom J M objIso X B g = ofRegion (.br (ℓ := 0) rfl hb)) :
    reindexValueHom J M objIso X (product A B) (packedPair M X A B f g) =
        ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) ↔
      PreservesDiagonal (τ := τ) (reindexValueHom J M objIso X (product A B) (packedPair M X A B f g)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct.compare_pair_iff_source_copy J M objIso ha hb f g fstAgrees sndAgrees hf hg

/-- After comparing the projections, duplicate agreement is equivalent to copying of the reindexed source duplicate. -/
theorem compare_duplicate_iff_source_copy (X : τ)
    (fstAgrees : reindexValueHom J M objIso (product X X) X (fstMap M X X) =
      ofRegion (productFstBranches X X))
    (sndAgrees : reindexValueHom J M objIso (product X X) X (sndMap M X X) =
      ofRegion (productSndBranches X X)) :
    reindexValueHom J M objIso X (product X X) (packedDiagonal M X) =
        diagonalArrow (Φ := Φ) X ↔
      PreservesDiagonal (τ := τ) (reindexValueHom J M objIso X (product X X) (packedDiagonal M X)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct.compare_duplicate_iff_source_copy J M objIso X fstAgrees sndAgrees

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
