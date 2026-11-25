module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Extensionality.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs

/-! # Transport copying and compare constructor products -/

public section

universe u v u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Paper.SingletonReification
open CfgEta.TypeCategory (productFstBranches productSndBranches seqValueBranches)
open CfgEta.TypeCategory.ConstructorReification (fstMap sndMap)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)

theorem reindexValueHom_comp {X A B : τ} (f : M.obj X ⟶ M.obj A) (g : M.obj A ⟶ M.obj B) :
    reindexValueHom J M objIso X B (f ≫ g) =
      reindexValueHom J M objIso X A f ≫ reindexValueHom J M objIso A B g := by
  simp [reindexValueHom, reindexHom]

private theorem packedPair_factor {X A B : τ} (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B) :
    packedPair M X A B f g = packedDiagonal M X ≫
      packedWhiskerRight M X X A f ≫ packedWhiskerLeft M A X B g := by
  unfold packedDiagonal packedPair packedWhiskerRight packedWhiskerLeft
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ _ (M.productIso A B).inv,
    ← Category.assoc (CartesianMonoidalCategory.lift (𝟙 (M.obj X)) (𝟙 (M.obj X)))]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

private theorem packedPair_self {X A : τ} (f : M.obj X ⟶ M.obj A) :
    packedPair M X A A f f = f ≫ packedDiagonal M A := by
  unfold packedDiagonal packedPair
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem reindexValueHom_pair {X A B : τ} (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B)
    (diagonal : reindexValueHom J M objIso X (product X X) (packedDiagonal M X) =
      diagonalArrow (Φ := Φ) X)
    (right : reindexValueHom J M objIso (product X X) (product A X) (packedWhiskerRight M X X A f) =
      whiskerRight (reindexValueHom J M objIso X A f) (ofType X))
    (left : reindexValueHom J M objIso (product A X) (product A B) (packedWhiskerLeft M A X B g) =
      whiskerLeft (ofType A) (reindexValueHom J M objIso X B g)) :
    reindexValueHom J M objIso X (product A B) (packedPair M X A B f g) =
      pairArrows (reindexValueHom J M objIso X A f) (reindexValueHom J M objIso X B g) := by
  rw [packedPair_factor M, reindexValueHom_comp, reindexValueHom_comp, diagonal, right, left]
  rfl

theorem reindexValueHom_preservesDiagonal {X A : τ} (f : M.obj X ⟶ M.obj A)
    (sourceDiagonal : reindexValueHom J M objIso X (product X X) (packedDiagonal M X) =
      diagonalArrow (Φ := Φ) X)
    (targetDiagonal : reindexValueHom J M objIso A (product A A) (packedDiagonal M A) =
      diagonalArrow (Φ := Φ) A)
    (right : reindexValueHom J M objIso (product X X) (product A X) (packedWhiskerRight M X X A f) =
      whiskerRight (reindexValueHom J M objIso X A f) (ofType X))
    (left : reindexValueHom J M objIso (product A X) (product A A) (packedWhiskerLeft M A X A f) =
      whiskerLeft (ofType A) (reindexValueHom J M objIso X A f)) :
    PreservesDiagonal (τ := τ) (reindexValueHom J M objIso X A f) := by
  change pairArrows (reindexValueHom J M objIso X A f) (reindexValueHom J M objIso X A f) =
    reindexValueHom J M objIso X A f ≫ diagonalArrow A
  rw [← reindexValueHom_pair J M objIso f f sourceDiagonal right left,
    packedPair_self M, reindexValueHom_comp, targetDiagonal]

private abbrev branchValue {X A : τ} {a : Tm Φ} (h : Tm.BranchValue [X] a A) :
    ofType (Φ := Φ) X ⟶ ofType A :=
  ofRegion (.br (ℓ := 0) rfl h)

private theorem branchPair_fst {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    branchValue (.pair ha hb) ≫ ofRegion (productFstBranches A B) = branchValue ha := by
  let hPair : ValueBranches [X] (.br 0 (.pair a b)) [product A B] := .br rfl (.pair ha hb)
  let hProj := productFstBranches (Φ := Φ) A B
  change ofRegion hPair ≫ ofRegion hProj = branchValue ha
  rw [ofRegion_comp hPair hProj (seqValueBranches hPair hProj)]
  exact (ofRegion_eq_iff _ _).mpr
    (.productBeta (.let₂Beta ha hb (.br (ℓ := 0) rfl (.var (i := 1) rfl))))

private theorem branchPair_snd {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    branchValue (.pair ha hb) ≫ ofRegion (productSndBranches A B) = branchValue hb := by
  let hPair : ValueBranches [X] (.br 0 (.pair a b)) [product A B] := .br rfl (.pair ha hb)
  let hProj := productSndBranches (Φ := Φ) A B
  change ofRegion hPair ≫ ofRegion hProj = branchValue hb
  rw [ofRegion_comp hPair hProj (seqValueBranches hPair hProj)]
  exact (ofRegion_eq_iff _ _).mpr
    (.productBeta (.let₂Beta ha hb (.br (ℓ := 0) rfl (.var (i := 0) rfl))))

set_option backward.isDefEq.respectTransparency false in
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
      PreservesDiagonal (τ := τ) (reindexValueHom J M objIso X (product A B) (packedPair M X A B f g)) := by
  have hc := pairArrows_copy_branchValue (.pair ha hb)
  constructor
  · intro h
    rw [h]
    exact hc
  · intro copy
    apply projection_ext_of_preservesDiagonal copy hc
    · calc
        _ = reindexValueHom J M objIso X A f := by
          rw [← fstAgrees, ← reindexValueHom_comp]
          simp [packedPair, fstMap]
        _ = _ := hf.trans (branchPair_fst ha hb).symm
    · calc
        _ = reindexValueHom J M objIso X B g := by
          rw [← sndAgrees, ← reindexValueHom_comp]
          simp [packedPair, sndMap]
        _ = _ := hg.trans (branchPair_snd ha hb).symm

set_option backward.isDefEq.respectTransparency false in
theorem compare_duplicate_iff_source_copy (X : τ)
    (fstAgrees : reindexValueHom J M objIso (product X X) X (fstMap M X X) =
      ofRegion (productFstBranches X X))
    (sndAgrees : reindexValueHom J M objIso (product X X) X (sndMap M X X) =
      ofRegion (productSndBranches X X)) :
    reindexValueHom J M objIso X (product X X) (packedDiagonal M X) =
        diagonalArrow (Φ := Φ) X ↔
      PreservesDiagonal (τ := τ) (reindexValueHom J M objIso X (product X X) (packedDiagonal M X)) := by
  have h : reindexValueHom J M objIso X X (𝟙 (M.obj X)) =
      ofRegion (Φ := Φ) (.br (ℓ := 0) rfl (.var (i := 0) rfl) : ValueBranches [X] (.br 0 (.var 0)) [X]) := by
    rw [ofRegion_id]
    simp [reindexValueHom, reindexHom]
  exact compare_pair_iff_source_copy J M objIso (.var (i := 0) rfl) (.var (i := 0) rfl)
    (𝟙 (M.obj X)) (𝟙 (M.obj X)) fstAgrees sndAgrees h h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProduct
