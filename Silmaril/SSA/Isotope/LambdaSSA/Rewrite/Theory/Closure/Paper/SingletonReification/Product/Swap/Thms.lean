module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Producer.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap

/-! # Ambient and syntactic comparisons for the packed swap -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (braid braidRegion braidBranches ofType ofRegion pairArrows)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (fstTerm)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap sndMap inlMap inrMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂ w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The term-level swap acts on the two fields of its only input. -/
theorem swapTerm_typed (A B : τ) :
    Tm.HasType [product A B] (swapTerm (Φ := Φ)) (product B A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.swapTerm_typed A B

section Values

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] (M : TypeModel τ V)

/-- The packed source symmetry pairs its second and first projections. -/
theorem packedSwap_pair (A B : τ) :
    packedSwap M A B = packedPair M (product A B) B A (sndMap M A B) (fstMap M A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.packedSwap_pair M A B

end Values

/-- Pairing the guarded second and first projections gives the guarded swap in Paper. -/
theorem pair_projections_braid (A B : τ) :
    pairArrows (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B))
      (ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)) = braid A B :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.pair_projections_braid A B

section Region

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- The guarded swap has the interpreted packed symmetry as its ambient denotation. -/
theorem braid_denotes (A B : τ) :
    RegionDenotes J M (braidBranches (Φ := Φ) A B).hasType
      (J.map (snd (𝟙_ V) (M.obj (product A B)) ≫ packedSwap M A B ≫
        labelInject M 0 (rfl : At [product B A] 0 (product B A)))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.braid_denotes J M A B

/-- Returning the swap expression has the same ambient graph as the guarded swap. -/
theorem swapReturn_denotes (A B : τ) :
    RegionDenotes J M (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)).hasType
      (J.map (snd (𝟙_ V) (M.obj (product A B)) ≫ packedSwap M A B ≫
        labelInject M 0 (rfl : At [product B A] 0 (product B A)))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.swapReturn_denotes J M A B

variable [RegionTypingCoherent (Φ := Φ) J M]

/-- Removing the singleton context and label wrappers gives the packed symmetry. -/
theorem denoteSingleton_braid (A B : τ) :
    denoteSingletonRegion J M (braidBranches (Φ := Φ) A B).hasType = J.map (packedSwap M A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.denoteSingleton_braid J M A B

/-- The single-bind term return gives the same packed symmetry at its exact interface. -/
theorem denoteSingleton_swapTerm (A B : τ) :
    denoteSingletonRegion J M (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)).hasType =
      J.map (packedSwap M A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.denoteSingleton_swapTerm J M A B

/-- The ambient singleton denotation of the first-projection expression. -/
theorem denoteSingleton_firstTerm (A B : τ) :
    denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) A B)).hasType = J.map (fstMap M A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.denoteSingleton_firstTerm J M A B


/-- Destructuring the input and returning a constructor has a value-map denotation. -/
theorem exists_denoteSingleton_let₂_var_branch (A S D : τ) {a : Tm Φ}
    (ha : Tm.BranchValue [S, A, product A S] a D) :
    ∃ f : M.obj (product A S) ⟶ M.obj D,
      denoteSingletonRegion J M (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl ha.hasType) :
        HasType [product A S] (.let₂ (.var 0) (.br 0 a)) [D]) = J.map f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.exists_denoteSingleton_let₂_var_branch
    J M A S D ha

/-- A constructor return after unpacking the input can apply the result tag by categorical postcomposition. -/
theorem denoteSingleton_let₂_resultTag (A S D : τ) {a : Tm Φ}
    (ha : Tm.BranchValue [S, A, product A S] a D) :
    denoteSingletonRegion J M
        (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.inr (.inl ha.hasType))) :
          HasType [product A S] (.let₂ (.var 0) (.br 0 (.inr (.inl a)))) [packedExitType [S, D]]) =
      denoteSingletonRegion J M
        (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl ha.hasType) :
          HasType [product A S] (.let₂ (.var 0) (.br 0 a)) [D]) ≫
        J.map (inlMap M D Silmaril.empty ≫ inrMap M S (coprod D Silmaril.empty)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.denoteSingleton_let₂_resultTag J M A S D ha

/-- The guarded region projection evaluates to the exact packed source projection. -/
theorem denoteSingleton_productFst (A S : τ) :
    denoteSingletonRegion J M (productFstBranches (Φ := Φ) A S).hasType = J.map (fstMap M A S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.denoteSingleton_productFst J M A S

/-- Destructure the state pair and send its second coordinate to the repeat tag. -/
theorem denoteSingleton_snd_repeatTag (A S D : τ) :
    denoteSingletonRegion J M
      (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))) :
        HasType (Φ := Φ) [product A S] (.let₂ (.var 0) (.br 0 (.inl (.var 0)))) [packedExitType [S, D]]) =
      J.map (sndMap M A S ≫ inlMap M S (coprod D Silmaril.empty)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.denoteSingleton_snd_repeatTag J M A S D

end Region

section Transport

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp] [HasFiniteCoproducts V]
  [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}

/-- Producer-based pairing transports the swap given right whiskering of the second projection. -/
theorem compare_swap_of_rightSnd (cmp : ModelComparisons J M objIso pe) (A B : τ)
    (rightSnd :
      let P := product A B
      reindexValueHom J M objIso (product P P) (product B P) (packedWhiskerRight M P P B (sndMap M A B)) =
        Paper.TypeCategory.whiskerRight (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B)) (ofType P)) :
    reindexValueHom J M objIso (product A B) (product B A) (packedSwap M A B) = braid A B :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.compare_swap_of_rightSnd J M objIso cmp A B rightSnd

variable [RegionTypingCoherent (Φ := Φ) J M]

/-- Given the producer comparison for the swap term, the source-model swap comparison is
equivalent to the displayed exact typed rewrite in the Paper quotient. -/
theorem compare_swap_iff_return (A B : τ)
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)).hasType) =
        ofRegion (τ := τ) (returnOnce_typed (swapTerm_typed (Φ := Φ) A B))) :
    reindexValueHom J M objIso (product A B) (product B A) (packedSwap M A B) = braid A B ↔
      Paper.Eqv [product A B] (returnOnce (swapTerm (Φ := Φ))) braidRegion [product B A] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.compare_swap_iff_return J M objIso A B producer

/-- At a guarded first projection, the ordinary projection and term-producer comparisons force
the corresponding projection return rewrite in default Paper. -/
theorem projection_comparisons_force_return (A B : τ)
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) A B)).hasType) =
        ofRegion (τ := τ) (returnOnce_typed (fstTerm (Φ := Φ) A B)))
    (projection : reindexValueHom J M objIso (product A B) A (fstMap M A B) =
      ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)) :
    Paper.Eqv [product A B] (returnOnce (.let₂ (.var 0) (.var 1) : Tm Φ))
      (.let₂ (.var 0) (.br 0 (.var 1))) [A] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap.projection_comparisons_force_return J M objIso A B producer projection

end Transport

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
