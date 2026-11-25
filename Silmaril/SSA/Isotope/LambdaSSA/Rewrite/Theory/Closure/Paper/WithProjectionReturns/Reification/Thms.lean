module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Reification.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification

/-! # Local reification by the existing projection-return equations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (braidBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg (guardedCfg_typed)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Seed" => (WithProjectionReturns.Step (τ := τ) (Φ := Φ))
local notation "Q" => Paper.Extension.Singleton.ofRegion Seed

/-- The two projections retain the original packed input type. -/
theorem rebuildPair_typed (A B : τ) :
    Tm.HasType [product A B] (rebuildPair (Φ := Φ)) (product A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.rebuildPair_typed A B

/-- The reverse pair of projections has the swapped product type. -/
theorem swapPair_typed (A B : τ) :
    Tm.HasType [product A B] (swapPair (Φ := Φ)) (product B A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.swapPair_typed A B

/-- Rebuilding the input preserves the guarded singleton typing. -/
theorem afterRebuild_typed {A B D : τ} {p : Region Φ} (hp : ValueBranches [product A B] p [D]) :
    ValueBranches [product A B] (afterRebuild p) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.afterRebuild_typed hp

/-- The lowered reconstruction is the identity in the projection-return quotient. -/
theorem rebuildPair_arrow (A B : τ) :
    Q (returnRegion_typed (rebuildPair_typed (Φ := Φ) A B)) =
      𝟙 (Paper.Extension.Singleton.ofType Seed (product A B)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.rebuildPair_arrow A B

/-- The lowered reverse pairing is the guarded braid in the projection-return quotient. -/
theorem swapPair_arrow (A B : τ) :
    Q (returnRegion_typed (swapPair_typed (Φ := Φ) A B)) = Q (braidBranches A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.swapPair_arrow A B

/-- Prepending the lowered reconstruction preserves the guarded arrow in the quotient. -/
theorem afterRebuild_arrow {A B D : τ} {p : Region Φ} (hp : ValueBranches [product A B] p [D]) :
    Q (afterRebuild_typed hp) = Q hp :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.afterRebuild_arrow hp

/-- The guarded assembly respects the two repacked representatives in the quotient. -/
theorem guardedCfg_afterRebuild_arrow {A B S D : τ} {e b : Region Φ}
    (he : ValueBranches [product A B] e [packedExitType [S, D]])
    (hb : ValueBranches [product (product A B) S] b [packedExitType [S, D]]) :
    Q (guardedCfg_typed (afterRebuild_typed he) (afterRebuild_typed hb)) =
      Q (guardedCfg_typed he hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.guardedCfg_afterRebuild_arrow he hb

section Ambient

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The repacked representative has the same ambient singleton denotation and the same
projection-return quotient arrow. -/
theorem afterRebuild_compare
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {A B D : τ} {p : Region Φ} (hp : ValueBranches [product A B] p [D]) :
    let hr := afterRebuild_typed hp
    denoteSingletonRegion J M hr.hasType = denoteSingletonRegion J M hp.hasType ∧ Q hr = Q hp :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.afterRebuild_compare J M shared hp

/-- The lowered swap gives the ambient packed symmetry and the projected guarded braid. -/
theorem swapPair_compare
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (A B : τ) :
    let hr := returnRegion_typed (swapPair_typed (Φ := Φ) A B)
    denoteSingletonRegion J M hr.hasType = J.map (Paper.SingletonReification.packedSwap M A B) ∧
      Q hr = Q (braidBranches A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.swapPair_compare J M shared A B

/-- Repacking both local producers preserves the ambient guarded CFG and its
arrow in the projection-return quotient. -/
theorem guardedCfg_afterRebuild_compare
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {A B S D : τ} {e b : Region Φ}
    (he : ValueBranches [product A B] e [packedExitType [S, D]])
    (hb : ValueBranches [product (product A B) S] b [packedExitType [S, D]]) :
    let hp := guardedCfg_typed (afterRebuild_typed he) (afterRebuild_typed hb)
    let hq := guardedCfg_typed he hb
    denoteSingletonRegion J M hp.hasType = denoteSingletonRegion J M hq.hasType ∧ Q hp = Q hq :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification.guardedCfg_afterRebuild_compare J M shared he hb

end Ambient

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification
