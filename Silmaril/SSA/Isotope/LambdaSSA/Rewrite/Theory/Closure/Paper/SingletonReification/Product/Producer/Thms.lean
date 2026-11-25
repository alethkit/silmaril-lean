module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer

/-! # Singleton products from guarded producer comparisons -/

public section

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A B : τ}
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "C" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)

/-- The chosen singleton denotation for returning the pair of input variables is the packed source diagonal. -/
theorem denote_duplicate_producer (X : τ) :
    let ht : Tm.HasType [X] (.pair (.var 0) (.var 0) : Tm Φ) (product X X) :=
      .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
    denoteSingletonRegion J M (returnOnce_typed ht).hasType = J.map (packedDiagonal M X) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer.denote_duplicate_producer J M X

/-- Applying the producer comparison to the typed pair of the input variable with itself compares the packed source duplicate. -/
theorem compare_duplicate_of_producer (X : τ)
    (producer :
      let ht : Tm.HasType [X] (.pair (.var 0) (.var 0) : Tm Φ) (product X X) :=
        .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
      reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ht).hasType) =
        ofRegion (returnOnce_typed ht)) :
    reindexValueHom J M objIso X (product X X) (packedDiagonal M X) = diagonalArrow (Φ := Φ) X :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer.compare_duplicate_of_producer
    J M objIso X producer

section

variable {ε : Type w} [HasEff Φ ε] {pe : ε}

/-- The producer and retained-left comparisons transport Cartesian pairing with a local right-whiskering comparison. -/
theorem reindexValueHom_pair_of_producer (cmp : ModelComparisons J M objIso pe)
    (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B)
    (right : reindexValueHom J M objIso (product X X) (product A X) (packedWhiskerRight M X X A f) =
      whiskerRight (reindexValueHom J M objIso X A f) (ofType X)) :
    reindexValueHom J M objIso X (product A B) (packedPair M X A B f g) =
      pairArrows (reindexValueHom J M objIso X A f) (reindexValueHom J M objIso X B g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer.reindexValueHom_pair_of_producer
    J M objIso cmp f g right

end

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

/-- A constructor-valued branch is compared by the existing single-bind return comparison. -/
theorem compare_branch_of_producer {a : Tm Φ} (ha : Tm.BranchValue [X] a A)
    (producer : reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ha.hasType).hasType) =
      ofRegion (returnOnce_typed ha.hasType)) :
    reindexHom J M objIso (denoteSingletonRegion J M (HasType.br (ℓ := 0) rfl ha.hasType)) =
      ofRegion (.br (ℓ := 0) rfl ha) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer.compare_branch_of_producer
    J M objIso ha producer

/-- The packed Cartesian lift of two constructor denotations is the guarded constructor pair. -/
theorem compare_constructor_pair_of_producer {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    {f : ctxObj M [X] ⟶ M.obj A} {g : ctxObj M [X] ⟶ M.obj B}
    (df : Denotes J M ha.hasType (J.map f)) (dg : Denotes J M hb.hasType (J.map g))
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (.pair ha.hasType hb.hasType)).hasType) =
        ofRegion (returnOnce_typed (.pair ha.hasType hb.hasType))) :
    reindexValueHom J M objIso X (product A B)
        (packedPair M X A B ((λ_ (M.obj X)).inv ≫ f) ((λ_ (M.obj X)).inv ≫ g)) =
      ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer.compare_constructor_pair_of_producer
    J M objIso ha hb df dg producer


end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
