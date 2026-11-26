module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration

/-! # Compare both carried iterators on a finitely unfolding step -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton (ofType ofRegion sumIso)
open Paper.SingletonReification.SingleCfg (blockComputation realizePackedStep_typed)
open Paper.SingletonReification.SingleCfg.Model (carrier)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open SyntacticCategory (iterateRegion_valueBranches)

universe u v u₁ v₁

/-- A fixpoint can be unfolded any finite number of times. -/
theorem eq_unroll_of_fixpoint {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {A B : C}
    (step : A ⟶ B ⨿ A) {k : A ⟶ B} (fix : k = step ≫ coprod.desc (𝟙 B) k) (n : Nat) :
    k = unroll step k n :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration.eq_unroll_of_fixpoint step fix n

/-- An unconditionally repeating step preserves every candidate tail. -/
theorem unroll_repeat {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {A B : C}
    (tail : A ⟶ B) (n : Nat) : unroll (coprod.inr : A ⟶ B ⨿ A) tail n = tail := by
  induction n with
  | zero => rfl
  | succ n h => simp only [unroll, coprod.inr_desc, h]

/-- A repeat phase followed by a return phase takes at most two steps. -/
theorem unroll_two_phases {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {A B L R : C}
    (cover : L ⨿ R ≅ A) (step : A ⟶ B ⨿ A) (next : L ⟶ R) (out : R ⟶ B)
    (repeatPhase : coprod.inl ≫ cover.hom ≫ step = next ≫ coprod.inr ≫ cover.hom ≫ coprod.inr)
    (resultPhase : coprod.inr ≫ cover.hom ≫ step = out ≫ coprod.inl)
    (tail : A ⟶ B) :
    unroll step tail 2 = cover.inv ≫ coprod.desc (next ≫ out) out :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration.unroll_two_phases
    cover step next out repeatPhase resultPhase tail

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)

/-- The descended iterator satisfies the fixpoint equation at the chosen sum. -/
theorem canonicalIterate_fixpoint {A B : Comp} (f : A ⟶ B ⨿ A) :
    canonicalIterate f = f ≫ coprod.desc (𝟙 B) (canonicalIterate f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration.canonicalIterate_fixpoint f

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The carrier square transports the interpreted fixpoint. Finite unfolding
then identifies it with the guarded fixpoint whenever the tail is irrelevant. -/
theorem transportedIterationAgrees_of_unroll {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (n : Nat) (out : Obj (product X S) ⟶ Obj (product X D))
    (finite : ∀ tail, unroll (actualCarriedStep J M objIso hb) tail n = out) :
    TransportedIterationAgrees J M objIso hb :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration.transportedIterationAgrees_of_unroll
    J M objIso hb n out finite

/-- Reify a carried loop once the bounded unfolding is checked on its guarded step. -/
theorem actualCarriedIteration_eq_of_boundedRealization {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb)
    (n : Nat) (out : Obj (product X S) ⟶ Obj (product X D))
    (finite : ∀ tail, unroll
      (ofRegion (Seed) (realizePackedStep_typed hb) ≫ (sumIso (Seed) (product X D) (product X S)).hom)
      tail n = out) :
    let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X D
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      ofRegion (Seed) (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  actualCarriedIteration_eq J M objIso cmp
    (transportedIterationAgrees_of_unroll J M objIso hb n out
      (fun tail => (congrArg (fun f => unroll f tail n) (actualCarriedStep_eq J M objIso cmp)).trans (finite tail)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
