module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Finite.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms

/-! # Fixpoint comparison for bounded carried steps -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.WithProjectionReturnsAndUnitEta.Reification
open scoped Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.Extension.Singleton (ofType iterateChosen_fixpoint)
open Paper.SingletonReification.SingleCfg (blockComputation)
open Paper.SingletonReification.SingleCfg.Model (carrier)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)

universe u v u₁ v₁

theorem eq_unroll_of_fixpoint {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {A B : C}
    (step : A ⟶ B ⨿ A) {k : A ⟶ B} (fix : k = step ≫ coprod.desc (𝟙 B) k) (n : Nat) :
    k = unroll step k n := by
  induction n with
  | zero => rfl
  | succ n h => exact fix.trans (congrArg (fun k => step ≫ coprod.desc (𝟙 B) k) h)

theorem unroll_two_phases {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {A B L R : C}
    (cover : L ⨿ R ≅ A) (step : A ⟶ B ⨿ A) (next : L ⟶ R) (out : R ⟶ B)
    (repeatPhase : coprod.inl ≫ cover.hom ≫ step = next ≫ coprod.inr ≫ cover.hom ≫ coprod.inr)
    (resultPhase : coprod.inr ≫ cover.hom ≫ step = out ≫ coprod.inl)
    (tail : A ⟶ B) :
    unroll step tail 2 = cover.inv ≫ coprod.desc (next ≫ out) out := by
  apply (cancel_epi cover.hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp only [unroll, coprod.inl_desc, reassoc_of% repeatPhase, coprod.inr_desc,
      reassoc_of% resultPhase, coprod.inl_desc, Category.comp_id]
  · simp only [unroll, coprod.inr_desc, reassoc_of% resultPhase, coprod.inl_desc, Category.comp_id]

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)

theorem canonicalIterate_fixpoint {A B : Comp} (f : A ⟶ B ⨿ A) :
    canonicalIterate f = f ≫ coprod.desc (𝟙 B) (canonicalIterate f) :=
  iterateChosen_fixpoint (Seed) f

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem transportedIterationAgrees_of_unroll {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (n : Nat) (out : Obj (product X S) ⟶ Obj (product X D))
    (finite : ∀ tail, unroll (actualCarriedStep J M objIso hb) tail n = out) :
    TransportedIterationAgrees J M objIso hb := by
  let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
  let state := carrier J M objIso X S
  let result := carrier J M objIso X D
  let target := actualCarriedStep J M objIso hb
  let loop := state.inv ≫ CategoryTheory.iterate actual ≫ result.hom
  have square : state.hom ≫ target = actual ≫ coprod.map result.hom state.hom :=
    actualCarriedStep_carrier_square J M objIso hb
  have step : state.inv ≫ actual ≫ coprod.map result.hom state.hom = target := by
    rw [← square, Iso.inv_hom_id_assoc]
  have descend :
      coprod.map result.hom state.hom ≫ coprod.desc (𝟙 _) loop =
        coprod.desc (𝟙 _) (CategoryTheory.iterate actual) ≫ result.hom := by
    apply coprod.hom_ext
    · simp only [coprod.inl_map_assoc, coprod.inl_desc, Category.comp_id, coprod.inl_desc_assoc,
        Category.id_comp]
    · simp only [coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, loop, Iso.hom_inv_id_assoc]
  have fix : loop = target ≫ coprod.desc (𝟙 _) loop := by
    rw [← step]
    simp only [Category.assoc, descend]
    exact congrArg (state.inv ≫ ·) (ElgotCategory.fixpoint_assoc actual result.hom)
  exact ((eq_unroll_of_fixpoint target fix n).trans (finite loop)).trans
    (((eq_unroll_of_fixpoint target (canonicalIterate_fixpoint target) n).trans
      (finite (canonicalIterate target))).symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedFiniteIteration
