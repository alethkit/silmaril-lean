module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Representative.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Iteration.Thms

/-! # Denotational preservation of joined singleton iteration -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationDenotation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofType sumIso projectStep_comp_sumIso_inv exists_projectStep)
open Paper.WithProjectionReturnsAndUnitEta (Step projection denoteArrow)
open Paper.WithProjectionReturnsAndUnitEta.Reification
  (canonicalIterate canonicalIterate_projectStep)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (Seed)

set_option backward.isDefEq.respectTransparency false in
theorem preserve {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    denoteArrow J M shared (canonicalIterate f) =
      CategoryTheory.iterate (denoteArrow J M shared (f ≫ (sumIso (Seed) B A).inv) ≫
        (Paper.TypeCategory.denoteExactSumIso J M B A).hom) := by
  obtain ⟨g, rfl⟩ := exists_projectStep (Seed) f
  let comparison := (Paper.TypeCategory.denoteExactSumIso J M B A).hom
  let norm := g ≫ (Paper.TypeCategory.sumIso B A).inv
  calc
    _ = denoteArrow J M shared ((projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.iterate g)) :=
      congrArg (denoteArrow J M shared) (canonicalIterate_projectStep g)
    _ = CategoryTheory.iterate
        (denoteArrow J M shared ((projection (τ := τ) (Φ := Φ)).map norm) ≫ comparison) :=
      Paper.TypeCategory.denoteFunctor_map_iterateSum J M shared norm
    _ = _ := congrArg (fun a : Obj A ⟶ Obj (Silmaril.coprod B A) =>
      CategoryTheory.iterate (denoteArrow J M shared a ≫ comparison))
      (projectStep_comp_sumIso_inv (Seed) (A := A) (B := B) g).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationDenotation
