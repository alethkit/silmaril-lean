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
open Paper.Extension.Singleton (ofType ofRegion sumIso)
open Paper.WithProjectionReturnsAndUnitEta (Step projection denoteArrow denoteArrow_projection)
open Paper.WithProjectionReturnsAndUnitEta.Reification
  (canonicalIterate canonicalIterate_projection_exact exists_canonicalIterate_body)

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
  obtain ⟨_, hr, h, _⟩ := exists_canonicalIterate_body f
  let g := Paper.TypeCategory.ofRegion hr
  change f = (projection (τ := τ) (Φ := Φ)).map g ≫ (sumIso (Seed) B A).hom at h
  rw [h, canonicalIterate_projection_exact g, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, denoteArrow_projection, denoteArrow_projection]
  exact Paper.TypeCategory.denoteFunctor_map_iterateSum J M shared g

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationDenotation
