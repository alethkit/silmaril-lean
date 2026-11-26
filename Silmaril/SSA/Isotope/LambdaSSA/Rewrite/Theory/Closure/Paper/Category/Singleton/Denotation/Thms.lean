module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Defs

/-! # Representative equations for denotation of guarded singleton arrows -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical (RegionTypingCoherent denoteSingletonRegion)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  {A B D : τ}

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
include shared

/-- The actual arrow's denotation computes from any guarded representative. -/
theorem denoteArrow_ofRegion {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    denoteArrow J M (ofRegion hr) = denoteSingletonRegion J M hr.hasType := by
  unfold denoteArrow denoteSingletonRegion
  let witness := (exists_ofRegion (ofRegion hr)).choose_spec
  have eqv := (ofRegion_eq_iff witness.choose hr).mp witness.choose_spec.symm
  rw [eqv.sound J M shared]

/-- After cancelling the choice of source coproduct, the two model coordinates
are supplied by the model of the exact sum type. -/
theorem denoteSumArrow_ofRegion {r : Region Φ}
    (hr : ValueBranches [A] r [Silmaril.coprod B D]) :
    denoteSumArrow J M (ofRegion hr ≫ (sumIso B D).hom) =
      denoteSingletonRegion J M hr.hasType ≫ J.map (M.coprodIso B D).hom := by
  simp only [denoteSumArrow, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    denoteArrow_ofRegion J M shared]

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
