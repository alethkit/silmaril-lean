module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Defs

/-! # Representative equations for the joined singleton denotation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteSingletonRegion)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  {A B : τ}

/-- The joined interpretation computes the ordinary guarded denotation on
every projected arrow. -/
theorem denoteArrow_projection (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B) :
    denoteArrow J M shared ((projection (τ := τ) (Φ := Φ)).map f) = Paper.TypeCategory.denoteArrow J M f :=
  rfl

/-- A joined arrow can be interpreted at any of its typed guarded representatives. -/
theorem denoteArrow_ofRegion {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    denoteArrow J M shared (Paper.Extension.Singleton.ofRegion Step hr) = denoteSingletonRegion J M hr.hasType :=
  (denoteArrow_projection J M shared (Paper.TypeCategory.ofRegion hr)).trans
    (Paper.TypeCategory.denoteArrow_ofRegion J M shared hr)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
