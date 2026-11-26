module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Soundness.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms

/-! # Denotation of guarded singleton arrows -/

@[expose] public section

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
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] {A B D : τ}

/-- Interpret an actual Paper singleton arrow using a typed representative.
The soundness theorem identifies the denotations of all its representatives. -/
noncomputable def denoteArrow (f : ofType (Φ := Φ) A ⟶ ofType B) :
    J.obj (M.obj A) ⟶ J.obj (M.obj B) :=
  denoteSingletonRegion J M (exists_ofRegion f).choose_spec.choose.hasType

/-- Interpret an arrow into a chosen binary coproduct in the model's value
coproduct coordinates, using the source's exact sum-type comparison. -/
noncomputable def denoteSumArrow (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType D) :
    J.obj (M.obj A) ⟶ J.obj (M.obj B ⨿ M.obj D) :=
  denoteArrow J M (f ≫ (sumIso B D).inv) ≫ J.map (M.coprodIso B D).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
