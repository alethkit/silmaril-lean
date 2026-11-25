module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Postcomposition at the outward exits of a dispatcher -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

/-- Apply a computation to the exit payload, forwarding a local jump unchanged.
The left summand exits and the right summand requests another iteration. -/
noncomputable def mapDispatcherExit {A B S : V} (k : J.obj A ⟶ J.obj B) :
    J.obj (A ⨿ S) ⟶ J.obj (B ⨿ S) :=
  splitMapCoprod J A S ≫ coprod.desc
    (k ≫ J.map (coprod.inl : B ⟶ B ⨿ S)) (J.map (coprod.inr : S ⟶ B ⨿ S))

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
