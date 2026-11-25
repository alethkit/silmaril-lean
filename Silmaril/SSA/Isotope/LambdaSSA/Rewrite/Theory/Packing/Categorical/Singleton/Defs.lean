module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs

/-! # Denotation of a region with one input and one exit -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Remove the input context's empty prefix and the exit's singleton coproduct wrapper. -/
noncomputable def denoteSingletonRegion {A B : τ} {r : Region Φ}
    (h : Region.HasType [A] r [B]) : J.obj (M.obj A) ⟶ J.obj (M.obj B) :=
  J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ ctxObj M [A]) ≫
    denoteRegion J M h ≫ J.map (singletonLabelPayload M B)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
