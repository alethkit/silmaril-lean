module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs

/-! # Interpreting a singleton hom with a subsingleton target -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Interpret a single hom by taking the actual singleton denotation of a
typed representative. Subsingleton elimination makes this independent of the
representative at both quotient levels. -/
noncomputable def denoteSubsingleton {A B : τ} [Subsingleton (J.obj (M.obj A) ⟶ J.obj (M.obj B))]
    (f : ofType Seed A ⟶ ofType Seed B) : J.obj (M.obj A) ⟶ J.obj (M.obj B) :=
  Quot.liftOn f (fun arrow : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B =>
    denoteSingletonRegion J M (Paper.TypeCategory.exists_ofRegion arrow).choose_spec.choose.hasType)
    (fun _ _ _ => Subsingleton.elim _ _)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
