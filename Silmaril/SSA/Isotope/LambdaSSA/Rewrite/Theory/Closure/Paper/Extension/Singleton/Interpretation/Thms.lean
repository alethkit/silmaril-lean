module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Interpretation.Defs

/-! # The local interpretation computes the denotation of each representative -/

public section

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

/-- Every typed representative gives the same actual denotation at the chosen
subsingleton target hom. -/
theorem denoteSubsingleton_ofRegion {A B : τ} [Subsingleton (J.obj (M.obj A) ⟶ J.obj (M.obj B))]
    {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    denoteSubsingleton Seed J M (ofRegion Seed hr) = denoteSingletonRegion J M hr.hasType :=
  Subsingleton.elim _ _

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
