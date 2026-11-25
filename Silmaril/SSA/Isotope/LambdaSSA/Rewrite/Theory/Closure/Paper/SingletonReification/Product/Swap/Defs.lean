module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Defs

/-! # Product symmetry in the packed LambdaSSA interpretation -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v u₁ v₁

variable {τ : Type u} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] (M : TypeModel τ V)

/-- The source swap in the interpretation's packed product coordinates. -/
noncomputable def packedSwap (A B : τ) : M.obj (product A B) ⟶ M.obj (product B A) :=
  (M.productIso A B).hom ≫ (BraidedCategory.braiding (M.obj A) (M.obj B)).hom ≫ (M.productIso B A).inv

/-- A term that destructures and swaps the two fields of its input. -/
def swapTerm {Φ : Type v} : Tm Φ :=
  .let₂ (.var 0) (.pair (.var 0) (.var 1))

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
