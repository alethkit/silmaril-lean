module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Context comparison for the categorical structured SSA embedding -/

@[expose] public section

universe u v h

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open LetIter.Semantics.Categorical (TypeModel envObj envSnocIso)
open LambdaSSA.Semantics.Categorical (ctxObj)

variable {τ : Type u} [TypeFormers τ] {V : Type v} [Category.{h} V]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] (M : TypeModel τ V)

/-- Match SSA's positional product with LetCase's environment product, whose
empty free context contributes one left tensor-unit factor. -/
def contextMap : {n : Nat} → (β : BoundCtx τ n) →
    ctxObj M β.toList ⟶ envObj M (Ctx.nil : Ctx Empty τ) β
  | _, .nil => (λ_ (𝟙_ V)).inv
  | _, .snoc β A => (contextMap β ▷ M.obj A) ≫ (envSnocIso M Ctx.nil β A).hom

end Silmaril.Isotope.LambdaSSA.Acyclic
