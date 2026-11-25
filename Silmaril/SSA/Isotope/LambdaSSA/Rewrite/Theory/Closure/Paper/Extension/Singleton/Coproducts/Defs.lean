module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Defs

/-! # Exact sum cocones in contextual singleton extensions -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- The syntactic sum and its two constructor injections, projected to the extended quotient. -/
def sumCofan (A B : τ) : BinaryCofan (ofType Seed A) (ofType Seed B) :=
  BinaryCofan.map (projection Seed) (Paper.TypeCategory.sumCofan A B)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
