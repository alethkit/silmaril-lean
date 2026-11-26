module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.Semantics.Categories.Thms

/-! # Guarded iteration at the chosen computation coproduct -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- Convert the chosen coproduct to the exact syntax sum before running guarded feedback. -/
noncomputable def iterateChosen {A B : TypeCategory Seed} (f : A ⟶ B ⨿ A) : A ⟶ B :=
  iterateSum Seed (A := A.as) (B := B.as) (f ≫ (sumIso Seed B.as A.as).inv)

/-- The iteration operator supplied by the guarded feedback construction. -/
noncomputable abbrev guardedIteration : Iteration (TypeCategory Seed) where
  iterate := iterateChosen Seed

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
