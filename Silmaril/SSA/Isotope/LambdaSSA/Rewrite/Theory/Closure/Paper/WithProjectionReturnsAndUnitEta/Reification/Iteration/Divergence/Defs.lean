module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs

/-! # The selected empty-exit arrow of a repeat-only step -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Zero" => ofType (Seed) (Silmaril.empty : τ)

/-- The source isomorphism identifies the two selected empty-exit arrows for a
step that applies an endomorphism and then always takes the repeat arm. -/
def RepeatDivergenceAgrees [Iteration Comp] {A X : Comp} (state : A ≅ X) (next : A ⟶ A) : Prop :=
  state.inv ≫ CategoryTheory.iterate (show A ⟶ Zero ⨿ A from next ≫ coprod.inr) =
    canonicalIterate (show X ⟶ Zero ⨿ X from (state.inv ≫ next ≫ state.hom) ≫ coprod.inr)

/-- Destructure the carrier and send the same state payload back to the local label. -/
theorem repeatStateBlock (X S D : τ) :
    ValueBranches [product X S] (.let₂ (.var 0) (.br 0 (.inl (.var 0))) : Region Φ) [packedExitType [S, D]] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.inl (.var (i := 0) rfl)))

/-- Evaluate a term, which may call an instruction, and repeat with its result. -/
theorem repeatTermBlock {X S D : τ} {t : Tm Φ} (ht : Tm.HasType [product X S] t S) :
    ValueBranches [product X S] (.let₁ t (.br 0 (.inl (.var 0)))) [packedExitType [S, D]] :=
  .let₁ ht (.br rfl (.inl (.var (i := 0) rfl)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
