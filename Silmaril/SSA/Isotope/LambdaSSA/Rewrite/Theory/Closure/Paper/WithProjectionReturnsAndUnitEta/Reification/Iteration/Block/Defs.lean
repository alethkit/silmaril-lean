module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs

/-! # Constructor returns from a carried block -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Destructure the packed block input and return a constructor value. -/
theorem unpackedConstructorReturn {X S D : τ} {a : Tm Φ}
    (ha : Tm.BranchValue [S, X, product X S] a D) :
    ValueBranches (Φ := Φ) [product X S] (.let₂ (.var 0) (.br 0 a)) [D] :=
  .let₂ (.var (i := 0) rfl) (.br rfl ha)

/-- Put the constructor result in the nested return arm of the packed exits. -/
theorem constructorResultBlock {X S D : τ} {a : Tm Φ}
    (ha : Tm.BranchValue [S, X, product X S] a D) :
    ValueBranches (Φ := Φ) [product X S] (.let₂ (.var 0) (.br 0 (.inr (.inl a)))) [packedExitType [S, D]] :=
  unpackedConstructorReturn (.inr (.inl ha))

/-- Return the capture field rather than the state field. -/
theorem captureResultBlock (X S : τ) :
    ValueBranches (Φ := Φ) [product X S] (.let₂ (.var 0) (.br 0 (.inr (.inl (.var 1))))) [packedExitType [S, X]] :=
  constructorResultBlock (.var (i := 1) rfl)

/-- Swap the two fields before returning the pair in the nested result tag. -/
theorem swapResultBlock (X S : τ) :
    ValueBranches (Φ := Φ) [product X S] (.let₂ (.var 0) (.br 0 (.inr (.inl (.pair (.var 0) (.var 1))))))
      [packedExitType [S, product S X]] :=
  constructorResultBlock (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
