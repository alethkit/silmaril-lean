module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Finite.Captured.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Thms

/-! The actual packed block in Maybe takes a repeat from its left input.
The state it carries into the second step takes the result arm. -/

open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit

example (capture : Bits) :
    exactStep.of (stateInput capture (.inl PUnit.unit)) =
      Sum.inl (Sum.inr (stateInput capture (.inr PUnit.unit))) ∧
    exactStep.of (stateInput capture (.inr PUnit.unit)) =
      Sum.inl (Sum.inl (stateInput capture capture)) :=
  ⟨exactStep_apply capture (.inl PUnit.unit), exactStep_apply capture (.inr PUnit.unit)⟩

example (capture : Bits) :
    exactStep.of (stateInput capture (.inl PUnit.unit)) ≠
      Sum.inl (Sum.inl (stateInput capture capture)) := by
  rw [exactStep_apply]
  intro h
  cases Sum.inl.inj h
