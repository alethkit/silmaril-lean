module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Defs

/-! # Conway star and the scalar two-cycle obstruction -/

public section

namespace Silmaril.Calco2019.CounterSemiring.Scalar

instance : CommSemiring Scalar where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  nsmul := nsmulRec

theorem star_add (a b : Scalar) : star (a + b) = star a * star (b * star a) := by
  cases a <;> cases b <;> rfl

theorem star_mul (a b : Scalar) : star (a * b) = 1 + a * star (b * a) * b := by
  cases a <;> cases b <;> rfl

/-- The scalar group equation for a cycle of two is independent of the
scalar Conway identities. -/
theorem two_cycle_counterexample :
    star generator ≠ (1 + generator) * star (generator * generator) := by decide

end Silmaril.Calco2019.CounterSemiring.Scalar
