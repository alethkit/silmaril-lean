module

public import Init.Data.Rat.Lemmas

/-! # Cambridge Chapter 3, Theorem 8

The mathematical induction example on pp. 33–34 of `sewell2026semantics`
ranges over the natural numbers, including zero. The sum at zero is empty.
The induction uses the doubled equality over naturals. The printed formula
uses the rational coefficient `1 / 2`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.ArithmeticSeries

/-- The sum of the first `n` positive integers. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem twice_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      calc
        2 * sumTo (k + 1) = 2 * sumTo k + 2 * (k + 1) :=
          Nat.mul_add 2 (sumTo k) (k + 1)
        _ = k * (k + 1) + 2 * (k + 1) := by rw [ih]
        _ = (k + 2) * (k + 1) := (Nat.add_mul k 2 (k + 1)).symm
        _ = (k + 1) * (k + 2) := Nat.mul_comm _ _

/-- Theorem 8 as printed, with the natural-number sum viewed in the rationals. -/
theorem sumTo_formula (n : Nat) :
    (sumTo n : Rat) = (1 / 2 : Rat) * (n : Rat) * ((n : Rat) + 1) := by
  have doubled : 2 * (sumTo n : Rat) = (n : Rat) * ((n : Rat) + 1) := by
    simpa only [Rat.natCast_mul, Rat.natCast_add, Rat.natCast_ofNat] using
      congrArg (fun m : Nat => (m : Rat)) (twice_sumTo n)
  calc
    (sumTo n : Rat) = (1 / 2 : Rat) * (2 * (sumTo n : Rat)) := by
      rw [← Rat.mul_assoc, Rat.div_mul_cancel (by decide : (2 : Rat) ≠ 0), Rat.one_mul]
    _ = (1 / 2 : Rat) * (n : Rat) * ((n : Rat) + 1) := by
      rw [doubled, ← Rat.mul_assoc]

end Silmaril.Courses.Cambridge.L1.ArithmeticSeries
