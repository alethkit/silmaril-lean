module

public import Silmaril.Languages.Python.Core.Binary64.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Core.Binary64

open Silmaril.Languages.Python.Core.Binary64
open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.AdjacentRounding (NearestEven)
open Silmaril.Numeric.Ieee754.RationalRounding
open Silmaril.Numeric.Ieee754.Binary64Signs (magnitudeBits exponent_magnitude)

private theorem quotientMagnitude_eq_abs (numerator divisor : Int) :
    quotientMagnitude numerator divisor = |(numerator : ℚ) / (divisor : ℚ)| := by
  simp only [quotientMagnitude, abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem quotient_nonnegative (numerator divisor : Int) :
    0 ≤ quotientMagnitude numerator divisor := by
  unfold quotientMagnitude
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem rounded_finite_iff (negative : Bool) {magnitude : ℚ} (nonnegative : 0 ≤ magnitude) :
    (F64.ofBits (roundSigned negative magnitude)).IsFinite ↔ magnitude < overflowThreshold := by
  have noOverflow := (not_congr (roundIndex_overflow_iff magnitude nonnegative)).trans not_le
  rw [← noOverflow, F64.IsFinite, exponent_magnitude]
  simp only [F64.ofBits, magnitudeBits_roundSigned, roundPositive_toNat]
  have range := roundIndex_le_limit magnitude
  change roundIndex magnitude / (2 ^ 52 : Nat) ≠ 0x7ff ↔ roundIndex magnitude ≠ limit
  unfold limit at range ⊢
  norm_num only [Nat.reducePow]
  omega

theorem trueDivide_zeroDivision_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .zeroDivisionError ↔ divisor = 0 := by
  by_cases zero : divisor = 0
  · simp [trueDivide, zero]
  · simp only [trueDivide, zero, ↓reduceIte, iff_false]
    split <;> simp

theorem trueDivide_overflow_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .overflowError ↔
      divisor ≠ 0 ∧ overflowThreshold ≤ quotientMagnitude numerator divisor := by
  by_cases zero : divisor = 0
  · simp [trueDivide, zero]
  have finite := rounded_finite_iff (quotientNegative numerator divisor) (quotient_nonnegative numerator divisor)
  by_cases below : quotientMagnitude numerator divisor < overflowThreshold
  · simp [trueDivide, zero, F64.Finite.ofRaw?, finite.mpr below, not_le_of_gt below]
  · simp [trueDivide, zero, F64.Finite.ofRaw?, mt finite.mp below, le_of_not_gt below]

theorem trueDivide_ok_iff (numerator divisor : Int) (result : F64.Finite) :
    trueDivide numerator divisor = .ok result ↔
      divisor ≠ 0 ∧ quotientMagnitude numerator divisor < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned (quotientNegative numerator divisor) (quotientMagnitude numerator divisor)) := by
  by_cases zero : divisor = 0
  · simp [trueDivide, zero]
  have finite := rounded_finite_iff (quotientNegative numerator divisor) (quotient_nonnegative numerator divisor)
  by_cases below : quotientMagnitude numerator divisor < overflowThreshold
  · simp [trueDivide, zero, F64.Finite.ofRaw?, finite.mpr below, below, Subtype.ext_iff, eq_comm]
  · simp [trueDivide, zero, F64.Finite.ofRaw?, mt finite.mp below, below]

theorem trueDivide_nearestEven {numerator divisor : Int} {result : F64.Finite}
    (computed : trueDivide numerator divisor = .ok result) :
    result.val.signBit = quotientNegative numerator divisor ∧
      NearestEven magnitude |(numerator : ℚ) / (divisor : ℚ)|
        (magnitudeBits result.val.bits).toNat := by
  obtain ⟨_, below, bits⟩ := (trueDivide_ok_iff numerator divisor result).mp computed
  rw [bits, ← quotientMagnitude_eq_abs]
  exact ⟨signBit_roundSigned _ _,
    (roundSigned_nearestEven _ _ (quotient_nonnegative numerator divisor) below).2⟩

end Silmaril.Proofs.Languages.Python.Core.Binary64
