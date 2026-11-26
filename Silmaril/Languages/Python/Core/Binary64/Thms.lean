module

public import Silmaril.Languages.Python.Core.Binary64.Defs
import Silmaril.Proofs.Languages.Python.Core.Binary64.Division
import Silmaril.Proofs.Languages.Python.Core.Binary64.Equality

public section
namespace Silmaril.Languages.Python.Core.Binary64

open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.AdjacentRounding (NearestEven)
open Silmaril.Numeric.Ieee754.RationalRounding
open Silmaril.Numeric.Ieee754.Binary64Signs (magnitudeBits)

theorem ofDecimal_ok_iff (negative : Bool) (coefficient : Nat) (exponent : Int) (result : F64.Finite) :
    ofDecimal? negative coefficient exponent = some result ↔
      decimalInProfile coefficient exponent ∧ decimalMagnitude coefficient exponent < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned negative (decimalMagnitude coefficient exponent)) :=
  Proofs.Languages.Python.Core.Binary64.ofDecimal_ok_iff negative coefficient exponent result

theorem ofDecimal_nearestEven {negative : Bool} {coefficient : Nat} {exponent : Int} {result : F64.Finite}
    (computed : ofDecimal? negative coefficient exponent = some result) :
    result.val.signBit = negative ∧
      NearestEven magnitude (decimalMagnitude coefficient exponent) (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.ofDecimal_nearestEven computed

theorem finite_has_exact_value (value : F64.Finite) : ∃ q : ℚ, value.val.toRat? = some q :=
  Proofs.Languages.Python.Core.Binary64.finite_has_exact_value value

theorem equal_eq_ieee (left right : F64.Finite) :
    equal left right = true ↔ left.val.equal right.val = true :=
  Proofs.Languages.Python.Core.Binary64.equal_eq_ieee left right

theorem equalInt_iff_exact (left : F64.Finite) (right : Int) :
    equalInt left right = true ↔ left.val.toRat? = some (right : ℚ) := by simp [equalInt]

theorem signed_zeros_equal :
    equal ⟨F64.ofBits 0, by decide⟩ ⟨F64.ofBits 0x8000000000000000, by decide⟩ = true := by
  decide +kernel

theorem trueDivide_zeroDivision_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .zeroDivisionError ↔ divisor = 0 :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_zeroDivision_iff numerator divisor

theorem trueDivide_overflow_iff (numerator divisor : Int) :
    trueDivide numerator divisor = .error .overflowError ↔
      divisor ≠ 0 ∧ overflowThreshold ≤ quotientMagnitude numerator divisor :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_overflow_iff numerator divisor

theorem trueDivide_ok_iff (numerator divisor : Int) (result : F64.Finite) :
    trueDivide numerator divisor = .ok result ↔
      divisor ≠ 0 ∧ quotientMagnitude numerator divisor < overflowThreshold ∧
        result.val = F64.ofBits (roundSigned (quotientNegative numerator divisor) (quotientMagnitude numerator divisor)) :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_ok_iff numerator divisor result

theorem trueDivide_nearestEven {numerator divisor : Int} {result : F64.Finite}
    (computed : trueDivide numerator divisor = .ok result) :
    result.val.signBit = quotientNegative numerator divisor ∧
      NearestEven magnitude |(numerator : ℚ) / (divisor : ℚ)|
        (magnitudeBits result.val.bits).toNat :=
  Proofs.Languages.Python.Core.Binary64.trueDivide_nearestEven computed

end Silmaril.Languages.Python.Core.Binary64
