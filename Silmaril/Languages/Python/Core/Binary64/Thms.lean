module

public import Silmaril.Languages.Python.Core.Binary64.Defs
import Silmaril.Proofs.Languages.Python.Core.Binary64.Division

public section
namespace Silmaril.Languages.Python.Core.Binary64

open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.AdjacentRounding (NearestEven)
open Silmaril.Numeric.Ieee754.RationalRounding
open Silmaril.Numeric.Ieee754.Binary64Signs (magnitudeBits)

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
