module

public import Silmaril.Numeric.Ieee754.SignedRationalRounding

/-! # Python integer true division

Round the magnitude of the exact integer quotient to binary64 once.
The sign is separate so division and underflow can produce negative zero.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Core.Binary64

open Silmaril.Numeric.Ieee754 (F64)
open Silmaril.Numeric.Ieee754.RationalRounding (roundSigned)

inductive DivisionError where
  | zeroDivisionError
  | overflowError
  deriving DecidableEq, Repr

def quotientMagnitude (numerator divisor : Int) : ℚ :=
  (numerator.natAbs : ℚ) / (divisor.natAbs : ℚ)

def quotientNegative (numerator divisor : Int) : Bool :=
  decide (numerator < 0) != decide (divisor < 0)

/-- Python's integer `/` returns a finite float, or raises if the divisor
is zero or rounding reaches infinity. -/
def trueDivide (numerator divisor : Int) : Except DivisionError F64.Finite :=
  if divisor = 0 then .error .zeroDivisionError
  else
    let bits := roundSigned (quotientNegative numerator divisor) (quotientMagnitude numerator divisor)
    match F64.Finite.ofRaw? (F64.ofBits bits) with
    | some result => .ok result
    | none => .error .overflowError

end Silmaril.Languages.Python.Core.Binary64
