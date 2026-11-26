module

public import Silmaril.Languages.Starlark.Binary64.Defs
import Silmaril.Proofs.Languages.Starlark.Binary64.Eval

public section

namespace Silmaril.Languages.Starlark.Binary64

/-- The bit-mask implementation returns exactly the specified magnitude encoding. -/
theorem absolute_iff_abs (input output : UInt64) : Absolute input output ↔ abs input = output :=
  Proofs.Languages.Starlark.Binary64.absolute_iff_abs input output

/-- The truth rules agree with the result of testing the magnitude encoding. -/
theorem truth_iff_truth (input : UInt64) (out : Bool) : Truth input out ↔ truth input = out :=
  Proofs.Languages.Starlark.Binary64.truth_iff_truth input out

/-- Exactly the two signed-zero encodings are false. -/
theorem truth_false_iff_signed_zero (input : UInt64) :
    truth input = false ↔ input = 0 ∨ input = 0x8000000000000000 :=
  Proofs.Languages.Starlark.Binary64.truth_false_iff_signed_zero input

end Silmaril.Languages.Starlark.Binary64
