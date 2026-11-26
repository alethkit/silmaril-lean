module

@[expose] public section

namespace Silmaril.Languages.Starlark.Binary64

/-- Clear the sign bit of an already encoded binary64 value. -/
def abs (bits : UInt64) : UInt64 := bits &&& 0x7fffffffffffffff

/-- Both signed zeros are false. All other encodings, including NaNs, are true. -/
def truth (bits : UInt64) : Bool := abs bits != 0

/-- The positive-sign encoding with the input's exponent and trailing significand. -/
def Absolute (input output : UInt64) : Prop :=
  output.toNat = input.toNat % 2 ^ 63

/-- Zero magnitude is the sole false case, regardless of the input's sign. -/
inductive Truth (input : UInt64) : Bool → Prop where
  | zero : input.toNat % 2 ^ 63 = 0 → Truth input false
  | nonzero : input.toNat % 2 ^ 63 ≠ 0 → Truth input true

end Silmaril.Languages.Starlark.Binary64
