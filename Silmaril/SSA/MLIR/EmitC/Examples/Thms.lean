module

public import Silmaril.SSA.MLIR.EmitC.Thms

/-! Signed endpoints, overflow in both directions, and admission failure. -/

namespace Silmaril.MLIR.EmitC.Examples

private def add : Add [i32, i32] := ⟨.here, .there .here⟩

private def inputs (lhs rhs : BitVec 32) : Arith.Env [i32, i32] :=
  .cons lhs (.cons rhs .nil)

example : add.eval .signedInt (inputs 0x7ffffffe#32 1#32) = .ok 2147483647 := rfl

example : (add.toArith.denote (inputs 0x80000001#32 0xffffffff#32)).toInt = -2147483648 :=
  add.toArith_signed_of_eval .signedInt _ _ rfl

example : add.eval .signedInt (inputs 0x7fffffff#32 1#32) = .error .signedOverflow := rfl
example : add.eval .signedInt (inputs 0x80000000#32 0xffffffff#32) =
    .error .signedOverflow := rfl

-- The flag-free target still wraps on this excluded input.
example : add.toArith.denote (inputs 0x7fffffff#32 1#32) = 0x80000000#32 := rfl

example : add.eval .unsupported (inputs 1#32 2#32) = .error .unsupportedABI := rfl

end Silmaril.MLIR.EmitC.Examples
