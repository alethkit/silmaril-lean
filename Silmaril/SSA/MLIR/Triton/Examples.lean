module

import Silmaril.SSA.MLIR.Triton.Thms

namespace Silmaril.MLIR.Gluon.Examples

private def arg : Value .sizePerThread1 := ⟨fun _ => 0⟩

private def range : Expr .sizePerThread1 .sizePerThread1 :=
  .arange .sizePerThread1 ⟨10, by decide⟩

private def converted : Expr .sizePerThread1 .sizePerThread2 :=
  .convertLayout .sizePerThread2 range

-- Lane 3, register 1 denotes coordinate 35 before conversion and 7 after it.
example : (range.denote arg).atSlot ⟨3, 1⟩ = 45 := rfl
example : (converted.denote arg).atSlot ⟨3, 1⟩ = 17 := rfl

-- Extraction by logical coordinate agrees with the erased `tt.make_range`.
example : Tensor.extract (converted.denote arg).toTensor (7, ()) = 17 :=
  converted.extract_denote_eq_erase arg (7, ())

example : Tensor.extract
    ((Expr.full .sizePerThread2 0xffff_ffff).denote arg).toTensor (63, ()) = 0xffff_ffff := rfl

end Silmaril.MLIR.Gluon.Examples
