module

import Silmaril.SSA.MLIR.StableHLO.Thms
import Silmaril.SSA.MLIR.Tensor.Thms

namespace Silmaril.MLIR.StableHLO.Examples

private def matrix : TensorType := ⟨[2, 2], .signed .w8⟩

private def entries : DenseValue matrix :=
  ⟨fun (row, col, ()) =>
    if row.val = 0 then
      if col.val = 0 then 127#8 else BitVec.ofInt 8 (-3)
    else if col.val = 0 then 42#8 else 2#8⟩

private def one : DenseValue matrix := ⟨fun _ => 1#8⟩

-- Two distinct coordinates of a dense tensor, including signed wraparound.
example : ((add (constant entries) (constant one)).elements (0, 0, ())).toInt = -128 := by
  decide

example : ((add (constant entries) (constant one)).elements (0, 1, ())).toInt = -2 := by
  decide

example : (lowerConstantAt entries (1, 0, ())).denote .nil = 42#8 :=
  lowerConstantAt_denote entries (1, 0, ())

private def scalar : TensorType := ⟨[], .unsigned .w8⟩
private def maxByte : Value scalar := constant ⟨fun () => 255#8⟩
private def two : Value scalar := constant ⟨fun () => 2#8⟩

-- The rank-zero tensor has one element, which wraps through scalar Arith.
example : (Tensor.lowerExtractBinary .addi scalar.width).denote
    (Tensor.extractOperands maxByte.elements two.elements ()) = 1#8 :=
  lowerAdd_denote maxByte two ()

private def empty : TensorType := ⟨[2, 0], .unsigned .w4⟩

example (lhs rhs : Value empty) : (add lhs rhs).elements = lhs.elements :=
  Tensor.eq_of_zero_dim (by decide : 0 ∈ empty.shape) _ _

end Silmaril.MLIR.StableHLO.Examples
