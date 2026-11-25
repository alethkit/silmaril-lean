module

public import Silmaril.SSA.MLIR.StableHLO.Defs
import Silmaril.SSA.MLIR.Tensor.Thms

public section

namespace Silmaril.MLIR.StableHLO

variable {ty : TensorType}

/-- Signed and unsigned wrapping addition both agree with signless Arith
addition at the word representation. -/
theorem IntType.add_eq_addi (element : IntType) (lhs rhs : BitVec element.toArith.val) :
    element.add lhs rhs = Arith.BinOp.addi.denote lhs rhs := by
  cases element with
  | signed _ => simp only [IntType.add, Arith.BinOp.denote, BitVec.ofInt_add, BitVec.ofInt_toInt]
  | unsigned _ => exact (BitVec.add_def lhs rhs).symm

/-- Reading the corresponding dense `arith.constant` gives the source element. -/
theorem extract_constant (value : DenseValue ty) (i : Tensor.Index ty.shape) :
    Tensor.extract (Tensor.denseConstant (width := ty.width) value.elements) i =
      (constant value).elements i := rfl

/-- Tensor `arith.addi` with empty overflow flags preserves every element. -/
theorem extract_add (lhs rhs : Value ty) (i : Tensor.Index ty.shape) :
    Tensor.extract (Tensor.binary (width := ty.width) .addi lhs.elements rhs.elements) i =
      (add lhs rhs).elements i := by
  rw [Tensor.extract_binary]
  exact (ty.element.add_eq_addi (lhs.elements i) (rhs.elements i)).symm

/-- The closed scalar constant block produces the demanded element. -/
theorem lowerConstantAt_denote (value : DenseValue ty) (i : Tensor.Index ty.shape) :
    (lowerConstantAt value i).denote .nil = (constant value).elements i := rfl

/-- Two residual operand extracts and the existing scalar Arith block
produce the demanded element of `stablehlo.add`. -/
theorem lowerAdd_denote (lhs rhs : Value ty) (i : Tensor.Index ty.shape) :
    (Tensor.lowerExtractBinary .addi ty.width).denote
        (Tensor.extractOperands lhs.elements rhs.elements i) = (add lhs rhs).elements i := by
  rw [Tensor.lowerExtractBinary_denote, extract_add]

end Silmaril.MLIR.StableHLO
