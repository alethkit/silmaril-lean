module

public import Silmaril.SSA.MLIR.Tensor.Defs
import Silmaril.SSA.MLIR.Arith.Thms
import Silmaril.Proofs.SSA.MLIR.Tensor.Shape

public section

namespace Silmaril.MLIR.Tensor

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

universe u

variable {shape src dst : Shape} {α : Type u} {width : Arith.Width}

/-- A rank-zero tensor is determined by its single scalar element. -/
theorem eq_splat_rank_zero (tensor : Tensor [] α) : tensor = splat (extract tensor ()) := by
  funext i
  cases i
  rfl

/-- A zero extent anywhere in a shape rules out extracting an element. -/
theorem Index.false_of_zero_dim (h : 0 ∈ shape) (i : Index shape) : False :=
  Proofs.MLIR.Tensor.false_of_zero_dim h i

/-- All tensors of a given shape with zero elements are extensionally equal. -/
theorem eq_of_zero_dim (h : 0 ∈ shape) (lhs rhs : Tensor shape α) : lhs = rhs :=
  funext fun i => (Index.false_of_zero_dim h i).elim

theorem extract_denseConstant (elements : Tensor shape (BitVec width.val)) (i : Index shape) :
    extract (denseConstant (width := width) elements) i = elements i := rfl

theorem extract_splat (value : α) (i : Index shape) :
    extract (splat value) i = value := rfl

theorem extract_reindex (indices : Index dst → Index src) (tensor : Tensor src α) (i : Index dst) :
    extract (reindex indices tensor) i = extract tensor (indices i) := rfl

/-- Move the extraction to the inputs of a pointwise Arith operation. -/
theorem extract_binary (op : Arith.BinOp) (lhs rhs : Tensor shape (BitVec width.val))
    (i : Index shape) :
    extract (binary (width := width) op lhs rhs) i = op.denote (extract lhs i) (extract rhs i) := rfl

/-- The residual extracts and typed scalar block compute the demanded element. -/
theorem lowerExtractBinary_denote (op : Arith.BinOp) (lhs rhs : Tensor shape (BitVec width.val))
    (i : Index shape) :
    (lowerExtractBinary op width).denote (extractOperands lhs rhs i) =
      extract (binary (width := width) op lhs rhs) i := rfl

/-- With those scalar arguments, LambdaSSA evaluation yields exactly the demanded element. -/
theorem lowerExtractBinary_eval_iff (op : Arith.BinOp) (lhs rhs : Tensor shape (BitVec width.val))
    (i : Index shape) (label : Nat) (out : Value Arith.Atom) :
    Semantics.Region.Eval Arith.instr (extractOperands (width := width) lhs rhs i).toLambdaSSA
        (lowerExtractBinary op width).toLambdaSSA () label out () ↔
      label = 0 ∧ out = Arith.word (w := width) (extract (binary (width := width) op lhs rhs) i) := by
  rw [Arith.Block.toLambdaSSA_eval_iff, lowerExtractBinary_denote]

end Silmaril.MLIR.Tensor
