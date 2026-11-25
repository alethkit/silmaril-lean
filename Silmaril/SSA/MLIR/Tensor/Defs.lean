module

public import Silmaril.SSA.MLIR.Arith.Defs

/-! # Static ranked tensors

Tensor values are functions on in-bounds multi-indices. This models logical
elements of `tensor.splat`, `tensor.extract`, dense `arith.constant`, and
flag-free tensor `arith.addi` and `arith.muli`.
-/

@[expose] public section

namespace Silmaril.MLIR.Tensor

universe u

abbrev Shape := List Nat

/-- The product of the coordinate types, with `Unit` as the empty product.
A zero extent contributes a `Fin 0` coordinate. -/
def Index : Shape → Type
  | [] => Unit
  | extent :: shape => Fin extent × Index shape

abbrev Tensor (shape : Shape) (α : Type u) := Index shape → α

/-- The value of an already matched dense `arith.constant` attribute. -/
def denseConstant {shape : Shape} {width : Arith.Width}
    (elements : Index shape → BitVec width.val) : Tensor shape (BitVec width.val) :=
  elements

/-- `tensor.splat` with a statically shaped result. -/
def splat {shape : Shape} {α : Type u} (value : α) : Tensor shape α :=
  fun _ => value

/-- `tensor.extract` on an index of the required rank and in bounds. -/
def extract {shape : Shape} {α : Type u} (tensor : Tensor shape α) (i : Index shape) : α :=
  tensor i

/-- Pull back logical elements along a map from output indices to input indices. -/
def reindex {src dst : Shape} {α : Type u} (indices : Index dst → Index src)
    (tensor : Tensor src α) : Tensor dst α :=
  fun i => tensor (indices i)

/-- Same-shape tensor `arith.addi` or `arith.muli` with empty overflow flags. -/
def binary {shape : Shape} {width : Arith.Width} (op : Arith.BinOp)
    (lhs rhs : Tensor shape (BitVec width.val)) : Tensor shape (BitVec width.val) :=
  fun i => op.denote (lhs i) (rhs i)

/-- The straight-line scalar block replacing the operation at the demanded index. -/
def lowerExtractBinary (op : Arith.BinOp) (width : Arith.Width) :
    Arith.Block [width, width] width :=
  .letOp (.binary op .here (.there .here)) (.yield .here)

/-- The residual extracts supply the two scalar block arguments. -/
def extractOperands {shape : Shape} {width : Arith.Width}
    (lhs rhs : Tensor shape (BitVec width.val)) (i : Index shape) : Arith.Env [width, width] :=
  .cons (extract lhs i) (.cons (extract rhs i) .nil)

end Silmaril.MLIR.Tensor
