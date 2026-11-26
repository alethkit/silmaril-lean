module

public import Silmaril.SSA.MLIR.Shape.Defs

/-! # Concrete extent construction and queries -/

@[expose] public section

namespace Silmaril.MLIR.Shape

universe u

/-- Shape-valued `shape.concat`. An invalid operand propagates. Otherwise both
operands must have known ranks and extents. -/
def concat? : ShapeValue → ShapeValue → Option ShapeValue
  | .invalid, _ | _, .invalid => some .invalid
  | lhs, rhs => do
      let left ← lhs.toStatic?
      let right ← rhs.toStatic?
      return .ofStatic (left ++ right)

/-- `shape.concat` with two concrete extent tensors and an extent tensor result. -/
def concatExtentTensor (lhs rhs : ExtentTensor) : ExtentTensor :=
  extentTensor (lhs.toShape ++ rhs.toShape)

/-- `shape.dim` on a static tensor with an `index` operand and a `!shape.size`
result. Negative or out-of-range indices give an invalid size. -/
def dimSize {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α) : Int → Size
  | .ofNat axis => (getExtent? (shapeOf tensor) axis).getD .invalid
  | .negSucc _ => .invalid

/-- `shape.dim` with an `index` result. An out-of-range index leaves the result undefined. -/
def dimIndex {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (axis : Int) : Evaluation Int :=
  sizeToIndex (dimSize tensor axis)

/-- Normalize a signed split position in `[-rank, rank]` to a prefix length. -/
def splitPoint? (rank : Nat) : Int → Option Nat
  | .ofNat point => if point ≤ rank then some point else none
  | .negSucc n => if n + 1 ≤ rank then some (rank - (n + 1)) else none

/-- The concrete split at an admitted position. -/
def splitAtConcrete? (shape : Tensor.Shape) (index : Int) : Option (Tensor.Shape × Tensor.Shape) :=
  (splitPoint? shape.length index).map fun point => shape.splitAt point

/-- `shape.split_at` with two shape results, on a concrete shape and an in-range
`index` operand. The outer option records admission to this fragment. -/
def splitAt? (shape : ShapeValue) (index : Int) : Option (ShapeValue × ShapeValue) :=
  shape.toStatic?.bind fun concrete =>
    (splitAtConcrete? concrete index).map fun (head, tail) => (.ofStatic head, .ofStatic tail)

/-- `shape.split_at` with an extent tensor operand and two extent tensor results.
An out-of-range `index` operand leaves the results undefined. -/
def splitAtExtentTensor (shape : ExtentTensor) (index : Int) : Evaluation (ExtentTensor × ExtentTensor) :=
  match splitAtConcrete? shape.toShape index with
  | some (head, tail) => .defined (extentTensor head, extentTensor tail)
  | none => .undefined

end Silmaril.MLIR.Shape
