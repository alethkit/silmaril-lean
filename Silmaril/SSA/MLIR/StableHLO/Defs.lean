module

public import Silmaril.SSA.MLIR.Tensor.Defs

/-! # Static StableHLO integer tensors

Logical semantics of `stablehlo.constant` and `stablehlo.add` on static,
unencoded ranked tensors. Integer addition uses the wrapping behavior of the
StableHLO v1.13.0 reference interpreter.
-/

@[expose] public section

namespace Silmaril.MLIR.StableHLO

/-- The non-Boolean integer widths in the StableHLO element type contract. -/
inductive IntWidth where
  | w2 | w4 | w8 | w16 | w32 | w64

def IntWidth.toArith : IntWidth → Arith.Width
  | .w2 => ⟨2, by decide⟩
  | .w4 => ⟨4, by decide⟩
  | .w8 => ⟨8, by decide⟩
  | .w16 => ⟨16, by decide⟩
  | .w32 => ⟨32, by decide⟩
  | .w64 => ⟨64, by decide⟩

/-- `signed` models the spec's `siN`, spelled `iN` in the MLIR dialect.
`unsigned` models `uiN` in both. -/
inductive IntType where
  | signed (width : IntWidth)
  | unsigned (width : IntWidth)

/-- Erase signedness when representing elements as signless Arith words. -/
abbrev IntType.toArith : IntType → Arith.Width
  | .signed width | .unsigned width => width.toArith

/-- Interpret signed words as two's-complement integers and unsigned words as
natural numbers. Encode the sum back at the original width. -/
def IntType.add (ty : IntType) :
    BitVec ty.toArith.val → BitVec ty.toArith.val → BitVec ty.toArith.val :=
  match ty with
  | .signed width => fun lhs rhs => BitVec.ofInt width.toArith.val (lhs.toInt + rhs.toInt)
  | .unsigned width => fun lhs rhs => BitVec.ofNat width.toArith.val (lhs.toNat + rhs.toNat)

structure TensorType where
  shape : Tensor.Shape
  element : IntType

abbrev TensorType.width (ty : TensorType) : Arith.Width := ty.element.toArith

/-- Logical tensor elements indexed by the full StableHLO type. -/
structure Value (ty : TensorType) where
  elements : Tensor.Tensor ty.shape (BitVec ty.width.val)

/-- The decoded logical elements of a dense `value` attribute, with any splat
already expanded. The indexed type includes the shape and integer type. -/
structure DenseValue (ty : TensorType) where
  elements : Tensor.Tensor ty.shape (BitVec ty.width.val)

/-- `stablehlo.constant`, with the attribute and result sharing a type. -/
def constant {ty : TensorType} (value : DenseValue ty) : Value ty :=
  ⟨value.elements⟩

/-- `stablehlo.add`, with one common type for the operands and result and
no operation-specific attributes. -/
def add {ty : TensorType} (lhs rhs : Value ty) : Value ty :=
  ⟨fun i => ty.element.add (lhs.elements i) (rhs.elements i)⟩

/-- The scalar Arith block for a demanded element of `stablehlo.constant`. -/
def lowerConstantAt {ty : TensorType} (value : DenseValue ty) (i : Tensor.Index ty.shape) :
    Arith.Block [] ty.width :=
  .letOp (.constant (value.elements i)) (.yield .here)

end Silmaril.MLIR.StableHLO
