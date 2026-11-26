module

public import Silmaril.SSA.MLIR.Tensor.Defs

/-! # Shape values and static tensor shapes

Static rank and extent information constrains the shapes of concrete tensors.
Shape dialect values separately carry unknown ranks or extents and invalid
values. The operations here use mathematical extents and indices.
-/

@[expose] public section

namespace Silmaril.MLIR.Shape

universe u

/-- Compile-time information about the shapes of concrete tensor values. -/
inductive StaticShape where
  | unranked
  | ranked (extents : List (Option Nat))
  deriving DecidableEq, Repr

def StaticShape.ofTensorShape (shape : Tensor.Shape) : StaticShape :=
  .ranked (shape.map some)

/-- The rank and every specified extent must agree with the concrete shape. -/
def StaticShape.Admits : StaticShape → Tensor.Shape → Prop
  | .unranked, _ => True
  | .ranked extents, shape =>
      extents.length = shape.length ∧
        ∀ (dim size : Nat), extents[dim]? = some (some size) → shape[dim]? = some size

/-- Values of `!shape.size`. Error propagation yields an invalid size. -/
inductive Size where
  | known (value : Nat)
  | unknown
  | invalid
  deriving DecidableEq, Repr

/-- Values of `!shape.shape`. A missing extent in a ranked value is unknown.
An invalid shape carries no usable rank or extents. -/
inductive ShapeValue where
  | unranked
  | ranked (extents : List (Option Nat))
  | invalid
  deriving DecidableEq, Repr

/-- Results of admitted casts, including the cases with undefined behavior. -/
inductive Evaluation (α : Type) where
  | defined (value : α)
  | undefined
  deriving DecidableEq, Repr

/-- Embed a concrete shape as a fully known value. This is also the shape-valued
interpretation of `shape.const_shape` for a nonnegative extent list. -/
def ShapeValue.ofStatic (shape : Tensor.Shape) : ShapeValue :=
  .ranked (shape.map some)

/-- Recover a static tensor shape only when the runtime rank and extents are known. -/
def ShapeValue.toStatic? : ShapeValue → Option Tensor.Shape
  | .ranked extents => extents.mapM id
  | .unranked | .invalid => none

/-- An extent tensor has one axis, of length equal to the described shape's rank. -/
abbrev ExtentTensor := (rank : Nat) × Tensor.Tensor [rank] Nat

/-- The extent-tensor result of `shape.const_shape` on nonnegative extents. -/
def extentTensor (shape : Tensor.Shape) : ExtentTensor :=
  ⟨shape.length, fun i => shape.get i.1⟩

/-- Read the coordinates of an extent tensor in order. -/
def ExtentTensor.toShape (extents : ExtentTensor) : Tensor.Shape :=
  List.ofFn fun dim => extents.2 (dim, ())

/-- `shape.from_extent_tensor` on a rank-one tensor of nonnegative indices. -/
def fromExtentTensor (extents : ExtentTensor) : ShapeValue :=
  .ofStatic extents.toShape

/-- `shape.from_extents` on index operands. An index outside the nonnegative
fragment causes admission to fail. -/
def fromExtents? (extents : List Int) : Option ShapeValue :=
  (extents.mapM Int.toNat?).map ShapeValue.ofStatic

/-- The shape-valued interpretation of `shape.shape_of` on a static tensor. -/
def shapeOf {shape : Tensor.Shape} {α : Type u} (_ : Tensor.Tensor shape α) : ShapeValue :=
  .ofStatic shape

/-- `shape.rank` with a shape operand and a size result. -/
def rank : ShapeValue → Size
  | .unranked => .unknown
  | .ranked extents => .known extents.length
  | .invalid => .invalid

/-- `shape.get_extent` with a shape operand and a nonnegative index. An invalid
shape returns an invalid size. Unranked access and out-of-range indices are
outside this profile. -/
def getExtent? (shape : ShapeValue) (dim : Nat) : Option Size :=
  match shape with
  | .unranked => none
  | .ranked extents => extents[dim]?.map (fun extent => extent.elim .unknown .known)
  | .invalid => some .invalid

/-- `shape.num_elements` on a concrete or invalid shape. Shapes with unknown
rank or extents are outside this profile. -/
def numElements? : ShapeValue → Option Size
  | .invalid => some .invalid
  | shape => shape.toStatic?.map (fun extents => .known extents.prod)

/-- `shape.to_extent_tensor` on a concrete or invalid shape. The result is
undefined on an invalid shape. Shapes with unknown rank or extents are outside
this profile. -/
def toExtentTensor? : ShapeValue → Option (Evaluation ExtentTensor)
  | .invalid => some .undefined
  | shape => shape.toStatic?.map (fun extents => .defined (extentTensor extents))

/-- `shape.size_to_index` with a size operand. -/
def sizeToIndex : Size → Evaluation Int
  | .known value => .defined (Int.ofNat value)
  | .unknown | .invalid => .undefined

/-- `shape.index_to_size`. Negative indices give undefined behavior. -/
def indexToSize : Int → Evaluation Size
  | .ofNat value => .defined (.known value)
  | .negSucc _ => .undefined

end Silmaril.MLIR.Shape
