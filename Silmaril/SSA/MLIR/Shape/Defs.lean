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

/-- Results of admitted operations that may have undefined behavior. -/
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

/-- Pair the axes of two concrete shapes from the right, padding with leading ones. -/
def alignedExtents (lhs rhs : Tensor.Shape) : List (Nat × Nat) :=
  let rank := max lhs.length rhs.length
  (lhs.leftpad rank 1).zip (rhs.leftpad rank 1)

/-- The concrete binary `shape.broadcast` rule. A pair of unequal non-unit
extents fails. The non-unit extent wins over one, including when it is zero. -/
def broadcastConcrete? (lhs rhs : Tensor.Shape) : Option Tensor.Shape :=
  let axes := alignedExtents lhs rhs
  if axes.all (fun (a, b) => a == b || a == 1 || b == 1) then
    some (axes.map fun (a, b) => if a = 1 then b else a)
  else none

/-- Every axis agrees or has a unit extent on one side after left padding. -/
def BroadcastCompatible (lhs rhs : Tensor.Shape) : Prop :=
  let rank := max lhs.length rhs.length
  ∀ dim : Fin rank,
    let a := (lhs.leftpad rank 1)[dim.val]?.getD 1
    let b := (rhs.leftpad rank 1)[dim.val]?.getD 1
    a = b ∨ a = 1 ∨ b = 1

/-- A compatible broadcast has the larger rank and the specified extent at each
aligned axis. -/
def BroadcastsTo (lhs rhs result : Tensor.Shape) : Prop :=
  let rank := max lhs.length rhs.length
  BroadcastCompatible lhs rhs ∧ result.length = rank ∧
    ∀ dim : Fin rank,
      let a := (lhs.leftpad rank 1)[dim.val]?.getD 1
      let b := (rhs.leftpad rank 1)[dim.val]?.getD 1
      result[dim.val]? = some (if a = 1 then b else a)

/-- Binary `shape.broadcast` with a `!shape.shape` result. Invalid operands
propagate. Without an invalid operand, both shapes must be concrete. -/
def broadcast? : ShapeValue → ShapeValue → Option ShapeValue
  | .invalid, _ | _, .invalid => some .invalid
  | lhs, rhs => do
      let lhs ← lhs.toStatic?
      let rhs ← rhs.toStatic?
      return ((broadcastConcrete? lhs rhs).map ShapeValue.ofStatic).getD .invalid

/-- Binary `shape.broadcast` with two concrete extent tensors and an extent
tensor result. An incompatible pair has no defined extent tensor result. -/
def broadcastExtentTensor (lhs rhs : ExtentTensor) : Evaluation ExtentTensor :=
  match broadcastConcrete? lhs.toShape rhs.toShape with
  | some result => .defined (extentTensor result)
  | none => .undefined

/-- Binary `shape.is_broadcastable` on two concrete shape views. Unknown or
invalid operands are outside the model. Use `fromExtentTensor` for an extent
tensor operand. -/
def isBroadcastable? (lhs rhs : ShapeValue) : Option Bool := do
  let lhs ← lhs.toStatic?
  let rhs ← rhs.toStatic?
  return (broadcastConcrete? lhs rhs).isSome

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
