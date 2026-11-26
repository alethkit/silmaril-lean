module

public import Silmaril.SSA.MLIR.Shape.Extents.Defs
import Silmaril.SSA.MLIR.Shape.Thms
import Silmaril.Proofs.SSA.MLIR.Shape.Extents

/-! # Concrete extent operation contracts -/

public section

namespace Silmaril.MLIR.Shape

universe u

theorem concat?_ofStatic (lhs rhs : Tensor.Shape) :
    concat? (.ofStatic lhs) (.ofStatic rhs) = some (.ofStatic (lhs ++ rhs)) :=
  Proofs.MLIR.Shape.concat?_ofStatic lhs rhs

theorem concat?_invalid_left (rhs : ShapeValue) : concat? .invalid rhs = some .invalid := rfl

theorem concat?_invalid_right (lhs : ShapeValue) : concat? lhs .invalid = some .invalid := by
  cases lhs <;> rfl

theorem concatExtentTensor_toShape (lhs rhs : ExtentTensor) :
    (concatExtentTensor lhs rhs).toShape = lhs.toShape ++ rhs.toShape :=
  ExtentTensor.toShape_extentTensor _

theorem dimSize_ofNat {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (axis : Nat) :
    dimSize tensor (Int.ofNat axis) = (shape[axis]?.map Size.known).getD .invalid :=
  Proofs.MLIR.Shape.dimSize_ofNat tensor axis

theorem dimSize_eq_known_iff {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (index : Int) (extent : Nat) :
    dimSize tensor index = .known extent ↔
      ∃ axis : Nat, index = (axis : Int) ∧ shape[axis]? = some extent :=
  Proofs.MLIR.Shape.dimSize_eq_known_iff tensor index extent

theorem dimSize_eq_invalid_iff {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (index : Int) :
    dimSize tensor index = .invalid ↔ index < 0 ∨ (shape.length : Int) ≤ index :=
  Proofs.MLIR.Shape.dimSize_eq_invalid_iff tensor index

theorem dimIndex_eq_defined_iff {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (index result : Int) :
    dimIndex tensor index = .defined result ↔
      ∃ axis extent : Nat, index = (axis : Int) ∧ shape[axis]? = some extent ∧ result = (extent : Int) :=
  Proofs.MLIR.Shape.dimIndex_eq_defined_iff tensor index result

theorem dimIndex_eq_undefined_iff {shape : Tensor.Shape} {α : Type u}
    (tensor : Tensor.Tensor shape α) (index : Int) :
    dimIndex tensor index = .undefined ↔ index < 0 ∨ (shape.length : Int) ≤ index :=
  Proofs.MLIR.Shape.dimIndex_eq_undefined_iff tensor index

/-- A query before the boundary of an appended shape reads the left operand. -/
theorem dimSize_append_left {lhs rhs : Tensor.Shape} {α β : Type u}
    (whole : Tensor.Tensor (lhs ++ rhs) α) (left : Tensor.Tensor lhs β)
    {axis : Nat} (inBounds : axis < lhs.length) :
    dimSize whole (Int.ofNat axis) = dimSize left (Int.ofNat axis) := by
  simp only [dimSize_ofNat, List.getElem?_append_left inBounds]

/-- An offset query reads the right operand, including its out-of-range case. -/
theorem dimSize_append_right {lhs rhs : Tensor.Shape} {α β : Type u}
    (whole : Tensor.Tensor (lhs ++ rhs) α) (right : Tensor.Tensor rhs β) (axis : Nat) :
    dimSize whole (Int.ofNat (lhs.length + axis)) = dimSize right (Int.ofNat axis) := by
  simp only [dimSize_ofNat, List.getElem?_append_right (Nat.le_add_right lhs.length axis),
    Nat.add_sub_cancel_left]

/-- The signed range is inclusive. Negative positions count from the end. -/
theorem splitPoint?_eq_some_iff (rank : Nat) (index : Int) (point : Nat) :
    splitPoint? rank index = some point ↔
      -(rank : Int) ≤ index ∧ index ≤ (rank : Int) ∧
        (point : Int) = (if index < 0 then (rank : Int) + index else index) :=
  Proofs.MLIR.Shape.splitPoint?_eq_some_iff rank index point

theorem splitPoint?_eq_none_iff (rank : Nat) (index : Int) :
    splitPoint? rank index = none ↔ index < -(rank : Int) ∨ (rank : Int) < index :=
  Proofs.MLIR.Shape.splitPoint?_eq_none_iff rank index

theorem splitAtConcrete?_eq_some_iff (shape lhs rhs : Tensor.Shape) (index : Int) :
    splitAtConcrete? shape index = some (lhs, rhs) ↔
      splitPoint? shape.length index = some lhs.length ∧ shape = lhs ++ rhs :=
  Proofs.MLIR.Shape.splitAtConcrete?_eq_some_iff shape lhs rhs index

theorem splitAtConcrete?_lookup_left {shape lhs rhs : Tensor.Shape} {index : Int}
    (split : splitAtConcrete? shape index = some (lhs, rhs)) {axis : Nat}
    (inBounds : axis < lhs.length) : shape[axis]? = lhs[axis]? := by
  rw [((splitAtConcrete?_eq_some_iff _ _ _ _).mp split).2, List.getElem?_append_left inBounds]

theorem splitAtConcrete?_lookup_right {shape lhs rhs : Tensor.Shape} {index : Int}
    (split : splitAtConcrete? shape index = some (lhs, rhs)) (axis : Nat) :
    shape[lhs.length + axis]? = rhs[axis]? := by
  rw [((splitAtConcrete?_eq_some_iff _ _ _ _).mp split).2,
    List.getElem?_append_right (Nat.le_add_right lhs.length axis), Nat.add_sub_cancel_left]

theorem splitAt?_ofStatic_eq_some_iff (shape lhs rhs : Tensor.Shape) (index : Int) :
    splitAt? (.ofStatic shape) index = some (.ofStatic lhs, .ofStatic rhs) ↔
      splitPoint? shape.length index = some lhs.length ∧ shape = lhs ++ rhs :=
  Proofs.MLIR.Shape.splitAt?_ofStatic_eq_some_iff shape lhs rhs index

theorem splitAt?_ofStatic_eq_none_iff (shape : Tensor.Shape) (index : Int) :
    splitAt? (.ofStatic shape) index = none ↔ index < -(shape.length : Int) ∨ (shape.length : Int) < index :=
  Proofs.MLIR.Shape.splitAt?_ofStatic_eq_none_iff shape index

theorem splitAtExtentTensor_eq_defined_iff (shape lhs rhs : ExtentTensor) (index : Int) :
    splitAtExtentTensor shape index = .defined (lhs, rhs) ↔
      splitPoint? shape.toShape.length index = some lhs.toShape.length ∧
        shape.toShape = lhs.toShape ++ rhs.toShape :=
  Proofs.MLIR.Shape.splitAtExtentTensor_eq_defined_iff shape lhs rhs index

theorem splitAtExtentTensor_eq_undefined_iff (shape : ExtentTensor) (index : Int) :
    splitAtExtentTensor shape index = .undefined ↔ index < -(shape.1 : Int) ∨ (shape.1 : Int) < index :=
  Proofs.MLIR.Shape.splitAtExtentTensor_eq_undefined_iff shape index

theorem splitAt?_concat?_ofStatic (lhs rhs : Tensor.Shape) :
    (concat? (.ofStatic lhs) (.ofStatic rhs)).bind (fun shape => splitAt? shape (Int.ofNat lhs.length)) =
      some (.ofStatic lhs, .ofStatic rhs) := by
  rw [concat?_ofStatic, Option.bind_some, splitAt?_ofStatic_eq_some_iff]
  simp [splitPoint?]

theorem concat?_of_splitAt? {shape lhs rhs : Tensor.Shape} {index : Int}
    (split : splitAt? (.ofStatic shape) index = some (.ofStatic lhs, .ofStatic rhs)) :
    concat? (.ofStatic lhs) (.ofStatic rhs) = some (.ofStatic shape) := by
  rw [concat?_ofStatic, ((splitAt?_ofStatic_eq_some_iff _ _ _ _).mp split).2]

theorem splitAtExtentTensor_concatExtentTensor (lhs rhs : ExtentTensor) :
    splitAtExtentTensor (concatExtentTensor lhs rhs) (Int.ofNat lhs.1) = .defined (lhs, rhs) := by
  rw [splitAtExtentTensor_eq_defined_iff, concatExtentTensor_toShape]
  simp [splitPoint?, ExtentTensor.toShape]

theorem concatExtentTensor_of_splitAtExtentTensor {shape lhs rhs : ExtentTensor} {index : Int}
    (split : splitAtExtentTensor shape index = .defined (lhs, rhs)) :
    concatExtentTensor lhs rhs = shape := by
  rw [concatExtentTensor, ← ((splitAtExtentTensor_eq_defined_iff _ _ _ _).mp split).2,
    ExtentTensor.extentTensor_toShape]

end Silmaril.MLIR.Shape
