module

public import Silmaril.SSA.MLIR.Shape.Extents.Defs
import Silmaril.SSA.MLIR.Shape.Thms

public section

namespace Silmaril.Proofs.MLIR.Shape

open Silmaril.MLIR Shape

universe u

theorem concat?_ofStatic (lhs rhs : Tensor.Shape) :
    concat? (.ofStatic lhs) (.ofStatic rhs) = some (.ofStatic (lhs ++ rhs)) := by
  change (do
    let left ← (ShapeValue.ofStatic lhs).toStatic?
    let right ← (ShapeValue.ofStatic rhs).toStatic?
    return ShapeValue.ofStatic (left ++ right)) = _
  simp [ShapeValue.toStatic?_ofStatic]

theorem dimSize_ofNat {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (axis : Nat) :
    dimSize tensor (Int.ofNat axis) = (shape[axis]?.map Size.known).getD .invalid := by
  simp only [dimSize, shapeOf, getExtent?_ofStatic]

theorem dimSize_eq_known_iff {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (index : Int) (extent : Nat) :
    dimSize tensor index = .known extent ↔
      ∃ axis : Nat, index = (axis : Int) ∧ shape[axis]? = some extent := by
  cases index with
  | ofNat axis =>
    rw [dimSize_ofNat]
    cases lookup : shape[axis]? <;> simp [Int.ofNat_inj, lookup]
  | negSucc n => simp [dimSize]

theorem dimSize_eq_invalid_iff {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (index : Int) :
    dimSize tensor index = .invalid ↔ index < 0 ∨ (shape.length : Int) ≤ index := by
  cases index with
  | ofNat axis =>
    rw [dimSize_ofNat]
    have missing : (shape[axis]?.map Size.known).getD .invalid = .invalid ↔ shape[axis]? = none := by
      cases shape[axis]? <;> simp
    rw [missing]
    simp <;> omega
  | negSucc n => simp [dimSize]

theorem dimIndex_eq_defined_iff {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α)
    (index result : Int) :
    dimIndex tensor index = .defined result ↔
      ∃ axis extent : Nat, index = (axis : Int) ∧ shape[axis]? = some extent ∧ result = (extent : Int) := by
  have exactSize (size : Size) :
      sizeToIndex size = .defined result ↔ ∃ n : Nat, size = .known n ∧ result = (n : Int) := by
    cases size <;> simp [sizeToIndex, eq_comm]
  simp only [dimIndex, exactSize, dimSize_eq_known_iff]
  exact ⟨fun ⟨extent, ⟨axis, indexEq, lookup⟩, valueEq⟩ => ⟨axis, extent, indexEq, lookup, valueEq⟩,
    fun ⟨axis, extent, indexEq, lookup, valueEq⟩ => ⟨extent, ⟨axis, indexEq, lookup⟩, valueEq⟩⟩

theorem dimIndex_eq_undefined_iff {shape : Tensor.Shape} {α : Type u}
    (tensor : Tensor.Tensor shape α) (index : Int) :
    dimIndex tensor index = .undefined ↔ index < 0 ∨ (shape.length : Int) ≤ index := by
  rw [← dimSize_eq_invalid_iff tensor index]
  cases index with
  | ofNat axis =>
    rw [dimIndex, dimSize_ofNat]
    cases shape[axis]? <;> simp [sizeToIndex]
  | negSucc n => simp [dimIndex, dimSize, sizeToIndex]

theorem splitPoint?_eq_some_iff (rank : Nat) (index : Int) (point : Nat) :
    splitPoint? rank index = some point ↔
      -(rank : Int) ≤ index ∧ index ≤ (rank : Int) ∧
        (point : Int) = (if index < 0 then (rank : Int) + index else index) := by
  cases index with
  | ofNat n =>
    by_cases fits : n ≤ rank <;> simp [splitPoint?, fits] <;> omega
  | negSucc n =>
    by_cases fits : n + 1 ≤ rank <;> simp [splitPoint?, fits, Int.negSucc_lt_zero] <;> omega

theorem splitPoint?_eq_none_iff (rank : Nat) (index : Int) :
    splitPoint? rank index = none ↔ index < -(rank : Int) ∨ (rank : Int) < index := by
  cases index with
  | ofNat n => by_cases fits : n ≤ rank <;> simp [splitPoint?, fits] <;> omega
  | negSucc n => by_cases fits : n + 1 ≤ rank <;> simp [splitPoint?, fits] <;> omega

private theorem splitPoint?_le_rank {rank point : Nat} {index : Int}
    (success : splitPoint? rank index = some point) : point ≤ rank := by
  obtain ⟨_, upper, pointEq⟩ := (splitPoint?_eq_some_iff rank index point).mp success
  split at pointEq <;> omega

theorem splitAtConcrete?_eq_some_iff (shape lhs rhs : Tensor.Shape) (index : Int) :
    splitAtConcrete? shape index = some (lhs, rhs) ↔
      splitPoint? shape.length index = some lhs.length ∧ shape = lhs ++ rhs := by
  unfold splitAtConcrete?
  cases split : splitPoint? shape.length index with
  | none => simp
  | some point =>
    constructor
    · intro result
      have parts : (shape.take point, shape.drop point) = (lhs, rhs) := by
        simpa only [Option.map_some, Option.some.injEq, List.splitAt_eq] using result
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj parts
      simp [List.length_take_of_le (splitPoint?_le_rank split)]
    · rintro ⟨pointEq, rfl⟩
      simp only [Option.some.injEq] at pointEq
      simp [pointEq]

theorem splitAt?_ofStatic_eq_some_iff (shape lhs rhs : Tensor.Shape) (index : Int) :
    splitAt? (.ofStatic shape) index = some (.ofStatic lhs, .ofStatic rhs) ↔
      splitPoint? shape.length index = some lhs.length ∧ shape = lhs ++ rhs := by
  rw [← splitAtConcrete?_eq_some_iff, splitAt?, ShapeValue.toStatic?_ofStatic, Option.bind_some]
  rcases splitAtConcrete? shape index with _ | ⟨head, tail⟩ <;>
    simp [ShapeValue.ofStatic, List.map_inj_right (fun _ _ => Option.some.inj)]

theorem splitAt?_ofStatic_eq_none_iff (shape : Tensor.Shape) (index : Int) :
    splitAt? (.ofStatic shape) index = none ↔ index < -(shape.length : Int) ∨ (shape.length : Int) < index := by
  rw [← splitPoint?_eq_none_iff, splitAt?, ShapeValue.toStatic?_ofStatic, Option.bind_some, splitAtConcrete?]
  cases splitPoint? shape.length index <;> simp

theorem splitAtExtentTensor_eq_defined_iff (shape lhs rhs : ExtentTensor) (index : Int) :
    splitAtExtentTensor shape index = .defined (lhs, rhs) ↔
      splitPoint? shape.toShape.length index = some lhs.toShape.length ∧
        shape.toShape = lhs.toShape ++ rhs.toShape := by
  have encode (extents : ExtentTensor) {concrete : Tensor.Shape} :
      extentTensor concrete = extents ↔ concrete = extents.toShape :=
    ⟨fun eq => by rw [← eq, ExtentTensor.toShape_extentTensor],
      fun eq => eq ▸ ExtentTensor.extentTensor_toShape extents⟩
  rw [← splitAtConcrete?_eq_some_iff, splitAtExtentTensor]
  rcases splitAtConcrete? shape.toShape index with _ | ⟨head, tail⟩ <;> simp [encode]

theorem splitAtExtentTensor_eq_undefined_iff (shape : ExtentTensor) (index : Int) :
    splitAtExtentTensor shape index = .undefined ↔ index < -(shape.1 : Int) ∨ (shape.1 : Int) < index := by
  have length : shape.toShape.length = shape.1 := by simp [ExtentTensor.toShape]
  rw [← length, ← splitPoint?_eq_none_iff, splitAtExtentTensor, splitAtConcrete?]
  cases splitPoint? shape.toShape.length index <;> simp

end Silmaril.Proofs.MLIR.Shape
