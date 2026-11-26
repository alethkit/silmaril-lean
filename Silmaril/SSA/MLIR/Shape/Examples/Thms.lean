module

public import Silmaril.SSA.MLIR.Shape.Thms

public section

namespace Silmaril.MLIR.Shape.Examples

theorem static_unknown_accepts_concrete :
    (StaticShape.ranked [none, some 2]).Admits [8, 2] := by
  refine ⟨rfl, ?_⟩
  intro dim size known
  rcases dim with _ | _ | dim <;> simp_all

theorem static_rank_mismatch : ¬ (StaticShape.ranked [none]).Admits [8, 2] := by
  simp [StaticShape.Admits]

theorem static_known_extent_mismatch : ¬ (StaticShape.ranked [none, some 2]).Admits [8, 3] := by
  intro admits
  cases admits.2 1 2 rfl

theorem rank_of_partial : rank (.ranked [none, some 2]) = .known 2 := rfl

theorem rank_of_unranked : rank .unranked = .unknown := rfl

theorem rank_of_invalid : rank .invalid = .invalid := rfl

theorem getExtent_unknown : getExtent? (.ranked [none, some 2]) 0 = some .unknown := rfl

theorem getExtent_invalid : getExtent? .invalid 0 = some .invalid := rfl

theorem getExtent_outside_profile : getExtent? (.ranked [some 2]) 1 = none := rfl

theorem unknown_cannot_reify : (ShapeValue.ranked [none, some 2]).toStatic? = none := rfl

theorem scalar_has_one_element : numElements? (.ofStatic []) = some (.known 1) := rfl

theorem zero_extent_has_no_elements : numElements? (.ofStatic [3, 0]) = some (.known 0) := rfl

theorem invalid_element_count : numElements? .invalid = some .invalid := rfl

theorem invalid_extent_tensor_is_undefined : toExtentTensor? .invalid = some .undefined := rfl

theorem partial_extent_tensor_outside_profile :
    toExtentTensor? (.ranked [none]) = none := rfl

theorem static_tensor_round_trip :
    (shapeOf (Tensor.splat (shape := [3, 0]) 42)).toStatic? = some [3, 0] :=
  shapeOf_toStatic? _

theorem unknown_size_cast_is_undefined : sizeToIndex .unknown = .undefined := rfl

theorem invalid_size_cast_is_undefined : sizeToIndex .invalid = .undefined := rfl

theorem negative_index_cast_is_undefined : indexToSize (-1) = .undefined := rfl

theorem zero_size_cast : sizeToIndex (.known 0) = .defined 0 := rfl

theorem fromExtents_rank_zero : fromExtents? [] = some (.ofStatic []) := rfl

theorem fromExtents_keeps_order_and_zero :
    (fromExtents? [5, 0, 2]).bind ShapeValue.toStatic? = some [5, 0, 2] := rfl

theorem fromExtents_negative_outside_profile : fromExtents? [5, -1, 2] = none := rfl

theorem fromExtentTensor_empty : fromExtentTensor (extentTensor []) = .ofStatic [] :=
  fromExtentTensor_extentTensor []

theorem fromExtentTensor_single_zero : fromExtentTensor (extentTensor [0]) = .ofStatic [0] :=
  fromExtentTensor_extentTensor [0]

theorem fromExtentTensor_reads_coordinates :
    let extents : ExtentTensor := ⟨2, fun dim => if dim.1.val = 0 then 5 else 3⟩
    (fromExtentTensor extents).toStatic? = some [5, 3] := rfl

end Silmaril.MLIR.Shape.Examples
