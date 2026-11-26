module

public import Silmaril.SSA.MLIR.Shape.Thms
public import Silmaril.SSA.MLIR.Shape.Extents.Thms
public import Silmaril.SSA.MLIR.Shape.Variadic.Thms

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

theorem broadcast_aligns_trailing_extents :
    broadcast? (.ofStatic [2, 1, 0]) (.ofStatic [0, 1]) = some (.ofStatic [2, 0, 0]) := rfl

theorem broadcast_rank_zero_pair : broadcast? (.ofStatic []) (.ofStatic []) =
    some (.ofStatic []) := rfl

theorem broadcast_rank_zero_with_zero_extent :
    broadcast? (.ofStatic []) (.ofStatic [3, 0]) = some (.ofStatic [3, 0]) := rfl

theorem broadcast_zero_and_two_are_incompatible :
    broadcast? (.ofStatic [3, 0]) (.ofStatic [2]) = some .invalid := rfl

theorem broadcastExtentTensor_trailing_extents :
    broadcastExtentTensor (extentTensor [2, 2]) (extentTensor [3, 1, 2]) =
      .defined (extentTensor [3, 2, 2]) := rfl

theorem broadcastExtentTensor_incompatible_is_undefined :
    broadcastExtentTensor (extentTensor [3, 0]) (extentTensor [2]) = .undefined := rfl

theorem isBroadcastable_concrete :
    isBroadcastable? (.ofStatic [2, 2]) (.ofStatic [3, 1, 2]) = some true ∧
    isBroadcastable? (.ofStatic [2, 2]) (.ofStatic [3, 2]) = some false := ⟨rfl, rfl⟩

theorem broadcast_partial_outside_profile :
    broadcast? (.ranked [none]) (.ofStatic [1]) = none := rfl

theorem isBroadcastable_invalid_outside_profile :
    isBroadcastable? .invalid (.ofStatic [1]) = none := rfl

theorem broadcastMany_no_operands :
    broadcastMany? [] = none ∧ broadcastManyExtentTensor? [] = none := ⟨rfl, rfl⟩

theorem broadcastMany_rank_zero_operand :
    broadcastMany? [.ofStatic []] = some (.ofStatic []) := rfl

theorem broadcastMany_singleton_extent_tensor :
    broadcastManyExtentTensor? [extentTensor [7, 0]] = some (.defined (extentTensor [7, 0])) := rfl

theorem isBroadcastableMany_fewer_than_two :
    isBroadcastableMany? [] = some true ∧
      isBroadcastableMany? [.ofStatic [7, 0]] = some true := ⟨rfl, rfl⟩

theorem broadcastMany_late_conflict :
    broadcastMany? ([[3, 1], [0]].map ShapeValue.ofStatic) = some (.ofStatic [3, 0]) ∧
      broadcastMany? ([[3, 1], [0], [1, 2]].map ShapeValue.ofStatic) = some .invalid ∧
      isBroadcastableMany? ([[3, 1], [0], [1, 2]].map ShapeValue.ofStatic) = some false :=
  ⟨rfl, rfl, rfl⟩

theorem broadcastMany_aligns_mixed_ranks :
    broadcastManyExtentTensor? ([[], [4], [0, 1], [5, 1, 4]].map extentTensor) =
      some (.defined (extentTensor [5, 0, 4])) := rfl

theorem broadcastManyExtentTensor_late_conflict :
    broadcastManyExtentTensor? ([[3, 1], [0], [1, 2]].map extentTensor) = some .undefined := rfl

theorem broadcastMany_projects_to_binary :
    broadcastMany? [.ofStatic [3, 1], .ofStatic [0]] = broadcast? (.ofStatic [3, 1]) (.ofStatic [0]) ∧
      broadcastManyExtentTensor? [extentTensor [0], extentTensor [2]] =
        some (broadcastExtentTensor (extentTensor [0]) (extentTensor [2])) ∧
      isBroadcastableMany? [.ofStatic [0], .ofStatic [2]] =
        isBroadcastable? (.ofStatic [0]) (.ofStatic [2]) :=
  ⟨broadcastMany?_pair _ _, broadcastManyExtentTensor?_pair _ _, isBroadcastableMany?_pair _ _⟩

theorem broadcastMany_invalid_dominates_unknown :
    broadcastMany? [.ofStatic [0], .unranked, .invalid] = some .invalid := rfl

theorem broadcastMany_unknown_outside_profile :
    broadcastMany? [.ofStatic [0], .ranked [none], .ofStatic [2]] = none := rfl

theorem isBroadcastableMany_invalid_outside_profile :
    isBroadcastableMany? [.ofStatic [0], .invalid, .ofStatic [2]] = none := rfl

theorem cstrBroadcastableMany_witnesses :
    cstrBroadcastableMany? ([[2, 2], [3, 1, 2], []].map ShapeValue.ofStatic) = some .passing ∧
      cstrBroadcastableMany? ([[3, 1], [0], [1, 2]].map ShapeValue.ofStatic) = some .unsatisfied :=
  ⟨rfl, rfl⟩

theorem cstrBroadcastableMany_requires_two_operands :
    cstrBroadcastableMany? [] = none ∧ cstrBroadcastableMany? [.ofStatic []] = none := ⟨rfl, rfl⟩

theorem cstrBroadcastableMany_unknown_outside_profile :
    cstrBroadcastableMany? [.ofStatic [0], .ranked [none]] = none := rfl

theorem concat_rank_zero : concat? (.ofStatic []) (.ofStatic [0, 5]) = some (.ofStatic [0, 5]) :=
  rfl

theorem concatExtentTensor_keeps_extent_order :
    (concatExtentTensor (extentTensor [3, 0]) (extentTensor [1, 5])).toShape = [3, 0, 1, 5] := rfl

theorem concat_invalid_propagates : concat? (.ranked [none]) .invalid = some .invalid := rfl

theorem concat_unknown_outside_fragment : concat? (.ranked [none]) (.ofStatic [4]) = none := rfl

theorem dim_zero_extent :
    dimSize (Tensor.splat (shape := [4, 0]) ()) 1 = .known 0 ∧
      dimIndex (Tensor.splat (shape := [4, 0]) ()) 1 = .defined 0 := ⟨rfl, rfl⟩

theorem dim_at_concat_boundary :
    dimSize (Tensor.splat (shape := [4, 0] ++ [6]) ()) 1 = .known 0 ∧
      dimSize (Tensor.splat (shape := [4, 0] ++ [6]) ()) 2 = .known 6 := ⟨rfl, rfl⟩

theorem dim_signed_index_bounds :
    dimSize (Tensor.splat (shape := [4, 0]) ()) (-1) = .invalid ∧
      dimIndex (Tensor.splat (shape := [4, 0]) ()) 2 = .undefined := ⟨rfl, rfl⟩

theorem dim_rank_zero : dimSize (Tensor.splat (shape := []) ()) 0 = .invalid := rfl

theorem splitAt_rank_zero :
    splitAt? (.ofStatic []) 0 = some (.ofStatic [], .ofStatic []) ∧
      splitAtExtentTensor (extentTensor []) 1 = .undefined := ⟨rfl, rfl⟩

theorem splitAt_endpoints :
    splitAt? (.ofStatic [4, 0, 6]) 0 = some (.ofStatic [], .ofStatic [4, 0, 6]) ∧
      splitAt? (.ofStatic [4, 0, 6]) (-3) = some (.ofStatic [], .ofStatic [4, 0, 6]) ∧
      splitAt? (.ofStatic [4, 0, 6]) 3 = some (.ofStatic [4, 0, 6], .ofStatic []) :=
  ⟨rfl, rfl, rfl⟩

theorem splitAt_negative_position :
    splitAt? (.ofStatic [4, 0, 6]) (-2) = some (.ofStatic [4], .ofStatic [0, 6]) := rfl

theorem splitAt_extent_tensor_negative_position :
    splitAtExtentTensor (extentTensor [4, 0, 6]) (-1) =
      .defined (extentTensor [4, 0], extentTensor [6]) := rfl

theorem splitAt_shape_error_outside_fragment :
    splitAt? (.ofStatic [4, 0, 6]) (-4) = none ∧ splitAt? (.ofStatic [4, 0, 6]) 4 = none :=
  ⟨rfl, rfl⟩

theorem splitAt_extent_tensor_out_of_range :
    splitAtExtentTensor (extentTensor [4, 0, 6]) (-4) = .undefined ∧
      splitAtExtentTensor (extentTensor [4, 0, 6]) 4 = .undefined := ⟨rfl, rfl⟩

theorem splitAtExtentTensor_round_trip :
    splitAtExtentTensor (concatExtentTensor (extentTensor [4]) (extentTensor [0, 6])) 1 =
      .defined (extentTensor [4], extentTensor [0, 6]) :=
  splitAtExtentTensor_concatExtentTensor _ _

theorem splitAt_invalid_outside_fragment : splitAt? .invalid 0 = none := rfl

end Silmaril.MLIR.Shape.Examples
