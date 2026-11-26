module

public import Silmaril.SSA.MLIR.Shape.Variadic.Defs
import Silmaril.Proofs.SSA.MLIR.Shape.Variadic

/-! # Variadic broadcast contracts -/

public section

namespace Silmaril.MLIR.Shape

/-- Success determines the largest rank and exactly the non-unit extents at each aligned axis. -/
theorem broadcastManyConcrete?_eq_some_iff (shapes : List Tensor.Shape) (result : Tensor.Shape) :
    broadcastManyConcrete? shapes = some result ↔ shapes ≠ [] ∧ BroadcastsManyTo shapes result :=
  Proofs.MLIR.Shape.broadcastManyConcrete?_eq_some_iff shapes result

theorem broadcastManyConcrete?_axis_iff {shapes : List Tensor.Shape} {result : Tensor.Shape}
    (success : broadcastManyConcrete? shapes = some result) {axis value : Nat} (nonunit : value ≠ 1) :
    trailingExtent result axis = value ↔ ∃ shape ∈ shapes, trailingExtent shape axis = value :=
  (((broadcastManyConcrete?_eq_some_iff _ _).mp success).2.2 axis value nonunit).symm

/-- The common-compatibility criterion is equivalent to the existence of a common result shape. -/
theorem compatible_iff_exists_broadcastsManyTo (shapes : List Tensor.Shape) :
    BroadcastManyCompatible shapes ↔ ∃ result : Tensor.Shape, BroadcastsManyTo shapes result :=
  Proofs.MLIR.Shape.compatible_iff_exists_broadcastsManyTo shapes

theorem not_broadcastManyCompatible_iff (shapes : List Tensor.Shape) :
    ¬ BroadcastManyCompatible shapes ↔
      ∃ (axis : Nat) (lhs rhs : Tensor.Shape), lhs ∈ shapes ∧ rhs ∈ shapes ∧
        trailingExtent lhs axis ≠ 1 ∧ trailingExtent rhs axis ≠ 1 ∧
        trailingExtent lhs axis ≠ trailingExtent rhs axis := by
  simp only [BroadcastManyCompatible, Classical.not_forall, exists_prop]

theorem broadcastManyConcrete?_isSome_iff (shapes : List Tensor.Shape) :
    (broadcastManyConcrete? shapes).isSome = true ↔ shapes ≠ [] ∧ BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.broadcastManyConcrete?_isSome_iff shapes

/-- An empty operand list or incompatible extents prevent a concrete result. -/
theorem broadcastManyConcrete?_eq_none_iff (shapes : List Tensor.Shape) :
    broadcastManyConcrete? shapes = none ↔ shapes = [] ∨ ¬ BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.broadcastManyConcrete?_eq_none_iff shapes

/-- Reordering concrete operands preserves both success with its exact result and failure. -/
theorem broadcastManyConcrete?_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    broadcastManyConcrete? lhs = broadcastManyConcrete? rhs :=
  Proofs.MLIR.Shape.broadcastManyConcrete?_perm perm

theorem broadcastMany?_ofStatic_eq_some_iff (shapes : List Tensor.Shape) (result : Tensor.Shape) :
    broadcastMany? (shapes.map ShapeValue.ofStatic) = some (.ofStatic result) ↔
      shapes ≠ [] ∧ BroadcastsManyTo shapes result :=
  Proofs.MLIR.Shape.broadcastMany?_ofStatic_eq_some_iff shapes result

theorem broadcastMany?_ofStatic_eq_invalid_iff (shapes : List Tensor.Shape) :
    broadcastMany? (shapes.map ShapeValue.ofStatic) = some .invalid ↔
      shapes ≠ [] ∧ ¬ BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.broadcastMany?_ofStatic_eq_invalid_iff shapes

/-- An invalid operand produces an invalid shape. -/
theorem broadcastMany?_invalid {inputs : List ShapeValue} (invalid : ShapeValue.invalid ∈ inputs) :
    broadcastMany? inputs = some .invalid :=
  Proofs.MLIR.Shape.broadcastMany?_invalid invalid

theorem broadcastMany?_ofStatic_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    broadcastMany? (lhs.map ShapeValue.ofStatic) = broadcastMany? (rhs.map ShapeValue.ofStatic) :=
  Proofs.MLIR.Shape.broadcastMany?_ofStatic_perm perm

theorem broadcastManyExtentTensor?_eq_defined_iff (inputs : List ExtentTensor) (result : ExtentTensor) :
    broadcastManyExtentTensor? inputs = some (.defined result) ↔
      inputs ≠ [] ∧ BroadcastsManyTo (inputs.map ExtentTensor.toShape) result.toShape :=
  Proofs.MLIR.Shape.broadcastManyExtentTensor?_eq_defined_iff inputs result

theorem broadcastManyExtentTensor?_eq_undefined_iff (inputs : List ExtentTensor) :
    broadcastManyExtentTensor? inputs = some .undefined ↔
      inputs ≠ [] ∧ ¬ BroadcastManyCompatible (inputs.map ExtentTensor.toShape) :=
  Proofs.MLIR.Shape.broadcastManyExtentTensor?_eq_undefined_iff inputs

theorem broadcastManyExtentTensor?_perm {lhs rhs : List ExtentTensor} (perm : lhs.Perm rhs) :
    broadcastManyExtentTensor? lhs = broadcastManyExtentTensor? rhs :=
  Proofs.MLIR.Shape.broadcastManyExtentTensor?_perm perm

theorem isBroadcastableMany?_ofStatic_eq_true_iff (shapes : List Tensor.Shape) :
    isBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some true ↔
      BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.isBroadcastableMany?_ofStatic_eq_true_iff shapes

theorem isBroadcastableMany?_ofStatic_eq_false_iff (shapes : List Tensor.Shape) :
    isBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some false ↔
      ¬ BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.isBroadcastableMany?_ofStatic_eq_false_iff shapes

theorem isBroadcastableMany?_ofStatic_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    isBroadcastableMany? (lhs.map ShapeValue.ofStatic) = isBroadcastableMany? (rhs.map ShapeValue.ofStatic) :=
  Proofs.MLIR.Shape.isBroadcastableMany?_ofStatic_perm perm

/-- A passing witness requires at least two concrete operands with common compatibility. -/
theorem cstrBroadcastableMany?_passing_iff (shapes : List Tensor.Shape) :
    cstrBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some .passing ↔
      2 ≤ shapes.length ∧ BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.cstrBroadcastableMany?_passing_iff shapes

/-- An admitted constraint is unsatisfied exactly when its concrete inputs are incompatible. -/
theorem cstrBroadcastableMany?_unsatisfied_iff (shapes : List Tensor.Shape) :
    cstrBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some .unsatisfied ↔
      2 ≤ shapes.length ∧ ¬ BroadcastManyCompatible shapes :=
  Proofs.MLIR.Shape.cstrBroadcastableMany?_unsatisfied_iff shapes

theorem cstrBroadcastableMany?_ofStatic_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    cstrBroadcastableMany? (lhs.map ShapeValue.ofStatic) =
      cstrBroadcastableMany? (rhs.map ShapeValue.ofStatic) := by
  simp only [cstrBroadcastableMany?, List.length_map, perm.length_eq,
    isBroadcastableMany?_ofStatic_perm perm]

theorem broadcastManyConcrete?_pair (lhs rhs : Tensor.Shape) :
    broadcastManyConcrete? [lhs, rhs] = broadcastConcrete? lhs rhs :=
  Proofs.MLIR.Shape.broadcastManyConcrete?_pair lhs rhs

theorem broadcastMany?_pair (lhs rhs : ShapeValue) :
    broadcastMany? [lhs, rhs] = broadcast? lhs rhs :=
  Proofs.MLIR.Shape.broadcastMany?_pair lhs rhs

theorem broadcastManyExtentTensor?_pair (lhs rhs : ExtentTensor) :
    broadcastManyExtentTensor? [lhs, rhs] = some (broadcastExtentTensor lhs rhs) :=
  Proofs.MLIR.Shape.broadcastManyExtentTensor?_pair lhs rhs

theorem isBroadcastableMany?_pair (lhs rhs : ShapeValue) :
    isBroadcastableMany? [lhs, rhs] = isBroadcastable? lhs rhs :=
  Proofs.MLIR.Shape.isBroadcastableMany?_pair lhs rhs

end Silmaril.MLIR.Shape
