module

public import Silmaril.SSA.MLIR.Shape.Defs

public section

namespace Silmaril.MLIR.Shape

universe u

theorem StaticShape.ofTensorShape_admits (shape : Tensor.Shape) :
    (ofTensorShape shape).Admits shape := by
  simp [ofTensorShape, Admits]

private theorem concreteExtents_iff (extents : List (Option Nat)) (shape : Tensor.Shape) :
    extents.mapM id = some shape ↔ extents = shape.map some := by
  induction extents generalizing shape with
  | nil => cases shape <;> simp
  | cons extent _ ih =>
    cases extent <;> cases shape <;> simp [Option.bind_eq_some_iff, ih] <;> exact and_comm

theorem ShapeValue.toStatic?_eq_some_iff (value : ShapeValue) (shape : Tensor.Shape) :
    value.toStatic? = some shape ↔ value = ofStatic shape := by
  cases value <;> simp [ofStatic, toStatic?, concreteExtents_iff]

theorem ShapeValue.toStatic?_ofStatic (shape : Tensor.Shape) :
    (ofStatic shape).toStatic? = some shape :=
  (toStatic?_eq_some_iff _ _).2 rfl

theorem shapeOf_toStatic? {shape : Tensor.Shape} {α : Type u} (tensor : Tensor.Tensor shape α) :
    (shapeOf tensor).toStatic? = some shape :=
  ShapeValue.toStatic?_ofStatic shape

theorem rank_ofStatic (shape : Tensor.Shape) :
    rank (.ofStatic shape) = .known shape.length := by
  simp [rank, ShapeValue.ofStatic]

theorem getExtent?_ofStatic (shape : Tensor.Shape) (dim : Nat) :
    getExtent? (.ofStatic shape) dim = shape[dim]?.map Size.known := by
  simp [getExtent?, ShapeValue.ofStatic, Option.map_map, Function.comp_def]

theorem numElements?_ofStatic (shape : Tensor.Shape) :
    numElements? (.ofStatic shape) = some (.known shape.prod) := by
  change ((ShapeValue.ofStatic shape).toStatic?.map _) = _
  simp only [ShapeValue.toStatic?_ofStatic, Option.map_some]

theorem extentTensor_coordinate (shape : Tensor.Shape) (dim : Fin shape.length) :
    (extentTensor shape).2 (dim, ()) = shape.get dim := rfl

theorem toExtentTensor?_ofStatic (shape : Tensor.Shape) :
    toExtentTensor? (.ofStatic shape) = some (.defined (extentTensor shape)) := by
  change ((ShapeValue.ofStatic shape).toStatic?.map _) = _
  simp only [ShapeValue.toStatic?_ofStatic, Option.map_some]

end Silmaril.MLIR.Shape
