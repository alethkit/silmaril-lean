module

public import Silmaril.SSA.MLIR.Shape.Defs
import Silmaril.Proofs.SSA.MLIR.Shape.Broadcast

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

theorem ExtentTensor.toShape_extentTensor (shape : Tensor.Shape) :
    (extentTensor shape).toShape = shape := List.ofFn_getElem

private theorem extentTensor_eq_of_coordinates {lhs rhs : ExtentTensor}
    (sameRank : lhs.1 = rhs.1)
    (sameExtents : ∀ dim : Fin lhs.1, lhs.2 (dim, ()) = rhs.2 (Fin.cast sameRank dim, ())) :
    lhs = rhs := by
  rcases lhs with ⟨rank, lhs⟩
  rcases rhs with ⟨_, rhs⟩
  cases sameRank
  exact congrArg (Sigma.mk rank) (funext fun ⟨dim, ()⟩ => sameExtents dim)

theorem ExtentTensor.extentTensor_toShape (extents : ExtentTensor) :
    extentTensor extents.toShape = extents := by
  apply extentTensor_eq_of_coordinates List.length_ofFn
  intro dim
  exact List.getElem_ofFn dim.isLt

theorem fromExtentTensor_extentTensor (shape : Tensor.Shape) :
    fromExtentTensor (extentTensor shape) = .ofStatic shape :=
  congrArg ShapeValue.ofStatic (ExtentTensor.toShape_extentTensor shape)

theorem rank_fromExtentTensor (extents : ExtentTensor) :
    rank (fromExtentTensor extents) = .known extents.1 := by
  simp [fromExtentTensor, rank_ofStatic, ExtentTensor.toShape]

theorem getExtent?_fromExtentTensor (extents : ExtentTensor) (dim : Fin extents.1) :
    getExtent? (fromExtentTensor extents) dim.val = some (.known (extents.2 (dim, ()))) := by
  simp [fromExtentTensor, getExtent?_ofStatic, ExtentTensor.toShape, dim.isLt]

theorem fromExtents?_ofStatic (shape : Tensor.Shape) :
    fromExtents? (shape.map Int.ofNat) = some (.ofStatic shape) := by
  rw [fromExtents?, List.mapM_map]
  change (shape.mapM (m := Option) (pure <| id ·)).map _ = _
  rw [List.mapM_pure, List.map_id, Option.pure_apply, Option.map_some]

theorem fromExtents?_negative (before after : List Int) (magnitude : Nat) :
    fromExtents? (before ++ Int.negSucc magnitude :: after) = none := by
  simp [fromExtents?, Int.toNat?]

theorem toExtentTensor?_ofStatic (shape : Tensor.Shape) :
    toExtentTensor? (.ofStatic shape) = some (.defined (extentTensor shape)) := by
  change ((ShapeValue.ofStatic shape).toStatic?.map _) = _
  simp only [ShapeValue.toStatic?_ofStatic, Option.map_some]

theorem toExtentTensor?_fromExtentTensor (extents : ExtentTensor) :
    toExtentTensor? (fromExtentTensor extents) = some (.defined extents) := by
  rw [fromExtentTensor, toExtentTensor?_ofStatic, ExtentTensor.extentTensor_toShape]

/-- The binary broadcast returns exactly the shape specified by trailing alignment. -/
theorem broadcastConcrete?_eq_some_iff (lhs rhs result : Tensor.Shape) :
    broadcastConcrete? lhs rhs = some result ↔ BroadcastsTo lhs rhs result :=
  Proofs.MLIR.Shape.broadcastConcrete?_eq_some_iff lhs rhs result

/-- A concrete broadcast fails exactly when an aligned pair disagrees and neither extent is one. -/
theorem broadcastConcrete?_eq_none_iff (lhs rhs : Tensor.Shape) :
    broadcastConcrete? lhs rhs = none ↔
      ∃ dim : Fin (max lhs.length rhs.length),
        let rank := max lhs.length rhs.length
        let a := (lhs.leftpad rank 1)[dim.val]?.getD 1
        let b := (rhs.leftpad rank 1)[dim.val]?.getD 1
        a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 :=
  Proofs.MLIR.Shape.broadcastConcrete?_eq_none_iff lhs rhs

theorem broadcast?_ofStatic (lhs rhs : Tensor.Shape) :
    broadcast? (.ofStatic lhs) (.ofStatic rhs) =
      some (((broadcastConcrete? lhs rhs).map ShapeValue.ofStatic).getD .invalid) := by
  change (do
    let a ← (ShapeValue.ofStatic lhs).toStatic?
    let b ← (ShapeValue.ofStatic rhs).toStatic?
    return ((broadcastConcrete? a b).map ShapeValue.ofStatic).getD .invalid) = _
  simp [ShapeValue.toStatic?_ofStatic]

theorem broadcast?_ofStatic_eq_some_iff (lhs rhs result : Tensor.Shape) :
    broadcast? (.ofStatic lhs) (.ofStatic rhs) = some (.ofStatic result) ↔
      BroadcastsTo lhs rhs result := by
  rw [broadcast?_ofStatic, ← broadcastConcrete?_eq_some_iff]
  cases broadcastConcrete? lhs rhs <;> simp [ShapeValue.ofStatic, List.map_inj_right (fun _ _ => Option.some.inj)]

theorem broadcast?_invalid_left (rhs : ShapeValue) : broadcast? .invalid rhs = some .invalid :=
  rfl

theorem broadcast?_invalid_right (lhs : ShapeValue) : broadcast? lhs .invalid = some .invalid := by
  cases lhs <;> rfl

theorem isBroadcastable?_ofStatic (lhs rhs : Tensor.Shape) :
    isBroadcastable? (.ofStatic lhs) (.ofStatic rhs) = some (broadcastConcrete? lhs rhs).isSome := by
  simp [isBroadcastable?, ShapeValue.toStatic?_ofStatic]

theorem isBroadcastable?_ofStatic_eq_true_iff (lhs rhs : Tensor.Shape) :
    isBroadcastable? (.ofStatic lhs) (.ofStatic rhs) = some true ↔
      ∃ result : Tensor.Shape, broadcast? (.ofStatic lhs) (.ofStatic rhs) = some (.ofStatic result) := by
  rw [isBroadcastable?_ofStatic, Option.some.injEq]
  simpa only [broadcast?_ofStatic_eq_some_iff, ← broadcastConcrete?_eq_some_iff] using
    (Option.isSome_iff_exists (x := broadcastConcrete? lhs rhs))

theorem isBroadcastable?_ofStatic_eq_false_iff (lhs rhs : Tensor.Shape) :
    isBroadcastable? (.ofStatic lhs) (.ofStatic rhs) = some false ↔
      broadcast? (.ofStatic lhs) (.ofStatic rhs) = some .invalid := by
  rw [isBroadcastable?_ofStatic, broadcast?_ofStatic]
  cases broadcastConcrete? lhs rhs <;> simp [ShapeValue.ofStatic]

theorem broadcastExtentTensor_eq_defined_iff (lhs rhs result : ExtentTensor) :
    broadcastExtentTensor lhs rhs = .defined result ↔
      BroadcastsTo lhs.toShape rhs.toShape result.toShape := by
  have encode {shape : Tensor.Shape} : extentTensor shape = result ↔ shape = result.toShape :=
    ⟨fun h => by rw [← h, ExtentTensor.toShape_extentTensor],
      fun h => h ▸ ExtentTensor.extentTensor_toShape result⟩
  rw [← broadcastConcrete?_eq_some_iff, broadcastExtentTensor]
  cases broadcastConcrete? lhs.toShape rhs.toShape <;> simp [encode]

theorem isBroadcastable?_fromExtentTensor_eq_true_iff (lhs rhs : ExtentTensor) :
    isBroadcastable? (fromExtentTensor lhs) (fromExtentTensor rhs) = some true ↔
      ∃ result : ExtentTensor, broadcastExtentTensor lhs rhs = .defined result := by
  rw [fromExtentTensor, fromExtentTensor, isBroadcastable?_ofStatic_eq_true_iff]
  simp only [broadcast?_ofStatic_eq_some_iff, broadcastExtentTensor_eq_defined_iff]
  exact ⟨fun ⟨shape, h⟩ => ⟨extentTensor shape, by simpa only [ExtentTensor.toShape_extentTensor]⟩,
    fun ⟨result, h⟩ => ⟨result.toShape, h⟩⟩

theorem isBroadcastable?_fromExtentTensor_eq_false_iff (lhs rhs : ExtentTensor) :
    isBroadcastable? (fromExtentTensor lhs) (fromExtentTensor rhs) = some false ↔
      broadcastExtentTensor lhs rhs = .undefined := by
  rw [fromExtentTensor, fromExtentTensor, isBroadcastable?_ofStatic, broadcastExtentTensor]
  cases broadcastConcrete? lhs.toShape rhs.toShape <;> simp

end Silmaril.MLIR.Shape
