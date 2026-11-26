module

public import Silmaril.SSA.MLIR.Shape.Defs

/-! # Concrete variadic Shape broadcasting

The broadcast operations admit a nonempty operand list. The predicate also
admits the empty list. The witness check requires at least two operands.
-/

@[expose] public section

namespace Silmaril.MLIR.Shape

/-- Read an axis from the right, counting from zero. Missing leading axes are one. -/
def trailingExtent (shape : Tensor.Shape) (axis : Nat) : Nat :=
  shape.reverse[axis]?.getD 1

/-- The greatest rank among the concrete operands. -/
def broadcastRank (shapes : List Tensor.Shape) : Nat :=
  shapes.foldr (fun shape rank => max shape.length rank) 0

/-- Every pair of non-unit extents at a common trailing axis must agree. -/
def BroadcastManyCompatible (shapes : List Tensor.Shape) : Prop :=
  ∀ (axis : Nat) (lhs rhs : Tensor.Shape), lhs ∈ shapes → rhs ∈ shapes →
    trailingExtent lhs axis ≠ 1 → trailingExtent rhs axis ≠ 1 →
      trailingExtent lhs axis = trailingExtent rhs axis

/-- A non-unit result extent occurs among the inputs, and all non-unit input
extents at this axis equal the result. In their absence the result is one. -/
def BroadcastAxis (shapes : List Tensor.Shape) (axis extent : Nat) : Prop :=
  ∀ value : Nat, value ≠ 1 →
    ((∃ shape ∈ shapes, trailingExtent shape axis = value) ↔ extent = value)

/-- The result has the greatest operand rank and agrees with each trailing axis. -/
def BroadcastsManyTo (shapes : List Tensor.Shape) (result : Tensor.Shape) : Prop :=
  result.length = broadcastRank shapes ∧
    ∀ axis : Nat, BroadcastAxis shapes axis (trailingExtent result axis)

/-- Broadcast a nonempty list of concrete shapes by combining operands from the
left. `none` represents either an empty operand list or incompatible extents. -/
def broadcastManyConcrete? : List Tensor.Shape → Option Tensor.Shape
  | [] => none
  | first :: rest => rest.foldlM broadcastConcrete? first

/-- `shape.broadcast` with a `!shape.shape` result. Empty operand lists and
unknown shapes without an invalid operand are outside the modeled fragment. -/
def broadcastMany? : List ShapeValue → Option ShapeValue
  | [] => none
  | first :: rest =>
    let inputs := first :: rest
    if .invalid ∈ inputs then some .invalid else
      (inputs.mapM ShapeValue.toStatic?).map fun shapes =>
        ((broadcastManyConcrete? shapes).map ShapeValue.ofStatic).getD .invalid

/-- `shape.broadcast` with a nonempty list of extent tensor operands and an
extent tensor result. Incompatibility leaves that result undefined. -/
def broadcastManyExtentTensor? : List ExtentTensor → Option (Evaluation ExtentTensor)
  | [] => none
  | first :: rest => some <|
    match broadcastManyConcrete? ((first :: rest).map ExtentTensor.toShape) with
    | some result => .defined (extentTensor result)
    | none => .undefined

/-- `shape.is_broadcastable` on concrete shape views. The empty input list
is vacuously compatible. Unknown and invalid shapes are outside this fragment. -/
def isBroadcastableMany? (inputs : List ShapeValue) : Option Bool :=
  (inputs.mapM ShapeValue.toStatic?).map fun shapes =>
    shapes.isEmpty || (broadcastManyConcrete? shapes).isSome

/-- The observation of a broadcast constraint. `passing` provides a passing
`!shape.witness`. `unsatisfied` records failure of the constraint. -/
inductive BroadcastWitnessResult where
  | passing
  | unsatisfied
  deriving DecidableEq, Repr

/-- Observe `shape.cstr_broadcastable` on at least two concrete shape views.
The result records satisfaction of the constraint. -/
def cstrBroadcastableMany? (inputs : List ShapeValue) : Option BroadcastWitnessResult :=
  if 2 ≤ inputs.length then
    (isBroadcastableMany? inputs).map fun compatible =>
      if compatible then .passing else .unsatisfied
  else none

end Silmaril.MLIR.Shape
