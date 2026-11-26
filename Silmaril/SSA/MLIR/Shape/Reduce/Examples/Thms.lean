module

import Silmaril.SSA.MLIR.Shape.Reduce.Thms

/-! Order-sensitive examples with a heterogeneous carry and a capture. -/

namespace Silmaril.MLIR.Shape.Reduce.Examples

open Arith (Width Env)
open _root_.Silmaril.MLIR.Pure (Eval OpSignature)

private def indexWidth : Width := ⟨16, by decide⟩
private def i8 : Width := ⟨8, by decide⟩

private inductive Op : OpSignature where
  | add (width : Width) : Op [width, width] width
  | sub (width : Width) : Op [width, width] width

private def evalOp : Eval Op
  | _, _, .add _, .cons lhs (.cons rhs .nil) => lhs + rhs
  | _, _, .sub _, .cons lhs (.cons rhs .nil) => lhs - rhs

/-- Yield `extent - (trace + axis)` and increment the count by the capture. -/
private def body : ReduceBody Op indexWidth [indexWidth, i8] [i8] :=
  .letOp (.add i8)
    (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) <|
  .letOp (.add indexWidth)
    (.cons (.there (.there (.there .here))) (.cons (.there .here) .nil)) <|
  .letOp (.sub indexWidth)
    (.cons (.there (.there (.there .here))) (.cons .here .nil)) <|
  .terminator (.cons .here (.cons (.there (.there .here)) .nil))

private def initial : Env [indexWidth, i8] := .cons 1 (.cons 7 .nil)
private def captures : Env [i8] := .cons 1 .nil

private def referenceStep (carried : Env [indexWidth, i8]) (axis extent : Nat) : Env [indexWidth, i8] :=
  match carried with
  | .cons trace (.cons count .nil) =>
    .cons (BitVec.ofNat indexWidth.val extent - (trace + BitVec.ofNat indexWidth.val axis))
      (.cons (count + 1) .nil)

example (shape : ExtentTensor) (fits : shape.ReduceFits indexWidth) :
    body.run? evalOp shape initial captures = some
      (shape.toShape.zipIdx.foldl (fun carried (extent, axis) => referenceStep carried axis extent) initial) := by
  refine (body.run?_eq_some_iff evalOp shape initial _ captures).mpr ⟨fits, ?_⟩
  apply body.denote_eq_foldl_of_step evalOp shape initial captures referenceStep
  intro carried axis extent
  cases carried with
  | cons trace rest =>
    cases rest with
    | cons count tail => cases tail; rfl

/-- Reversing the extents changes the first result. The zero extent still
invokes the body, as the second result records two visits. -/
example :
    body.run? evalOp (extentTensor [5, 0]) initial captures = some (.cons (-5) (.cons 9 .nil)) ∧
      body.run? evalOp (extentTensor [0, 5]) initial captures = some (.cons 5 (.cons 9 .nil)) :=
  ⟨rfl, rfl⟩

example : body.run? evalOp (extentTensor []) initial captures = some initial :=
  body.run?_of_rank_zero evalOp _ initial captures rfl

example : body.run? evalOp (extentTensor [32768]) initial captures = none := rfl

private def narrowIndex : Width := ⟨2, by decide⟩
private def emptyYield : ReduceBody Op narrowIndex [] [] := .terminator .nil

example : emptyYield.run? evalOp (extentTensor [0]) .nil .nil = some .nil := rfl

example : emptyYield.run? evalOp (extentTensor [0, 0]) .nil .nil = none := rfl

end Silmaril.MLIR.Shape.Reduce.Examples
