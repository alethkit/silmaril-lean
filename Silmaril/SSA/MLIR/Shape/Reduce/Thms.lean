module

public import Silmaril.SSA.MLIR.Shape.Reduce.Defs
import Silmaril.Proofs.SSA.MLIR.Shape.Reduce

public section

namespace Silmaril.MLIR.Shape

open Arith (Width Env)
open _root_.Silmaril.MLIR.Pure (Eval OpSignature)

/-- Every admitted iteration receives exact signed encodings of its axis and extent. -/
theorem ExtentTensor.ReduceFits.step_indices_exact {shape : ExtentTensor} {indexWidth : Width}
    (fits : shape.ReduceFits indexWidth) (axis : Fin shape.1) :
    (BitVec.ofNat indexWidth.val axis.val).toInt = (axis.val : Int) ∧
      (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))).toInt = (shape.2 (axis, ()) : Int) :=
  Proofs.MLIR.Shape.Reduce.step_indices_exact fits axis

namespace ReduceBody

variable {Op : OpSignature} {indexWidth : Width} {Carried Captures : List Width}

/-- The tensor traversal visits exactly the ordered `(extent, axis)` pairs of
the corresponding concrete shape, with axes numbered from zero. -/
theorem denote_eq_foldl (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) :
    body.denote evalOp shape initial captures =
      shape.toShape.zipIdx.foldl (fun carried (extent, axis) =>
        body.step evalOp (BitVec.ofNat indexWidth.val axis) (BitVec.ofNat indexWidth.val extent)
          carried captures) initial :=
  Proofs.MLIR.Shape.Reduce.denote_eq_foldl body evalOp shape initial captures

/-- A pure reference step that agrees with the region on each invocation
computes the same result by folding the concrete extent list. -/
theorem denote_eq_foldl_of_step (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (reference : Env Carried → Nat → Nat → Env Carried)
    (agrees : ∀ carried axis extent,
      body.step evalOp (BitVec.ofNat indexWidth.val axis) (BitVec.ofNat indexWidth.val extent)
        carried captures = reference carried axis extent) :
    body.denote evalOp shape initial captures =
      shape.toShape.zipIdx.foldl (fun carried (extent, axis) => reference carried axis extent) initial := by
  simp only [denote_eq_foldl, agrees]

theorem run?_eq_some_iff (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial result : Env Carried) (captures : Env Captures) :
    body.run? evalOp shape initial captures = some result ↔
      shape.ReduceFits indexWidth ∧ body.denote evalOp shape initial captures = result := by
  by_cases fits : shape.ReduceFits indexWidth <;> simp [run?, fits]

theorem run?_eq_none_iff (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) :
    body.run? evalOp shape initial captures = none ↔ ¬ shape.ReduceFits indexWidth := by
  by_cases fits : shape.ReduceFits indexWidth <;> simp [run?, fits]

/-- A rank-zero shape leaves all carried values at their initial values. -/
theorem run?_of_rank_zero (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (rankZero : shape.1 = 0) : body.run? evalOp shape initial captures = some initial :=
  Proofs.MLIR.Shape.Reduce.run?_of_rank_zero body evalOp shape initial captures rankZero

end ReduceBody

end Silmaril.MLIR.Shape
