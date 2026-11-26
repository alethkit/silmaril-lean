module

public import Silmaril.SSA.MLIR.Shape.Reduce.SCF.Defs
import Silmaril.SSA.MLIR.SCF.For.Thms
import Silmaril.Proofs.SSA.MLIR.Shape.Reduce.SCF

public section

namespace Silmaril.MLIR.Shape.ReduceBody

open Arith (Width Env)
open _root_.Silmaril.MLIR.Pure (Eval OpSignature)
open _root_.Silmaril.MLIR.SCF (For Yield)

variable {Op : OpSignature} {indexWidth : Width} {Carried Captures : List Width}

/-- The optional lookup succeeds exactly below the concrete rank. -/
theorem extentTable_lookup (shape : ExtentTensor) (indexWidth : Width) (axis : Nat) :
    (extentTable indexWidth shape)[axis]? = if h : axis < shape.1 then
      some (BitVec.ofNat indexWidth.val (shape.2 (⟨axis, h⟩, ()))) else none :=
  Proofs.MLIR.Shape.Reduce.SCF.extentTable_lookup shape indexWidth axis

theorem extentTable_lookup_of_axis {shape : ExtentTensor} (fits : shape.ReduceFits indexWidth)
    (axis : Fin shape.1) :
    (extentTable indexWidth shape)[(BitVec.ofNat indexWidth.val axis.val).toNat]? =
      some (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))) :=
  Proofs.MLIR.Shape.Reduce.SCF.extentTable_lookup_of_axis fits axis

/-- Each executed SCF body reads the matching extent before evaluating the original typed body. -/
theorem lowerToFor_body_eval (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial carried : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) (axis : Fin shape.1) :
    (body.lowerToFor shape supported).body.eval (forEval evalOp) Yield.eval
        (.cons (BitVec.ofNat indexWidth.val axis.val) (carried.append (lowerInput shape initial captures))) =
      body.step evalOp (BitVec.ofNat indexWidth.val axis.val)
        (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))) carried captures :=
  Proofs.MLIR.Shape.Reduce.SCF.lowerToFor_body_eval body evalOp shape initial carried captures supported fits axis

theorem lowerToFor_tripCount (body : ReduceBody Op indexWidth Carried Captures)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).tripCount (lowerInput shape initial captures) = shape.1 :=
  Proofs.MLIR.Shape.Reduce.SCF.lowerToFor_tripCount body shape initial captures supported fits

/-- The admitted Shape inputs satisfy the checked unsigned SCF arithmetic guard. -/
theorem lowerToFor_admitted (body : ReduceBody Op indexWidth Carried Captures)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).Admitted (lowerInput shape initial captures) :=
  Proofs.MLIR.Shape.Reduce.SCF.lowerToFor_admitted body shape initial captures supported fits

/-- The emitted SCF program agrees with the checked Shape runner on their common domain. -/
theorem lowerToFor_run (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).run (forEval evalOp) (lowerInput shape initial captures) =
      body.run? evalOp shape initial captures :=
  Proofs.MLIR.Shape.Reduce.SCF.lowerToFor_run body evalOp shape initial captures supported fits

/-- The guarded lowering retains source admission at all target-supported widths. -/
theorem runLowered?_eq (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) :
    body.runLowered? evalOp shape initial captures =
      if indexWidth.val ≤ 2 ^ 24 - 1 then body.run? evalOp shape initial captures else none :=
  Proofs.MLIR.Shape.Reduce.SCF.runLowered?_eq body evalOp shape initial captures

/-- Compose with the existing SCF-to-CF correctness theorem at its sufficient budget. -/
theorem lowerToFor_cfg_run (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).lower.run (For.lowerEval (forEval evalOp))
        (2 * shape.1 + 3) (lowerInput shape initial captures) = body.run? evalOp shape initial captures := by
  rw [← lowerToFor_tripCount body shape initial captures supported fits,
    For.lower_run_at _ _ _ (lowerToFor_admitted body shape initial captures supported fits)]
  exact lowerToFor_run body evalOp shape initial captures supported fits

end Silmaril.MLIR.Shape.ReduceBody
