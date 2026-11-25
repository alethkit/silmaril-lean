module

public import Silmaril.SSA.MLIR.Triton.Defs
import Silmaril.Proofs.SSA.MLIR.Triton.Observation

public section

namespace Silmaril.MLIR.Gluon

theorem Layout.slotToIndex_indexToSlot (layout : Layout) (i : Fin 64) :
    layout.slotToIndex (layout.indexToSlot i) = i :=
  Proofs.MLIR.Gluon.slotToIndex_indexToSlot layout i

theorem Layout.indexToSlot_slotToIndex (layout : Layout) (slot : Slot) :
    layout.indexToSlot (layout.slotToIndex slot) = slot :=
  Proofs.MLIR.Gluon.indexToSlot_slotToIndex layout slot

/-- Each layout conversion preserves the entire logical Tensor value. -/
theorem Value.toTensor_convertLayout {src : Layout} (value : Value src) (dst : Layout) :
    (value.convertLayout dst).toTensor = value.toTensor :=
  Proofs.MLIR.Gluon.toTensor_convertLayout value dst

/-- Observing the Gluon result as a Tensor agrees with interpreting the erased
Triton expression on the logical observation of the argument. -/
theorem Expr.denote_toTensor_eq_erase {input layout : Layout} (expr : Expr input layout)
    (arg : Value input) : (expr.denote arg).toTensor = expr.erase.toTensor arg.toTensor :=
  Proofs.MLIR.Gluon.denote_toTensor_eq_erase expr arg

/-- Every in-bounds Tensor extraction is preserved by layout erasure. -/
theorem Expr.extract_denote_eq_erase {input layout : Layout} (expr : Expr input layout)
    (arg : Value input) (i : Tensor.Index [64]) :
    Tensor.extract (expr.denote arg).toTensor i =
      Tensor.extract (expr.erase.toTensor arg.toTensor) i :=
  congrArg (fun tile => Tensor.extract tile i) (expr.denote_toTensor_eq_erase arg)

end Silmaril.MLIR.Gluon
