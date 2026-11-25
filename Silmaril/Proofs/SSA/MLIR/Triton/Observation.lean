module

public import Silmaril.SSA.MLIR.Triton.Defs

public section

namespace Silmaril.Proofs.MLIR.Gluon

open Silmaril.MLIR.Gluon

theorem slotToIndex_indexToSlot (layout : Layout) (i : Fin 64) :
    layout.slotToIndex (layout.indexToSlot i) = i := by
  cases layout <;> apply Fin.ext <;>
    simp only [Layout.slotToIndex, Layout.indexToSlot, Fin.val_mk] <;> omega

theorem indexToSlot_slotToIndex (layout : Layout) (slot : Slot) :
    layout.indexToSlot (layout.slotToIndex slot) = slot := by
  obtain ⟨lane, reg⟩ := slot
  cases layout <;> simp only [Layout.indexToSlot, Layout.slotToIndex, Fin.val_mk] <;>
    congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

theorem toTensor_convertLayout {src : Layout} (value : Value src) (dst : Layout) :
    (value.convertLayout dst).toTensor = value.toTensor := by
  funext i
  change value.atSlot (src.indexToSlot (dst.slotToIndex (dst.indexToSlot i.1))) =
    value.atSlot (src.indexToSlot i.1)
  rw [slotToIndex_indexToSlot]

theorem denote_toTensor_eq_erase {input layout : Layout} (expr : Expr input layout)
    (arg : Value input) : (expr.denote arg).toTensor = expr.erase.toTensor arg.toTensor := by
  induction expr with
  | arg => rfl
  | arange layout start =>
      funext i
      change BitVec.ofNat 32 (start.val + (layout.slotToIndex (layout.indexToSlot i.1)).val) =
        BitVec.ofNat 32 (start.val + i.1.val)
      rw [slotToIndex_indexToSlot]
  | full => rfl
  | convertLayout dst expr ih =>
      change ((expr.denote arg).convertLayout dst).toTensor = expr.erase.toTensor arg.toTensor
      rw [toTensor_convertLayout, ih]

end Silmaril.Proofs.MLIR.Gluon
