module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Index

/-! The emitted index identifies the exact checked signature in declaration order. -/

public section

namespace Silmaril.MLIR.WasmSSA.ModuleCall

universe u v

variable {I : Type u} {O : Type v} {symbols : MLIR.Module (FuncSignature I O)}
  {inputs : I} {outputs : O}

theorem callIndex?_lookup (call : DirectCall symbols inputs outputs) {index : Wasm.FuncIdx}
    (emitted : callIndex? call = some index) :
    symbols.funcs[index.toNat]? = some (call.callee, ⟨inputs, outputs⟩) :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.callIndex?_lookup call emitted

theorem callIndex?_exists (call : DirectCall symbols inputs outputs)
    (fits : symbols.funcs.length ≤ 2 ^ 32) : ∃ index, callIndex? call = some index :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.callIndex?_exists call fits

theorem emitCall?_eq_some [DecidableEq I] [DecidableEq O] {callee : String} {index : Wasm.FuncIdx} :
    emitCall? symbols callee inputs outputs = some (.call index) ↔
      symbols.find? callee = some ⟨inputs, outputs⟩ ∧ symbolIndex? symbols callee = some index :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.emitCall?_eq_some

end Silmaril.MLIR.WasmSSA.ModuleCall
