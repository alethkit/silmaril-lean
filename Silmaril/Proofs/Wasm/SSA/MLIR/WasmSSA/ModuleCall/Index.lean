module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Defs

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall

open Silmaril.MLIR
open Silmaril.MLIR.WasmSSA.ModuleCall

universe u v

private theorem findIdx_lookup {F : Type u} {symbols : MLIR.Module F} {name : String} {entry : F}
    (found : symbols.find? name = some entry) :
    ∃ position, symbols.funcs.findIdx? (fun item => name == item.1) = some position ∧
      symbols.funcs[position]? = some (name, entry) := by
  obtain ⟨before, after, entries, earlier⟩ := List.lookup_eq_some_iff.mp found
  have skipped : before.findIdx? (fun item => name == item.1) = none :=
    List.findIdx?_eq_none_iff.mpr (by simpa [bne] using earlier)
  refine ⟨before.length, ?_, ?_⟩
  · simp [entries, List.findIdx?_append, skipped, List.findIdx?_cons]
  · simp [entries]

variable {I : Type u} {O : Type v} {symbols : MLIR.Module (FuncSignature I O)}
  {inputs : I} {outputs : O}

theorem callIndex?_lookup (call : DirectCall symbols inputs outputs) {index : Wasm.FuncIdx}
    (emitted : callIndex? call = some index) :
    symbols.funcs[index.toNat]? = some (call.callee, ⟨inputs, outputs⟩) := by
  obtain ⟨position, found, atPosition⟩ := findIdx_lookup call.resolved
  simp only [callIndex?, symbolIndex?, found, Option.bind_some, Wasm.Idx.ofNat?_eq_some_iff] at emitted
  exact emitted ▸ atPosition

theorem callIndex?_exists (call : DirectCall symbols inputs outputs)
    (fits : symbols.funcs.length ≤ 2 ^ 32) : ∃ index, callIndex? call = some index := by
  obtain ⟨position, found, atPosition⟩ := findIdx_lookup call.resolved
  have bound := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp atPosition).choose fits
  exact ⟨⟨⟨position, bound⟩⟩, by
    simp [callIndex?, symbolIndex?, found, Wasm.Idx.ofNat?_eq_some_iff, Wasm.Idx.toNat]⟩

theorem emitCall?_eq_some [DecidableEq I] [DecidableEq O]
    {callee : String} {index : Wasm.FuncIdx} :
    emitCall? symbols callee inputs outputs = some (.call index) ↔
      symbols.find? callee = some ⟨inputs, outputs⟩ ∧ symbolIndex? symbols callee = some index := by
  by_cases found : symbols.find? callee = some ⟨inputs, outputs⟩
  · cases h : symbolIndex? symbols callee <;>
      simp [emitCall?, DirectCall.resolve?, found, callIndex?, h]
  · simp [emitCall?, DirectCall.resolve?, found]

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall
