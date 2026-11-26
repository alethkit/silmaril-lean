module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples.Defs
public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Thms
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples

/-! Checked emission, closed Core instantiation and invocation of `run`. -/

public section

namespace Silmaril.MLIR.WasmSSA.ModuleCall.Examples

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand validate?)

theorem source_signatures : source.signatures = declared := rfl

theorem leafIndex_lookup :
    source.signatures.funcs[leafIndex.toNat]? = some ("select_difference", ⟨Params, .i64⟩) :=
  callIndex?_lookup site rfl

theorem emitted_functions : coreModule.funcs = [wrapperCode, WasmSSA.Examples.expected] ∧
    wrapperCode.body = [.localGet ⟨0⟩, .localGet ⟨1⟩, .call leafIndex, .return_] ∧
    leafIndex.toNat = 1 := ⟨rfl, rfl, rfl⟩

theorem coreModule_validates : validate? coreModule = some checkedType ∧
    checkedType.imports = [] := ⟨rfl, rfl⟩

/-- Instantiation of the validated closed module needs no further start or segment steps. -/
theorem coreModule_instantiates (P : Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) coreModule [] instantiated ∧ instantiated.code = [] :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.coreModule_instantiates P host

theorem export_allocated : instantiated.frame.module.exports = [⟨"run", .func wrapperAddress⟩] ∧
    instantiated.store.funcs[wrapperAddress]? = some wrapperInstance ∧
    wrapperInstance.module = instantiated.frame.module ∧ wrapperInstance.code = .wasm wrapperCode :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem leaf_allocated :
    instantiated.frame.module.funcs[leafIndex.toNat]? = some leafAddress ∧
    instantiated.store.funcs[leafAddress]? = some leafInstance ∧
    leafInstance.code = .wasm WasmSSA.Examples.expected := ⟨rfl, rfl, rfl⟩

theorem invoke_export_ok (x y : BitVec 64) :
    InvokeOk instantiated.store wrapperAddress [.i64 x, .i64 y] := by
  refine ⟨wrapperInstance, _, _, rfl,
    (show Expand wrapperInstance.type (Func.coreSignature Params .i64) from Expand.iff.mpr rfl), ?_⟩
  exact .cons (.num _) (.cons (.num _) .nil)

/-- Invocation of the allocated export has a run to the leaf's source result,
with the instantiated store preserved. -/
theorem invoke_export (P : Profile) (host : HostSemantics Empty) (x y : BitVec 64) :
    Steps P host (invoke instantiated.store wrapperAddress [.i64 x, .i64 y])
      ⟨instantiated.store, {}, vals [result x y]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.invoke_export P host x y

example : emitCall? source.signatures "select_difference" Params .i64 = some (.call leafIndex) := rfl
example : emitCall? source.signatures "missing" Params .i64 = none := rfl
example : emitCall? source.signatures "select_difference" [.i64, .i32] .i64 = none := rfl
example : emitCall? source.signatures "select_difference" Params .i32 = none := rfl

example (P : Profile) (host : HostSemantics Empty) :
    Steps P host (invoke instantiated.store wrapperAddress [.i64 5, .i64 9])
      ⟨instantiated.store, {}, vals [.i64 0xfffffffffffffffc]⟩ := invoke_export P host 5 9

example (P : Profile) (host : HostSemantics Empty) :
    Steps P host (invoke instantiated.store wrapperAddress [.i64 5, .i64 5])
      ⟨instantiated.store, {}, vals [.i64 5]⟩ := invoke_export P host 5 5

end Silmaril.MLIR.WasmSSA.ModuleCall.Examples
