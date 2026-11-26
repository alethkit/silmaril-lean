module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples.Thms
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Completion
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Completion.Thms

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall

open Silmaril.MLIR.WasmSSA (CompletesAt Func)
open Silmaril.MLIR.WasmSSA.Examples (context selectDifference)
open Silmaril.MLIR.WasmSSA.ModuleCall.Examples
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand)

theorem invoke_export_completes (P : Profile) (host : HostSemantics Empty) (x y : BitVec 64) :
    CompletesAt P host (invoke instantiated.store wrapperAddress [.i64 x, .i64 y])
      ⟨instantiated.store, {}, vals [result x y]⟩ := by
  let s := instantiated.store
  let caller := Frame.forCall wrapperInstance.module [.i64 x, .i64 y] wrapperCode.locals
  let done : Config Empty := ⟨s, caller, vals [result x y] ++ [.plain .return_]⟩
  obtain ⟨moduleLookup, leafLookup, leafStored⟩ := leaf_allocated
  obtain ⟨_, wrapperLookup, wrapperModule, wrapperStored⟩ := export_allocated
  have calleeIndex : caller.module.funcs[leafIndex.toNat]? = some leafAddress := by
    change wrapperInstance.module.funcs[leafIndex.toNat]? = some leafAddress
    rw [wrapperModule]
    exact moduleLookup
  have leafType : Expand leafInstance.type (Func.coreSignature Params .i64) := Expand.iff.mpr rfl
  have wrapperType : Expand wrapperInstance.type (Func.coreSignature Params .i64) := Expand.iff.mpr rfl
  have fits : selectDifference.Fits := by decide
  have leafBody := selectDifference.toWasm_body_completes context ⟨0⟩ fits (args x y)
    leafInstance.module P host s
  have call : CompletesAt P host
      ⟨s, caller, vals [.i64 x, .i64 y] ++ [.plain (.call leafIndex), .plain .return_]⟩ done :=
    MLIR.WasmSSA.ModuleCall.directCall_completes_then (below := []) calleeIndex leafLookup
      leafStored leafType rfl rfl leafBody
      (completes_here (fun _ => Step.return_vals_stuck))
  have readY : CompletesAt P host
      ⟨s, caller, vals [.i64 x] ++ [.plain (.localGet ⟨1⟩), .plain (.call leafIndex), .plain .return_]⟩
      done := localGet_completes_then (below := [.i64 x]) (v := .i64 y) rfl call
  have body : CompletesAt P host ⟨s, caller, expression wrapperCode.body⟩ done :=
    localGet_completes_then (below := []) (v := .i64 x) rfl readY
  exact MLIR.WasmSSA.ModuleCall.invoke_completes_of_body wrapperLookup wrapperStored
    wrapperType rfl rfl ⟨_, body⟩

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall
