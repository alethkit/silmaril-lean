module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Completion.Thms
public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples.Thms
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.CompletionExample

/-! Every maximal execution of the allocated export has the same result. -/

public section

namespace Silmaril.MLIR.WasmSSA.ModuleCall.Examples

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- Every finite prefix of `run` can continue to the specified terminal result,
with the instantiated store unchanged throughout. No infinite execution exists. -/
theorem invoke_export_completes (P : Profile) (host : HostSemantics Empty) (x y : BitVec 64) :
    CompletesAt P host (invoke instantiated.store wrapperAddress [.i64 x, .i64 y])
      ⟨instantiated.store, {}, vals [result x y]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall.invoke_export_completes P host x y

end Silmaril.MLIR.WasmSSA.ModuleCall.Examples
