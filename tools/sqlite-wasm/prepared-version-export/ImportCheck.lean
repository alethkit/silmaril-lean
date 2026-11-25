module

import SqliteWasm.PreparedVersionExport
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType)
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 131072

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_libversion_number") =
        some ⟨"sqlite3_libversion_number", .func address⟩ ∧
      InvokeOk runtime address [] ∧
      Steps P host (invoke runtime address []) ⟨runtime, {}, [constI32 3054001]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedVersionExport P host

private def version : Func := (definedFunction? sqlite 289).get (by kernel_rfl)
private def runtimeType : DefType := ((allocTypes sqlite.types)[version.type.toNat]?).get (by kernel_rfl)

private def initial : Store Nat :=
  { funcs := [⟨runtimeType, {}, .wasm version⟩]
    mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0x5a]⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 17⟩] }

example : runIK neverFail 32 (invoke initial 0 []) =
    (⟨initial, {}, [constI32 3054001]⟩, true) := by
  kernel_rfl

#print axioms originalDecode
#print axioms originalVersionExport
#print axioms originalVersionFunction
#print axioms reactorPreparedVersionExport

end SqliteWasm
