module

import SqliteWasm.PreparedFinalizeNull
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType)
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 65536

sqlite_check_eq originalFinalizeExport :
    sourceExport? original "sqlite3_finalize" = some 111

sqlite_check_eq originalFinalizeFunction :
    sourceFunction? original 111 = definedFunction? sqlite 111

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_finalize") =
        some ⟨"sqlite3_finalize", .func address⟩ ∧
      frame.module.funcs[111]? = some address ∧
      InvokeOk runtime address [.i32 0] ∧
      Steps P host (invoke runtime address [.i32 0]) ⟨runtime, {}, [constI32 0]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedFinalizeNull P host

private def finalize : Func := (definedFunction? sqlite 111).get (by kernel_rfl)
private def finalizeType : DefType := ((allocTypes sqlite.types)[finalize.type.toNat]?).get (by kernel_rfl)

private def initial : Store Nat :=
  { funcs := [⟨finalizeType, { globals := [0] }, .wasm finalize⟩]
    mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0x5a]⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 126112⟩, ⟨⟨.var, .i32⟩, .i32 17⟩] }

example :
    runIK neverFail 64 (invoke initial 0 [.i32 0]) =
      (⟨initial, {}, [constI32 0]⟩, true) := by
  kernel_rfl

#print axioms originalFinalizeExport
#print axioms originalFinalizeFunction
#print axioms originalDecode
#print axioms reactorPreparedFinalizeNull

end SqliteWasm
