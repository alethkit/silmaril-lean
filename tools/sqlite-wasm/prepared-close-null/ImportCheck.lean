module

import SqliteWasm.PreparedCloseNull
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

sqlite_check_eq originalCloseExport :
    sourceExport? original "sqlite3_close" = some 295

sqlite_check_eq originalCloseWrapper :
    sourceFunction? original 295 = definedFunction? sqlite 295

theorem decodedCloseHelper :
    ((Binary.Core.decode? originalBytes.toByteArray).bind (fun m => definedFunction? m 296)) =
      definedFunction? sqlite 296 := by
  rw [originalDecode, Option.bind_some]

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address helperAddress,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_close") =
        some ⟨"sqlite3_close", .func address⟩ ∧
      frame.module.funcs[295]? = some address ∧
      frame.module.funcs[296]? = some helperAddress ∧
      InvokeOk runtime address [.i32 0] ∧
      Steps P host (invoke runtime address [.i32 0]) ⟨runtime, {}, [constI32 0]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedCloseNull P host

private def wrapper : Func := (definedFunction? sqlite 295).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 296).get (by kernel_rfl)
private def wrapperType : DefType := ((allocTypes sqlite.types)[wrapper.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType := ((allocTypes sqlite.types)[helper.type.toNat]?).get (by kernel_rfl)

private def linked : ModuleInst :=
  { funcs := (List.replicate 297 0).set 296 1, globals := [0] }

private def initial : Store Nat :=
  { funcs := [⟨wrapperType, linked, .wasm wrapper⟩, ⟨helperType, linked, .wasm helper⟩]
    mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0x5a]⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 126112⟩, ⟨⟨.var, .i32⟩, .i32 17⟩] }

example :
    runIK neverFail 64 (invoke initial 0 [.i32 0]) =
      (⟨initial, {}, [constI32 0]⟩, true) := by
  kernel_rfl

#print axioms originalCloseExport
#print axioms originalCloseWrapper
#print axioms decodedCloseHelper
#print axioms originalDecode
#print axioms reactorPreparedCloseNull

end SqliteWasm
