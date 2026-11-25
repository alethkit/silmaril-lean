module

import SqliteWasm.PreparedFreeNull
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType)
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 65536

sqlite_check_eq originalFreeExport :
    sourceExport? original "free" = some 1546

theorem decodedFreeFunctions :
    (Binary.Core.decode? originalBytes.toByteArray).map
      (fun m => (definedFunction? m 1546, definedFunction? m 1547)) =
        some (definedFunction? sqlite 1546, definedFunction? sqlite 1547) := by
  rw [originalDecode, Option.map_some]

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address helperAddress,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "free") = some ⟨"free", .func address⟩ ∧
      frame.module.funcs[1546]? = some address ∧
      frame.module.funcs[1547]? = some helperAddress ∧
      InvokeOk runtime address [.i32 0] ∧
      Steps P host (invoke runtime address [.i32 0]) ⟨runtime, {}, []⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedFreeNull P host

private def wrapper : Func := (definedFunction? sqlite 1546).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 1547).get (by kernel_rfl)
private def wrapperType : DefType := ((allocTypes sqlite.types)[wrapper.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType := ((allocTypes sqlite.types)[helper.type.toNat]?).get (by kernel_rfl)

private def linked : ModuleInst := { funcs := (List.replicate 1548 0).set 1547 1 }

private def initial : Store Nat :=
  { funcs := [⟨wrapperType, linked, .wasm wrapper⟩, ⟨helperType, linked, .wasm helper⟩]
    mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0x5a]⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 17⟩] }

example : runIK neverFail 64 (invoke initial 0 [.i32 0]) = (⟨initial, {}, []⟩, true) := by
  kernel_rfl

#print axioms originalFreeExport
#print axioms decodedFreeFunctions
#print axioms originalDecode
#print axioms reactorPreparedFreeNull

end SqliteWasm
