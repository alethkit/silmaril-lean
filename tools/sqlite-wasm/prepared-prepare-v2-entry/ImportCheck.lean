module

import SqliteWasm.PreparedPrepareV2Entry
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

sqlite_check_eq originalPrepareV2Export :
    sourceExport? original "sqlite3_prepare_v2" = some 113

theorem decodedPrepareV2Functions :
    (Binary.Core.decode? originalBytes.toByteArray).map
      (fun m => (definedFunction? m 113, definedFunction? m 105)) =
        some (definedFunction? sqlite 113, definedFunction? sqlite 105) := by
  rw [originalDecode, Option.map_some]

example (P : Profile) (host : HostSemantics Nat) (db sql nByte stmtOut tailOut : BitVec 32) :
    let args : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    ∃ runtime frame address helperAddress wrapper helper wrapperTy helperTy,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_prepare_v2") =
        some ⟨"sqlite3_prepare_v2", .func address⟩ ∧
      frame.module.funcs[113]? = some address ∧
      frame.module.funcs[105]? = some helperAddress ∧
      definedFunction? sqlite 113 = some wrapper ∧
      definedFunction? sqlite 105 = some helper ∧
      runtime.funcs[address]? = some ⟨wrapperTy, frame.module, .wasm wrapper⟩ ∧
      runtime.funcs[helperAddress]? = some ⟨helperTy, frame.module, .wasm helper⟩ ∧
      InvokeOk runtime address args ∧
      Steps P host (invoke runtime address args) ⟨runtime, {}, [
        .frame 1 (Frame.forCall frame.module args wrapper.locals) [.label 1 [] [
          .frame 1 (Frame.forCall frame.module forwarded helper.locals) [.label 1 [] (expression helper.body)]
        ]]
      ]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedPrepareV2Entry P host db sql nByte stmtOut tailOut

private def wrapper : Func := (definedFunction? sqlite 113).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 105).get (by kernel_rfl)
private def wrapperType : DefType := ((allocTypes sqlite.types)[wrapper.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType := ((allocTypes sqlite.types)[helper.type.toNat]?).get (by kernel_rfl)

private def linked : ModuleInst := { funcs := (List.replicate 114 0).set 105 1 }

private def initial : Store Nat :=
  { funcs := [⟨wrapperType, linked, .wasm wrapper⟩, ⟨helperType, linked, .wasm helper⟩]
    mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0x5a]⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 17⟩] }

private def args : List Val := [.i32 11, .i32 23, .i32 0xffffffff, .i32 37, .i32 43]
private def forwarded : List Val := [.i32 11, .i32 23, .i32 0xffffffff, .i32 128, .i32 0,
  .i32 37, .i32 43]

example : runIK neverFail 8 (invoke initial 0 args) = (⟨initial, {}, [
    .frame 1 (Frame.forCall linked args wrapper.locals) [.label 1 [] [
      .frame 1 (Frame.forCall linked forwarded helper.locals) [.label 1 [] (expression helper.body)]
    ]]
  ]⟩, false) := by
  kernel_rfl

#print axioms originalPrepareV2Export
#print axioms decodedPrepareV2Functions
#print axioms originalDecode
#print axioms reactorPreparedPrepareV2Entry

end SqliteWasm
