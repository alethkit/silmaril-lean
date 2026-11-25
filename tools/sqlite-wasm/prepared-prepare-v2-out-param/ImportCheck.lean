module

import SqliteWasm.PreparedPrepareV2OutParam
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

sqlite_check_eq originalPrepareV2OutputExport :
    sourceExport? original "sqlite3_prepare_v2" = some 113

example (P : Profile) (host : HostSemantics Nat)
    (db sql nByte stmtOut tailOut : BitVec 32) (bound : stmtOut.toNat + 4 ≤ 131072) :
    let args : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    ∃ runtime frame address helperAddress wrapper code stack memory mem,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_prepare_v2") =
        some ⟨"sqlite3_prepare_v2", .func address⟩ ∧
      frame.module.funcs[113]? = some address ∧
      frame.module.funcs[105]? = some helperAddress ∧
      definedFunction? sqlite 113 = some wrapper ∧
      definedFunction? sqlite 105 = some code ∧
      runtime.global? frame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) ∧
      runtime.mem? frame ⟨0⟩ = some (memory, mem) ∧
      InvokeOk runtime address args ∧
      let lowered := runtime.setGlobal stack (.i32 126096)
      let cleared := Memory.writeSlice mem.bytes stmtOut.toNat (Memory.encodeLE 4 0)
      Steps P host (invoke runtime address args)
        ⟨lowered.setMem memory { mem with bytes := cleared }, {}, [
          .frame 1 (Frame.forCall frame.module args wrapper.locals) [.label 1 [] [
            .frame 1 ((Frame.forCall frame.module forwarded code.locals).setLocal ⟨7⟩ (.i32 126096))
              [.label 1 [] (expression (code.body.drop 8))]
          ]]
        ]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedPrepareV2ClearsOutput P host db sql nByte stmtOut tailOut bound

private def wrapper : Func := (definedFunction? sqlite 113).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 105).get (by kernel_rfl)
private def wrapperType : DefType := ((allocTypes sqlite.types)[wrapper.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType := ((allocTypes sqlite.types)[helper.type.toNat]?).get (by kernel_rfl)

private def linked : ModuleInst := { funcs := (List.replicate 114 0).set 105 1, globals := [0], mems := [0] }

private def initial : Store Nat :=
  { funcs := [⟨wrapperType, linked, .wasm wrapper⟩, ⟨helperType, linked, .wasm helper⟩]
    mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0x11, 0x22, 0x33, 0x44, 0x5a]⟩⟩]
    globals := [⟨⟨.var, .i32⟩, .i32 126112⟩] }

example : (helper.body.drop 8).take 2 = [.localGet ⟨0⟩, .call ⟨130⟩] := by
  kernel_rfl

private def args : List Val := [.i32 11, .i32 23, .i32 0xffffffff, .i32 1, .i32 43]
private def forwarded : List Val := [.i32 11, .i32 23, .i32 0xffffffff, .i32 128, .i32 0,
  .i32 1, .i32 43]

private def memoryAfter : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0, 0, 0, 0, 0x5a]⟩⟩

example : runIK neverFail 15 (invoke initial 0 args) =
    (⟨(initial.setGlobal 0 (.i32 126096)).setMem 0 memoryAfter, {}, [
      .frame 1 (Frame.forCall linked args wrapper.locals) [.label 1 [] [
        .frame 1 ((Frame.forCall linked forwarded helper.locals).setLocal ⟨7⟩ (.i32 126096))
          [.label 1 [] (expression (helper.body.drop 8))]
      ]]
    ]⟩, false) := by
  kernel_rfl

#print axioms originalPrepareV2OutputExport
#print axioms originalDecode
#print axioms reactorPreparedPrepareV2Entry
#print axioms reactorPreparedPrepareV2ClearsOutput

end SqliteWasm
