module

import SqliteWasm.PreparedPrepareV2NullRejection
import SqliteWasm.ArtifactCheck

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open SqliteWasmArtifact

set_option maxRecDepth 65536

sqlite_check_eq originalPrepareV2RejectedExport :
    sourceExport? original "sqlite3_prepare_v2" = some 113

theorem decodedPrepareV2RejectionFunctions :
    (Binary.Core.decode? originalBytes.toByteArray).map (fun m =>
      (definedFunction? m 113, definedFunction? m 105, definedFunction? m 130, definedFunction? m 26)) =
      some (definedFunction? sqlite 113, definedFunction? sqlite 105,
        definedFunction? sqlite 130, definedFunction? sqlite 26) := by
  rw [originalDecode, Option.map_some]

example (P : Profile) (host : HostSemantics Nat)
    (nByte stmtOut tailOut : BitVec 32) (bound : stmtOut.toNat + 4 ≤ 131072)
    (outCallback : 53000 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 52996)
    (outCheckScratch : 126084 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 126080)
    (outReportScratch : 126108 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 126096) :
    let args : List Val := [.i32 0, .i32 0, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    ∃ runtime frame address helperAddress checkAddress logAddress wrapper helperFn checkFn logFn
        wrapperTy helperTy checkTy logTy stack memory mem,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_prepare_v2") =
        some ⟨"sqlite3_prepare_v2", .func address⟩ ∧
      frame.module.funcs[113]? = some address ∧ frame.module.funcs[105]? = some helperAddress ∧
      frame.module.funcs[130]? = some checkAddress ∧ frame.module.funcs[26]? = some logAddress ∧
      definedFunction? sqlite 113 = some wrapper ∧ definedFunction? sqlite 105 = some helperFn ∧
      definedFunction? sqlite 130 = some checkFn ∧ definedFunction? sqlite 26 = some logFn ∧
      (allocTypes sqlite.types)[checkFn.type.toNat]? = some checkTy ∧
      (allocTypes sqlite.types)[logFn.type.toNat]? = some logTy ∧
      runtime.funcs[address]? = some ⟨wrapperTy, frame.module, .wasm wrapper⟩ ∧
      runtime.funcs[helperAddress]? = some ⟨helperTy, frame.module, .wasm helperFn⟩ ∧
      runtime.funcs[checkAddress]? = some ⟨checkTy, frame.module, .wasm checkFn⟩ ∧
      runtime.funcs[logAddress]? = some ⟨logTy, frame.module, .wasm logFn⟩ ∧
      runtime.global? frame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) ∧
      runtime.mem? frame ⟨0⟩ = some (memory, mem) ∧
      stmtOut.toNat + 4 ≤ mem.bytes.size ∧ 126108 ≤ mem.bytes.size ∧
      InvokeOk runtime address args ∧
      (Memory.load mem.bytes 52996 4 = some 0 →
        Memory.load (prepareV2NullRejectionBytes mem.bytes stmtOut.toNat) stmtOut.toNat 4 = some 0 ∧
        Steps P host (invoke runtime address args)
          ⟨runtime.setMem memory
            { mem with bytes := prepareV2NullRejectionBytes mem.bytes stmtOut.toNat },
            {}, [constI32 21]⟩) := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedPrepareV2NullRejection P host nByte stmtOut tailOut
    bound outCallback outCheckScratch outReportScratch

-- Check both in-bounds output placements against the imported theorem.
example (P : Profile) (host : HostSemantics Nat) :=
  reactorPreparedPrepareV2NullRejection P host 0 65536 0
    (by decide) (Or.inl (by decide)) (Or.inr (by decide)) (Or.inr (by decide))

example (P : Profile) (host : HostSemantics Nat) :=
  reactorPreparedPrepareV2NullRejection P host 0 131068 0
    (by decide) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))

#print axioms originalPrepareV2RejectedExport
#print axioms decodedPrepareV2RejectionFunctions
#print axioms originalDecode
#print axioms reactorPreparedPrepareV2NullRejection

end SqliteWasm
