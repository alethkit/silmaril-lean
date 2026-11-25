module

import SqliteWasm.PostInitVarint

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open SqliteWasm SqliteWasmArtifact

set_option maxRecDepth 65536

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress readerAddress fn fi,
      let after := threadSetupMemory (initializerMark mem 0) 0
      let initialized := runtime.setMem memoryAddress after
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func 25⟩ ∧
      InvokeOk runtime 25 [] ∧
      Steps P host (invoke runtime 25 []) ⟨initialized, {}, []⟩ ∧
      ((Binary.Core.decode? originalBytes.toByteArray).bind (fun decoded => definedFunction? decoded 434)) =
        some fn ∧
      frame.module.funcs[434]? = some readerAddress ∧
      runtime.funcs[readerAddress]? = some fi ∧
      initialized.funcs[readerAddress]? = some fi ∧
      fi.code = .wasm fn ∧
      initialized.mem? { module := fi.module } ⟨0⟩ = some (memoryAddress, after) ∧
      after.bytes.size = 131072 ∧
      Varint.read? (File.View.ofBytes ⟨after.bytes⟩) 59328 = some (1, 59329) ∧
      ∀ dst : BitVec 32, dst.toNat + 8 ≤ after.bytes.size →
        Steps P host ⟨initialized, frame, vals [.i32 59328, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨initialized.setMem memoryAddress
            { after with bytes := Memory.writeSlice after.bytes dst.toNat (Memory.encodeLE 8 1) },
            frame, [constI32 1]⟩ := by
  rw [originalDecode, Option.bind_some, Option.bind_some]
  exact reactorPostInitVarint P host

#print axioms originalDecode
#print axioms reactorPostInitVarint
