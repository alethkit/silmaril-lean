module

import SqliteWasm.PreparedInitVersion

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 131072

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress versionAddress versionEntry,
      let initialized := runtime.setMem memoryAddress (threadSetupMemory (initializerMark mem 0) 0)
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func 25⟩ ∧
      frame.module.exports.find? (·.name == "sqlite3_libversion_number") =
        some ⟨"sqlite3_libversion_number", .func versionAddress⟩ ∧
      runtime.mem? frame ⟨0⟩ = some (memoryAddress, mem) ∧
      runtime.funcs[versionAddress]? = some versionEntry ∧
      initialized.funcs[versionAddress]? = some versionEntry ∧
      InvokeOk runtime 25 [] ∧
      Steps P host (invoke runtime 25 []) ⟨initialized, {}, []⟩ ∧
      InvokeOk initialized versionAddress [] ∧
      Steps P host (invoke initialized versionAddress []) ⟨initialized, {}, [constI32 3054001]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedInitVersion P host

#print axioms originalDecode
#print axioms reactorPreparedInitVersion

end SqliteWasm
