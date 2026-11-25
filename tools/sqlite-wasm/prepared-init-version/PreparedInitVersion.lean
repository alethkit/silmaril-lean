module

public import SqliteWasm.PreparedInvocation
import SqliteWasm.PreparedVersionExport

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 65536

/-- The pinned reactor returns its version after calling the prepared initializer.
The second invocation starts and ends with the exact store returned by the first. -/
theorem reactorPreparedInitVersion (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress versionAddress versionEntry,
      let initialized := runtime.setMem memoryAddress (threadSetupMemory (initializerMark mem 0) 0)
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
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
  obtain ⟨runtime, frame, mem, memoryAddress, prepared, initExport, mapped, initOk, runInit⟩ :=
    reactorPreparedInvocation P host
  obtain ⟨versionRuntime, versionFrame, versionAddress, versionEntry,
    versionPrepared, versionExport, entry, runVersion⟩ :=
    reactorPreparedVersionExportWithEntry P host
  obtain ⟨sameStore, frameAndStart⟩ := Prod.mk.inj (Option.some.inj (prepared.symm.trans versionPrepared))
  have sameFrame := (Prod.mk.inj frameAndStart).1
  subst versionRuntime
  subst versionFrame
  let initialized := runtime.setMem memoryAddress (threadSetupMemory (initializerMark mem 0) 0)
  have retained : initialized.funcs[versionAddress]? = some versionEntry := entry
  exact ⟨runtime, frame, mem, memoryAddress, versionAddress, versionEntry, prepared, initExport,
    versionExport, mapped, entry, retained, initOk, runInit, runVersion initialized retained⟩

#print axioms reactorPreparedInitVersion

end SqliteWasm
