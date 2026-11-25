module

import SqliteWasm.PreparedInitReentry

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open SqliteWasm

set_option maxRecDepth 65536

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress fi,
      let after := threadSetupMemory (initializerMark mem 0) 0
      let initialized := runtime.setMem memoryAddress after
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func 25⟩ ∧
      frame.module.funcs[25]? = some 25 ∧
      runtime.funcs[25]? = some fi ∧
      initialized.funcs[25]? = some fi ∧
      fi.module = frame.module ∧
      fi.code = .wasm initializerFunction ∧
      initialized.mem? (Frame.forCall fi.module [] initializerFunction.locals) ⟨0⟩ =
        some (memoryAddress, after) ∧
      Memory.load after.bytes (initializerAddress 0) 4 = some 1 ∧
      InvokeOk runtime 25 [] ∧
      Steps P host (invoke runtime 25 []) ⟨initialized, {}, []⟩ ∧
      InvokeOk initialized 25 [] ∧
      Steps P host (invoke initialized 25 []) ⟨initialized, {}, [.trap]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedInitReentry P host

#print axioms originalDecode
#print axioms reactorPreparedInitReentry
