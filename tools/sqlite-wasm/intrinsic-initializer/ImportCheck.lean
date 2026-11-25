module

import SqliteWasm.IntrinsicInitializer

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand InstrsOk)
open SqliteWasm
open SqliteWasmArtifact (definedFunction?)

example :
    (Binary.Core.decode? originalBytes.toByteArray).map Module.start = some none ∧
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      (m.exports.find? (·.name == "_initialize")).map Export.index) = some (.func ⟨25⟩) :=
  ⟨originalStartAbsent, originalInitializeExport⟩

example :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      (definedFunction? m 25).bind fun f => f.body.getLast?) = some (.call ⟨23⟩) :=
  originalInitializeTailCall

example :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      definedFunction? m 23) = some initializerConstructor :=
  originalInitializerConstructor

example : initializerConstructorCode.erase = initializerConstructor.body :=
  initializerConstructorErases

example : InstrsOk {} initializerConstructor.body (.plain [] []) :=
  initializerConstructorTyped rfl

example {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {caller : Frame}
    {address : Nat} {fi : FuncInst H} (slot : caller.module.funcs[23]? = some address)
    (entry : s.funcs[address]? = some fi) (code : fi.code = .wasm initializerConstructor)
    (signature : Expand fi.type (.func .nil .nil)) :
    Steps P host ⟨s, caller, [.plain (.call ⟨23⟩)]⟩ ⟨s, caller, []⟩ :=
  initializerConstructorReturns slot entry code signature

#print axioms originalStartAbsent
#print axioms originalInitializeExport
#print axioms originalInitializeTailCall
#print axioms originalInitializerConstructor
#print axioms initializerConstructorSignature
#print axioms initializerConstructorLocals
#print axioms initializerConstructorErases
#print axioms initializerConstructorTyped
#print axioms initializerConstructorReturns
