module

public import SqliteWasm.WholeModule
public import SqliteWasmArtifactEntries
public import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.ModuleParts.Defs

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Intrinsic (Code)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand InstrsOk)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

/-- The last call of the exported reactor initializer selects function 23. -/
def initializerConstructor : Func := (definedFunction? sqlite 23).get rfl

def initializerConstructorCode : Code [] [] [] := .done

theorem originalStartAbsent :
    (Binary.Core.decode? originalBytes.toByteArray).map Module.start = some none := by
  rw [originalDecode]
  rfl

theorem originalInitializeExport :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      (m.exports.find? (·.name == "_initialize")).map Export.index) = some (.func ⟨25⟩) := by
  rw [originalDecode]
  rfl

theorem originalInitializeTailCall :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      (definedFunction? m 25).bind fun f => f.body.getLast?) = some (.call ⟨23⟩) := by
  rw [originalDecode]
  rfl

theorem originalInitializerConstructor :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      definedFunction? m 23) = some initializerConstructor := by
  rw [originalDecode]
  rfl

theorem initializerConstructorSignature :
    sqlite.functionSignature? ⟨23⟩ = some ⟨[], []⟩ := rfl

theorem initializerConstructorLocals : initializerConstructor.locals = [] := rfl

theorem initializerConstructorErases :
    initializerConstructorCode.erase = initializerConstructor.body := rfl

theorem initializerConstructorTyped {ctx : Validation.Context} (locals : ctx.locals = []) :
    InstrsOk ctx initializerConstructor.body (.plain [] []) := by
  rw [← initializerConstructorErases]
  exact initializerConstructorCode.sound locals

/-- A resolved call to the actual empty constructor returns without a store update. -/
theorem initializerConstructorReturns {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {address : Nat} {fi : FuncInst H}
    (slot : caller.module.funcs[23]? = some address)
    (entry : s.funcs[address]? = some fi)
    (code : fi.code = .wasm initializerConstructor)
    (signature : Expand fi.type (.func .nil .nil)) :
    Steps P host ⟨s, caller, [.plain (.call ⟨23⟩)]⟩ ⟨s, caller, []⟩ := by
  let callee := Frame.forCall fi.module [] initializerConstructor.locals
  have lookup := Step.call (P := P) (host := host) (x := ⟨23⟩) slot entry
  have enter := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType fi.type) (vs := []) trivial entry signature rfl code
  have label : Step P host ⟨s, callee, [.label 0 [] []]⟩ ⟨s, callee, []⟩ :=
    Step.labelVals (vs := [])
  have leave : Step P host ⟨s, caller, [.frame 0 callee []]⟩ ⟨s, caller, []⟩ :=
    Step.frameVals (vs := []) rfl
  exact ((lookup.steps.tail enter).trans (Steps.frame (f := caller) (n := 0) label.steps)).tail leave

end SqliteWasm
