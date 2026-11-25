module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame)

def v1Code (ty : Option NumType) : State → List Wasm.V1.Execution.Admin
  | .nested n below result => [.label ty.toList.length []
      [.label n [] (Wasm.V1.Execution.values (below ++ result) ++ [.source (.br ⟨1⟩)])]]
  | .outer below result => [.label ty.toList.length []
      (Wasm.V1.Execution.values (below ++ result) ++ [.source (.br ⟨0⟩)])]
  | .done result => Wasm.V1.Execution.values result

def limeCode (ty : Option NumType) : State → List Wasm.Lime1.Execution.Admin
  | .nested n below result => [.label ty.toList.length []
      [.label n [] (Wasm.Lime1.Execution.values (below ++ result) ++ [.source (.br ⟨1⟩)])]]
  | .outer below result => [.label ty.toList.length []
      (Wasm.Lime1.Execution.values (below ++ result) ++ [.source (.br ⟨0⟩)])]
  | .done result => Wasm.Lime1.Execution.values result

def coreCode (ty : Option NumType) : State → List Core.Admin
  | .nested n below result => [.label ty.toList.length []
      [.label n [] (Core.vals ((below ++ result).map LegacyDivision.liftValue) ++ [.plain (.br ⟨1⟩)])]]
  | .outer below result => [.label ty.toList.length []
      (Core.vals ((below ++ result).map LegacyDivision.liftValue) ++ [.plain (.br ⟨0⟩)])]
  | .done result => Core.vals (result.map LegacyDivision.liftValue)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (ty : Option NumType)
    (a : State) : Wasm.V1.Execution.Config H :=
  ⟨s, f, v1Code ty a⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (ty : Option NumType)
    (a : State) : Wasm.Lime1.Execution.Config H :=
  ⟨s, f, limeCode ty a⟩

def coreConfig {H : Type} (s : Core.Store H) (f : Core.Frame) (ty : Option NumType)
    (a : State) : Core.Config H :=
  ⟨s, f, coreCode ty a⟩

end Silmaril.Wasm.Institution.Operational.BranchExit
