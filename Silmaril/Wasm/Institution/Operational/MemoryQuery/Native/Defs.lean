module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Defs
public import Silmaril.Wasm.Lime1.Execution.Transport
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Wasm.Execution

def arg : Wasm.V1.MemArg := ⟨2, 0⟩
def index : MemIdx := ⟨0⟩

def v1CodeAt (immediate : Wasm.V1.MemArg) : State → List Wasm.V1.Execution.Admin
  | .size => [.source .memorySize]
  | .load address => [.source (.intConst .i32 address), .source (.intLoad .i32 none immediate)]
  | .value bits => [.source (.intConst .i32 bits)]
  | .trap => [.trap]

def limeCodeAt (immediate : Wasm.V1.MemArg) : State → List Wasm.Lime1.Execution.Admin
  | .size => [.source .memorySize]
  | .load address => [.source (.intConst .i32 address), .source (.intLoad .i32 none immediate)]
  | .value bits => [.source (.intConst .i32 bits)]
  | .trap => [.trap]

def coreCodeAt (immediate : Wasm.V1.MemArg) : State → List Core.Admin
  | .size => [.plain (.memorySize index)]
  | .load address => [.plain (.intConst .i32 address), .plain (.intLoad .i32 none index immediate.toCore)]
  | .value bits => [.plain (.intConst .i32 bits)]
  | .trap => [.trap]

def v1ConfigAt {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.V1.Execution.Store H) (f : Runtime.Frame) (q : State) :
    Wasm.V1.Execution.Config H := ⟨s, f, v1CodeAt immediate q⟩

def limeConfigAt {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.Lime1.Execution.Store H) (f : Runtime.Frame) (q : State) :
    Wasm.Lime1.Execution.Config H := ⟨s, f, limeCodeAt immediate q⟩

def coreConfigAt {H : Type} (immediate : Wasm.V1.MemArg) (s : Core.Store H) (f : Core.Frame) (q : State) : Core.Config H :=
  ⟨s, f, coreCodeAt immediate q⟩

abbrev v1Code := v1CodeAt arg
abbrev limeCode := limeCodeAt arg
abbrev coreCode := coreCodeAt arg

abbrev v1Config {H : Type} := v1ConfigAt (H := H) arg
abbrev limeConfig {H : Type} := limeConfigAt (H := H) arg
abbrev coreConfig {H : Type} := coreConfigAt (H := H) arg

end Silmaril.Wasm.Institution.Operational.MemoryQuery
