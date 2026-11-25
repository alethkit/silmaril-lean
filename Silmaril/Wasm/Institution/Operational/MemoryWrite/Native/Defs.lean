module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (a : MemAddr) (m : MemInst) :
    State → Wasm.V1.Execution.Config H
  | .store address word => ⟨s, f, [.source (.intConst .i32 address), .source (.intConst .i32 word),
      .source (.intStore .i32 none MemoryQuery.arg)]⟩
  | .written bytes => ⟨Wasm.V1.Execution.setMemory s a { m with data := bytes }, f, []⟩
  | .trap => ⟨s, f, [.trap]⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (a : MemAddr) (m : MemInst) :
    State → Wasm.Lime1.Execution.Config H
  | .store address word => ⟨s, f, [.source (.intConst .i32 address), .source (.intConst .i32 word),
      .source (.intStore .i32 none MemoryQuery.arg)]⟩
  | .written bytes => ⟨Wasm.Lime1.Execution.setMemory s a { m with data := bytes }, f, []⟩
  | .trap => ⟨s, f, [.trap]⟩

def coreConfig {H : Type} (s : Core.Store H) (f : Core.Frame) (a : Nat) (m : Core.MemInst) :
    State → Core.Config H
  | .store address word => ⟨s, f, [.plain (.intConst .i32 address), .plain (.intConst .i32 word),
      .plain (.intStore .i32 none MemoryQuery.index MemoryQuery.arg.toCore)]⟩
  | .written bytes => ⟨s.setMem a { m with bytes := bytes }, f, []⟩
  | .trap => ⟨s, f, [.trap]⟩

/-- The allocated slot selected by the module's zero index has a 32-bit address type. -/
def CoreMemory32 {H : Type} (s : Core.Store H) (f : Core.Frame) (a : Nat) (m : Core.MemInst) : Prop :=
  s.mem? f MemoryQuery.index = some (a, m) ∧ m.type.address = .i32

end Silmaril.Wasm.Institution.Operational.MemoryWrite
