module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow

open Execution
open Execution.Runtime (Frame MemAddr MemInst)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (a : MemAddr) (m : MemInst) :
    State → Wasm.V1.Execution.Config H
  | .request delta => ⟨s, f, [.source (.intConst .i32 delta), .source .memoryGrow]⟩
  | .grown bytes => ⟨Wasm.V1.Execution.setMemory s a { m with data := bytes }, f,
      [.source (.intConst .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩
  | .failed => ⟨s, f, [.source (.intConst .i32 (-1))]⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (a : MemAddr)
    (m : MemInst) : State → Wasm.Lime1.Execution.Config H
  | .request delta => ⟨s, f, [.source (.intConst .i32 delta), .source .memoryGrow]⟩
  | .grown bytes => ⟨Wasm.Lime1.Execution.setMemory s a { m with data := bytes }, f,
      [.source (.intConst .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩
  | .failed => ⟨s, f, [.source (.intConst .i32 (-1))]⟩

def coreConfig {H : Type} (s : Core.Store H) (f : Core.Frame) (a : Nat) (m : MemInst) :
    State → Core.Config H
  | .request delta => ⟨s, f, [.plain (.intConst .i32 delta), .plain (.memoryGrow MemoryQuery.index)]⟩
  | .grown bytes => ⟨s.setMem a ({ m with data := bytes } : MemInst).toCore, f,
      [.plain (.intConst .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩
  | .failed => ⟨s, f, [.plain (.intConst .i32 (-1))]⟩

end Silmaril.Wasm.Institution.Operational.MemoryGrow
