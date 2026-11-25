module

import SqliteWasm.InitializerFlag

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open SqliteWasm

private def initialMemory : MemInst := ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0, 0, 0, 0]⟩⟩
private def flagBase : BitVec 32 := 0#32 - 59328#32
private def initial : Store Unit :=
  { mems := [initialMemory], globals := [⟨⟨.const, .i32⟩, .i32 flagBase⟩] }
private def frame : Frame := { module := { mems := [0], globals := [0, 0] } }

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial, frame, expression initializerFunction.body⟩
      ⟨initial.setMem 0 { initialMemory with bytes := ⟨#[1, 0, 0, 0]⟩ },
        frame, expression [.call ⟨1516⟩, .call ⟨23⟩]⟩ := by
  have run := initializerZeroFlag (P := P) (host := host) (s := initial) (f := frame)
    (base := flagBase) (globalAddr := 0) (memoryAddr := 0)
    (globalType := ⟨.const, .i32⟩) (mem := initialMemory)
    (by rfl) (by rfl) (by decide +kernel)
  have marked :
      Memory.writeSlice initialMemory.bytes (flagBase + 59328#32).toNat (Memory.encodeLE 4 1) =
        ⟨#[1, 0, 0, 0]⟩ := by decide +kernel
  rw [marked] at run
  exact run

private def markedMemory : MemInst := { initialMemory with bytes := ⟨#[1, 0, 0, 0]⟩ }
private def markedStore : Store Unit := initial.setMem 0 markedMemory

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨markedStore, frame, expression initializerFunction.body⟩
      ⟨markedStore, frame, [.trap]⟩ :=
  initializerNonzeroFlag (base := flagBase) (globalAddr := 0) (memoryAddr := 0)
    (globalType := ⟨.const, .i32⟩) (mem := markedMemory) (word := 1)
    (by rfl) (by rfl) (by decide +kernel) (by decide)

#print axioms originalInitializerFunction
#print axioms initializerZeroFlag
#print axioms initializerNonzeroFlag
