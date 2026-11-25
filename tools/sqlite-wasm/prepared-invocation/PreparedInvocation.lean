module

public import SqliteWasm.DirectPreparation
public import SqliteWasm.InitializerStartup
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 65536
set_option maxHeartbeats 700000

private theorem mappedMemoryEntry {H : Type} {s : Store H} {frame : Frame}
    {address : Nat} {mem : MemInst}
    (found : s.mem? frame ⟨0⟩ = some (address, mem)) :
    frame.module.mems[0]? = some address ∧ s.mems[address]? = some mem := by
  change (frame.module.mems[0]?.bind fun a => s.mems[a]?.bind fun m => some (a, m)) =
    some (address, mem) at found
  obtain ⟨a, slot, lookup⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨m, entry, equality⟩ := Option.bind_eq_some_iff.mp lookup
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equality)
  exact ⟨slot, entry⟩

private theorem markingPreservesSource (mem : MemInst) (fits : 59332 ≤ mem.bytes.size) :
    Memory.load (initializerMark mem 0).bytes 59892 4 = Memory.load mem.bytes 59892 4 := by
  have write : Memory.writeBytes mem.bytes 59328 (Memory.encodeLE 4 1) =
      some (initializerMark mem 0).bytes := by
    unfold Memory.writeBytes
    rw [Memory.encodeLE_size, ite_eq_left fits]
    rfl
  have read := Memory.readBytes_writeBytes_disjoint _ _ _ 59328 59892 4 write
    (Or.inr (by simp only [Memory.encodeLE_size]; decide))
  unfold Memory.load
  rw [read]

/-- The canonical typed fixture produces a direct-preparation result whose resolved
export has a successful argument-free invocation and the specified memory update. -/
theorem reactorPreparedInvocation (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func 25⟩ ∧
      runtime.mem? frame ⟨0⟩ = some (memoryAddress, mem) ∧
      InvokeOk runtime 25 [] ∧
      Steps P host (invoke runtime 25 [])
        ⟨runtime.setMem memoryAddress (threadSetupMemory (initializerMark mem 0) 0), {}, []⟩ := by
  obtain ⟨before, allocated, runtime, frame, mem, prepared, alloc,
    sameFunctions, slot, global, mapped, size, flag, source⟩ := reactorDirectPreparation
  obtain ⟨memorySlot, memoryEntry⟩ := mappedMemoryEntry mapped
  have base : runtime.global? { module := frame.module } ⟨1⟩ =
      some (before.globals.length + 1, ⟨⟨.const, .i32⟩, .i32 0⟩) := global
  have zero : Memory.load mem.bytes (initializerAddress 0) 4 = some 0 := flag
  have bound : 59984 ≤ mem.bytes.size := by omega
  obtain ⟨address, word, exported, addrSlot, invokable, loaded, _, invoked⟩ :=
    initializerReturnsAfterAllocation (P := P) (host := host)
      alloc (by rfl) sameFunctions memorySlot memoryEntry base zero bound
  have sameAddress : address = 25 := Option.some.inj (addrSlot.symm.trans slot)
  have marked := (markingPreservesSource mem (by omega)).trans source
  have sameWord : word = 0 := Option.some.inj (loaded.symm.trans marked)
  subst address
  subst word
  exact ⟨runtime, frame, mem, before.mems.length, prepared, exported, mapped, invokable, invoked⟩

#print axioms reactorPreparedInvocation

end SqliteWasm
