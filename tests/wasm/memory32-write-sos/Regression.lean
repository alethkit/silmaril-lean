module

import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.MemoryWrite
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Logic.Core (bytesAt Region)

private def original : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def changed : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def other : Runtime.MemInst := ⟨⟨#[7, 8]⟩, none⟩
private def mem : Runtime.MemInst := ⟨original, some 3⟩
private def addr : Runtime.MemAddr := ⟨1⟩
private def frame : Runtime.Frame := ⟨[.int .i64 9], { memories := [addr] }⟩
private def store : V1.Execution.Store Unit := { memories := [other, mem] }
private def host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private theorem found : V1.Execution.frameMemory store frame = some (addr, mem) := rfl
private theorem limeFound :
    Lime1.Execution.frameMemory (store.mapCode V1.Func.toLime) frame = some (addr, mem) :=
  (V1.Execution.map_frameMemory store frame).trans found

private theorem write : Edge original (.store 1 0x11223344) (.written changed) :=
  fact (.write 1 0x11223344 changed (by decide))

private theorem oob : Edge original (.store 3 0x11223344) .trap :=
  fact (.trap 3 0x11223344 (by decide))

example : Memory.load changed 1 4 = some 0x11223344 := read_after_write write
example : bytesAt changed ⟨5, 1⟩ = bytesAt original ⟨5, 1⟩ :=
  disjoint_bytes write (Or.inl (show (1 : Nat) + 4 ≤ 5 from by decide))

example : V1.Execution.Step host (v1Config store frame addr mem (.store 1 0x11223344))
    (v1Config store frame addr mem (.written changed)) :=
  v1_sound found write

example : (v1Config store frame addr mem (.written changed)).store.memories =
    [other, { mem with data := changed }] := rfl

example : Lime1.Execution.Step limeHost
    (v1Config store frame addr mem (.store 3 0x11223344)).toLime
    (v1Config store frame addr mem .trap).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact lime_sound limeFound oob

example : (v1Config store frame addr mem .trap).store = store := rfl

example : Core.Step Numerics.Profile.spec noHost
    (v1Config store frame addr mem (.store 1 0x11223344)).toLime.toCore
    (v1Config store frame addr mem (.written changed)).toLime.toCore := by
  rw [v1_to_lime, v1_to_lime,
    lime_to_core _ _ _ _ (show Admitted original (.store 1 0x11223344) from trivial),
    lime_to_core _ _ _ _ (closed write)]
  exact core_sound (memory32_toCore limeFound) write

example {target : Core.Config Unit}
    (h : Core.Steps Numerics.Profile.spec noHost
      (v1Config store frame addr mem (.store 1 0x11223344)).toLime.toCore target) :
    ∃ out, Runs original (.store 1 0x11223344) out ∧
      target = (v1Config store frame addr mem out).toLime.toCore ∧ target.frame = frame.toCore := by
  have ready : Admitted original (.store 1 0x11223344) := trivial
  rw [v1_to_lime, lime_to_core _ _ _ _ ready] at h
  obtain ⟨out, run, guard, eq⟩ := (core_run_iff (memory32_toCore limeFound) ready).mp h
  exact ⟨out, run, by rw [v1_to_lime, lime_to_core _ _ _ _ guard, eq],
    by rw [eq]; cases out <;> rfl⟩

section Offset

private def immediate : V1.MemArg := ⟨2, 2⟩
private def before : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 0, 0, 0, 0, 0xdd]⟩
private def after : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 0x44, 0x33, 0x22, 0x11, 0xdd]⟩
private def initial : Runtime.MemInst := ⟨before, some 3⟩
private def updated : Runtime.MemInst := { initial with data := after }
private def initialStore : V1.Execution.Store Unit := { memories := [other, initial] }
private def updatedStore := V1.Execution.setMemory initialStore addr updated
private def updatedLime := updatedStore.mapCode V1.Func.toLime
private def updatedCore := updatedLime.toCore

private theorem initialFound : V1.Execution.frameMemory initialStore frame = some (addr, initial) := rfl
private theorem updatedFound : V1.Execution.frameMemory updatedStore frame = some (addr, updated) := rfl
private theorem updatedLimeFound : Lime1.Execution.frameMemory updatedLime frame = some (addr, updated) := rfl
private theorem updatedCoreFound : CoreMemory32 updatedCore frame.toCore addr.value updated.toCore :=
  memory32_toCore updatedLimeFound

-- The alignment hint is 4 bytes. The four-byte access starts at byte 3.
private theorem offsetWrite : EdgeAt before 2 (.store 1 0x11223344) (.written after) :=
  fact_at (.write 1 _ after (by decide))

example : V1.Execution.Step host (v1ConfigAt immediate initialStore frame addr initial (.store 1 0x11223344))
    ⟨updatedStore, frame, []⟩ :=
  v1_sound_at immediate initialFound offsetWrite

example : updatedStore.memories = [other, updated] := rfl

example : Memory.load after 3 4 = some 0x11223344 := read_after_write_at offsetWrite

example : Memory.load after 1 4 = some 0x3344ccbb := by decide

private theorem offsetLoad : MemoryQuery.EdgeAt after 2 (.load 1) (.value 0x11223344) :=
  MemoryQuery.fact_at (.load 1 _ (read_after_write_at offsetWrite))

example : Lime1.Execution.Step limeHost (MemoryQuery.limeConfigAt immediate updatedLime frame (.load 1))
    ⟨updatedLime, frame, [.source (.intConst .i32 0x11223344)]⟩ :=
  MemoryQuery.lime_sound_at immediate updatedLimeFound offsetLoad

-- Native Core independently reads the same bytes. Reflect this step into SOS.
example : ∃ out, MemoryQuery.EdgeAt after 2 (.load 1) out ∧
    (⟨updatedCore, frame.toCore, [.plain (.intConst .i32 0x11223344)]⟩ : Core.Config Unit) =
      MemoryQuery.coreConfigAt immediate updatedCore frame.toCore out :=
  (MemoryQuery.core_step_iff_at (P := Numerics.Profile.spec) immediate updatedCoreFound.1 rfl).mp
    (.memory (.loadIntVal (t := .i32) (arg := immediate.toCore)
      (a := .i32) (i := 1) (c := 0x11223344) updatedCoreFound.1 (by decide)))

-- Both address computations use a natural sum. Byte 1 would have been in bounds.
example : Core.effAddr (0xffffffff : BitVec 32).toNat immediate.toCore = 4294967297 :=
  MemoryQuery.core_effective_address _ _

example : V1.Execution.Step host (MemoryQuery.v1ConfigAt immediate updatedStore frame (.load 0xffffffff))
    ⟨updatedStore, frame, [.trap]⟩ :=
  (MemoryQuery.v1_step_iff_at immediate updatedFound).mpr
    ⟨.trap, MemoryQuery.load_trap_iff_at.mpr (by decide), rfl⟩

-- The start is inside the buffer but the write would cross its end. The full
-- native trap target preserves both memories, including the successful write.
example : Core.Steps Numerics.Profile.spec noHost
    (coreConfigAt immediate updatedCore frame.toCore addr.value updated.toCore (.store 3 0))
    ⟨updatedCore, frame.toCore, [.trap]⟩ :=
  (core_run_iff_at immediate updatedCoreFound (a := .store 3 0) trivial).mpr
    ⟨.trap, .single (store_trap_iff_at.mpr (by decide)), trivial, rfl⟩

example : ∃ out, RunsAt after 2 (.store 3 0) out ∧ Admitted after out ∧
    (⟨updatedLime, frame, [.trap]⟩ : Lime1.Execution.Config Unit) =
      limeConfigAt immediate updatedLime frame addr updated out :=
  (lime_run_iff_at (host := limeHost) immediate updatedLimeFound (a := .store 3 0) trivial).mp
    (.single (.intStoreTrap _ _ _ _ _ _ _ addr updated rfl (by decide)))

example : ∃ out, RunsAt after 2 (.store 0xffffffff 0) out ∧ Admitted after out ∧
    (⟨updatedStore, frame, [.trap]⟩ : V1.Execution.Config Unit) =
      v1ConfigAt immediate updatedStore frame addr updated out :=
  (v1_run_iff_at (host := host) immediate updatedFound (a := .store 0xffffffff 0) trivial).mp
    (.single (.intStoreTrap _ _ _ _ _ _ _ addr updated rfl (by decide)))

section Activation

open V1.Execution (Step Steps values)

private def writerAddr : Runtime.FuncAddr := ⟨0⟩
private def writerModule : Runtime.ModuleInst := { memories := [addr] }
private def writerType : V1.FuncType := ⟨[], []⟩
private def writer : V1.Func :=
  ⟨⟨0⟩, [.int .i64], [.intConst .i32 1, .intConst .i32 0x11223344, .intStore .i32 none immediate]⟩
private def writerFrame : Runtime.Frame := ⟨[.int .i64 0], writerModule⟩
private def writerStore : V1.Execution.Store Unit :=
  { initialStore with funcs := [.wasm writerType writerModule writer] }
private def writtenStore := V1.Execution.setMemory writerStore addr updated
private def reader : Runtime.Frame := { frame with module := { frame.module with funcs := [writerAddr] } }
private def readerSaved : List Runtime.Value := [.int .i64 7, .int .i32 1]
private def readerTail : List V1.Execution.Admin := [.source (.intLoad .i32 none immediate)]
private def writerCode := v1ConfigAt immediate writerStore writerFrame addr initial (.store 1 0x11223344)

private theorem writerMemory : V1.Execution.frameMemory writerStore writerFrame = some (addr, initial) := rfl
private theorem readerMemory : V1.Execution.frameMemory writerStore reader = some (addr, initial) := rfl
private theorem afterWrite : V1.Execution.frameMemory writtenStore reader = some (addr, updated) :=
  v1_frameMemory_setBytes readerMemory after

private theorem activeWrite : Step host
    ⟨writerStore, reader, v1ActivationCode none writerFrame readerSaved readerTail writerCode.code⟩
    ⟨writtenStore, reader, v1ActivationCode none writerFrame readerSaved readerTail []⟩ :=
  (v1_activation_store_step_iff_at (immediate := immediate) (saved := []) (tail := []) writerMemory).mpr
    ⟨.written after, offsetWrite, rfl⟩

-- The ordinary invocation enters its own function label. The caller retains
-- its i64 operand beneath the address and observes the shared write after return.
example : Steps host
    ⟨writerStore, reader, values readerSaved ++ [.source (.call ⟨0⟩)] ++ readerTail⟩
    ⟨writtenStore, reader, values [.int .i64 7, .int .i32 0x11223344]⟩ := by
  apply Relation.ReflTransGen.head
    (b := ⟨writerStore, reader, values readerSaved ++ [.invoke writerAddr] ++ readerTail⟩)
    (Step.context (.call writerStore reader ⟨0⟩ writerAddr rfl) readerSaved readerTail)
  apply Relation.ReflTransGen.head
    (b := ⟨writerStore, reader, v1ActivationCode none writerFrame readerSaved readerTail writerCode.code⟩)
    (Step.context (.invokeWasm writerStore reader writerAddr writerType writerModule writer [] rfl rfl
      (by decide)) readerSaved readerTail)
  apply Relation.ReflTransGen.head activeWrite
  apply Relation.ReflTransGen.head
    (b := ⟨writtenStore, reader, values readerSaved ++ [.frame 0 writerFrame []] ++ readerTail⟩)
    (Step.context (.frame (.pure writtenStore writerFrame (.labelDone 0 [] [])) 0 reader) readerSaved readerTail)
  apply Relation.ReflTransGen.head
    (b := ⟨writtenStore, reader, values readerSaved ++ readerTail⟩)
    (Step.context (.pure writtenStore reader (.frameDone 0 writerFrame [] rfl)) readerSaved readerTail)
  exact .single ((v1_context_load_step_iff_at (immediate := immediate) (saved := [.int .i64 7])
    (tail := []) afterWrite).mpr ⟨.value 0x11223344, offsetLoad, rfl⟩)

example : writtenStore.funcs = writerStore.funcs ∧ writtenStore.memories = [other, updated] := ⟨rfl, rfl⟩

private def unallocatedCaller : Runtime.Frame := ⟨frame.locals, {}⟩

example : Step host
    ⟨writtenStore, unallocatedCaller, v1ActivationCode (some (.int .i32)) reader [] []
      (MemoryQuery.v1CodeAt immediate (.load 1))⟩
    ⟨writtenStore, unallocatedCaller, v1ActivationCode (some (.int .i32)) reader [] []
      (MemoryQuery.v1CodeAt immediate (.value 0x11223344))⟩ :=
  (v1_activation_load_step_iff_at (saved := []) (tail := []) afterWrite).mpr
    ⟨.value 0x11223344, offsetLoad, rfl⟩

private def calleeSaved : List Runtime.Value := [.int .i64 19]
private def calleeTail : List V1.Execution.Admin := [.source .nop]
private def failing := v1ConfigAt immediate writtenStore writerFrame addr updated (.store 3 0)
private def trappedCode : List V1.Execution.Admin := values calleeSaved ++ [.trap] ++ calleeTail
private theorem writerMemoryAfter : V1.Execution.frameMemory writtenStore writerFrame = some (addr, updated) :=
  v1_frameMemory_setBytes writerMemory after

-- The supplied bounds trap is native. The theorem reads it back while both
-- frames still retain their pending continuations.
private theorem boundsStep : Step host
    ⟨writtenStore, reader, v1ActivationCode none writerFrame readerSaved readerTail
      (values calleeSaved ++ failing.code ++ calleeTail)⟩
    ⟨writtenStore, reader, v1ActivationCode none writerFrame readerSaved readerTail trappedCode⟩ :=
  .context (.frame (.label (.context
    (.intStoreTrap writtenStore writerFrame .i32 none immediate 3 0 addr updated
      writerMemoryAfter (by decide)) calleeSaved calleeTail) 0 []) 0 reader) readerSaved readerTail

example : ∃ out, EdgeAt after 2 (.store 3 0) out ∧
    let next := v1ConfigAt immediate writtenStore writerFrame addr updated out
    (⟨writtenStore, reader, v1ActivationCode none writerFrame readerSaved readerTail trappedCode⟩ :
      V1.Execution.Config Unit) =
      ⟨next.store, reader, v1ActivationCode none next.frame readerSaved readerTail
        (values calleeSaved ++ next.code ++ calleeTail)⟩ :=
  (v1_activation_store_step_iff_at (immediate := immediate) (saved := calleeSaved)
    (tail := calleeTail) writerMemoryAfter).mp boundsStep

-- Native discard removes the callee suffix, then the label and frame. Only
-- then does it discard the caller's operands and skip its pending load.
example : Steps host
    ⟨writtenStore, reader, v1ActivationCode none writerFrame readerSaved readerTail
      (values calleeSaved ++ failing.code ++ calleeTail)⟩
    ⟨writtenStore, reader, [.trap]⟩ := by
  apply Relation.ReflTransGen.head boundsStep
  apply Relation.ReflTransGen.head
    (b := ⟨writtenStore, reader, v1ActivationCode none writerFrame readerSaved readerTail [.trap]⟩)
    (Step.context (.frame (.label (.pure writtenStore writerFrame (.trapValues (.int .i64 19) []
      calleeTail)) 0 []) 0 reader) readerSaved readerTail)
  apply Relation.ReflTransGen.head
    (b := ⟨writtenStore, reader, values readerSaved ++ [.frame 0 writerFrame [.trap]] ++ readerTail⟩)
    (Step.context (.frame (.pure writtenStore writerFrame (.labelTrap 0 [])) 0 reader) readerSaved readerTail)
  apply Relation.ReflTransGen.head
    (b := ⟨writtenStore, reader, values readerSaved ++ [.trap] ++ readerTail⟩)
    (Step.context (.pure writtenStore reader (.frameTrap 0 writerFrame)) readerSaved readerTail)
  exact .single (.pure writtenStore reader (.trapValues (.int .i64 7) [.int .i32 1] readerTail))

end Activation

end Offset
