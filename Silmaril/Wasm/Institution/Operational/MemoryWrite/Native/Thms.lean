module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Core
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.V1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.V1Context
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Transport

/-! Exact native successors and finite endpoints for isolated full-width
Memory32 stores at module slot zero. The immediate has an unsigned 32-bit
offset. A bounds trap retains the input store and frame. Successful writes
preserve the size of the selected memory and leave all other memories intact. -/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

section V1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H} {s : Wasm.V1.Execution.Store H}
variable {f : Frame} {addr : MemAddr}
variable {mem : MemInst}

theorem v1_sound_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a b : State} (edge : EdgeAt mem.data immediate.offset.val a b) :
    Wasm.V1.Execution.Step host (v1ConfigAt immediate s f addr mem a) (v1ConfigAt immediate s f addr mem b) :=
  Proofs.V1.sound immediate lookup edge

theorem v1_sound (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a b : State} (edge : Edge mem.data a b) :
    Wasm.V1.Execution.Step host (v1Config s f addr mem a) (v1Config s f addr mem b) :=
  v1_sound_at MemoryQuery.arg lookup edge

theorem v1_step_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1ConfigAt immediate s f addr mem a) target ↔
      ∃ out, EdgeAt mem.data immediate.offset.val a out ∧ target = v1ConfigAt immediate s f addr mem out :=
  ⟨Proofs.V1.readback immediate lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound_at immediate lookup edge⟩

theorem v1_step_iff (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1Config s f addr mem a) target ↔
      ∃ out, Edge mem.data a out ∧ target = v1Config s f addr mem out :=
  v1_step_iff_at MemoryQuery.arg lookup

theorem v1_run_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.V1.Execution.Config H}
    (guard : Admitted mem.data a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1ConfigAt immediate s f addr mem a) target ↔
      ∃ out, RunsAt mem.data immediate.offset.val a out ∧ Admitted mem.data out ∧ target = v1ConfigAt immediate s f addr mem out :=
  Proofs.run_iff (v1ConfigAt immediate s f addr mem) _ _ immediate.offset.val (fun h => v1_sound_at immediate lookup h)
    (fun h => (v1_step_iff_at immediate lookup).mp h) guard

theorem v1_run_iff (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.V1.Execution.Config H}
    (guard : Admitted mem.data a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s f addr mem a) target ↔
      ∃ out, Runs mem.data a out ∧ Admitted mem.data out ∧ target = v1Config s f addr mem out :=
  v1_run_iff_at MemoryQuery.arg lookup guard

end V1

section V1Context

open Wasm.V1.Execution
open Execution.Runtime (Value)

/-- Reflect a leading full-width load in the current frame, retaining the value prefix and tail. -/
theorem v1_context_load_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {address : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ MemoryQuery.v1CodeAt immediate (.load address) ++ tail⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load address) out ∧
        dst = ⟨s, f, values saved ++ MemoryQuery.v1CodeAt immediate out ++ tail⟩ :=
  Proofs.V1Context.load_step_iff lookup

/-- Reflect a leading full-width store in the current frame, with the exact store update or trap. -/
theorem v1_context_store_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {address word : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ (v1ConfigAt immediate s f a m (.store address word)).code ++ tail⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store address word) out ∧
        let next := v1ConfigAt immediate s f a m out
        dst = ⟨next.store, next.frame, values saved ++ next.code ++ tail⟩ :=
  Proofs.V1Context.store_step_iff lookup

/-- An entered scalar function label and frame preserve both continuations on a load step. -/
theorem v1_activation_load_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {result : Option NumType} {callerSaved saved : List Value}
    {callerTail tail : List Admin} {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg}
    {address : BitVec 32} {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, v1ActivationCode result callee callerSaved callerTail
      (values saved ++ MemoryQuery.v1CodeAt immediate (.load address) ++ tail)⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load address) out ∧
        dst = ⟨s, caller, v1ActivationCode result callee callerSaved callerTail
          (values saved ++ MemoryQuery.v1CodeAt immediate out ++ tail)⟩ :=
  Proofs.V1Context.load_activation_iff lookup

/-- An entered scalar function reads its own slot zero. The selected memory update reaches the caller's shared store. -/
theorem v1_activation_store_step_iff_at {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {result : Option NumType} {callerSaved saved : List Value}
    {callerTail tail : List Admin} {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg}
    {address word : BitVec 32} {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, v1ActivationCode result callee callerSaved callerTail
      (values saved ++ (v1ConfigAt immediate s callee a m (.store address word)).code ++ tail)⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store address word) out ∧
        let next := v1ConfigAt immediate s callee a m out
        dst = ⟨next.store, caller, v1ActivationCode result next.frame callerSaved callerTail
          (values saved ++ next.code ++ tail)⟩ :=
  Proofs.V1Context.store_activation_iff lookup

/-- Every frame whose slot zero resolves to the written instance sees the new bytes. -/
theorem v1_frameMemory_setBytes {H : Type} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) (bytes : ByteArray) :
    frameMemory (setMemory s a { m with data := bytes }) f = some (a, { m with data := bytes }) :=
  Proofs.V1Context.frameMemory_setBytes lookup bytes

end V1Context

section Lime1
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H} {s : Wasm.Lime1.Execution.Store H}
variable {f : Frame} {addr : MemAddr}
variable {mem : MemInst}

theorem lime_sound_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a b : State} (edge : EdgeAt mem.data immediate.offset.val a b) :
    Wasm.Lime1.Execution.Step host (limeConfigAt immediate s f addr mem a) (limeConfigAt immediate s f addr mem b) :=
  Proofs.Lime1.sound immediate lookup edge

theorem lime_sound (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a b : State} (edge : Edge mem.data a b) :
    Wasm.Lime1.Execution.Step host (limeConfig s f addr mem a) (limeConfig s f addr mem b) :=
  lime_sound_at MemoryQuery.arg lookup edge

theorem lime_step_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfigAt immediate s f addr mem a) target ↔
      ∃ out, EdgeAt mem.data immediate.offset.val a out ∧ target = limeConfigAt immediate s f addr mem out :=
  ⟨Proofs.Lime1.readback immediate lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound_at immediate lookup edge⟩

theorem lime_step_iff (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfig s f addr mem a) target ↔
      ∃ out, Edge mem.data a out ∧ target = limeConfig s f addr mem out :=
  lime_step_iff_at MemoryQuery.arg lookup

theorem lime_run_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.Lime1.Execution.Config H}
    (guard : Admitted mem.data a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfigAt immediate s f addr mem a) target ↔
      ∃ out, RunsAt mem.data immediate.offset.val a out ∧ Admitted mem.data out ∧ target = limeConfigAt immediate s f addr mem out :=
  Proofs.run_iff (limeConfigAt immediate s f addr mem) _ _ immediate.offset.val (fun h => lime_sound_at immediate lookup h)
    (fun h => (lime_step_iff_at immediate lookup).mp h) guard

theorem lime_run_iff (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.Lime1.Execution.Config H}
    (guard : Admitted mem.data a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s f addr mem a) target ↔
      ∃ out, Runs mem.data a out ∧ Admitted mem.data out ∧ target = limeConfig s f addr mem out :=
  lime_run_iff_at MemoryQuery.arg lookup guard

end Lime1

section Core
variable {H : Type} {P : Wasm.Numerics.Profile} {s : Core.Store H}
variable {f : Core.Frame} {addr : Nat}
variable {mem : Core.MemInst}

theorem core_sound_at (immediate : Wasm.V1.MemArg) (lookup : CoreMemory32 s f addr mem) {a b : State} (edge : EdgeAt mem.bytes immediate.offset.val a b) :
    Core.Step P noHost (coreConfigAt immediate s f addr mem a) (coreConfigAt immediate s f addr mem b) :=
  Proofs.core_sound immediate lookup.1 edge

theorem core_sound (lookup : CoreMemory32 s f addr mem) {a b : State} (edge : Edge mem.bytes a b) :
    Core.Step P noHost (coreConfig s f addr mem a) (coreConfig s f addr mem b) :=
  core_sound_at MemoryQuery.arg lookup edge

theorem core_step_iff_at (immediate : Wasm.V1.MemArg) (lookup : CoreMemory32 s f addr mem) {a : State} {target : Core.Config H} :
    Core.Step P noHost (coreConfigAt immediate s f addr mem a) target ↔
      ∃ out, EdgeAt mem.bytes immediate.offset.val a out ∧ target = coreConfigAt immediate s f addr mem out :=
  ⟨Proofs.core_readback immediate lookup.1, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound_at immediate lookup edge⟩

theorem core_step_iff (lookup : CoreMemory32 s f addr mem) {a : State} {target : Core.Config H} :
    Core.Step P noHost (coreConfig s f addr mem a) target ↔
      ∃ out, Edge mem.bytes a out ∧ target = coreConfig s f addr mem out :=
  core_step_iff_at MemoryQuery.arg lookup

theorem core_run_iff_at (immediate : Wasm.V1.MemArg) (lookup : CoreMemory32 s f addr mem) {a : State} {target : Core.Config H}
    (guard : Admitted mem.bytes a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfigAt immediate s f addr mem a) target ↔
      ∃ out, RunsAt mem.bytes immediate.offset.val a out ∧ Admitted mem.bytes out ∧ target = coreConfigAt immediate s f addr mem out :=
  Proofs.run_iff (coreConfigAt immediate s f addr mem) _ _ immediate.offset.val (fun h => core_sound_at immediate lookup h)
    (fun h => (core_step_iff_at immediate lookup).mp h) guard

theorem core_run_iff (lookup : CoreMemory32 s f addr mem) {a : State} {target : Core.Config H}
    (guard : Admitted mem.bytes a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s f addr mem a) target ↔
      ∃ out, Runs mem.bytes a out ∧ Admitted mem.bytes out ∧ target = coreConfig s f addr mem out :=
  core_run_iff_at MemoryQuery.arg lookup guard

end Core

theorem v1_to_lime_at {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1ConfigAt immediate s f a m q).toLime = limeConfigAt immediate (s.mapCode Wasm.V1.Func.toLime) f a m q :=
  Proofs.v1_to_lime immediate s f a m q

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1Config s f a m q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f a m q :=
  v1_to_lime_at MemoryQuery.arg s f a m q

theorem memory32_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (h : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    CoreMemory32 s.toCore f.toCore a.value m.toCore :=
  Proofs.memory32_toCore h

theorem lime_to_core_at {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) {q : State} (guard : Admitted m.data q) :
    (limeConfigAt immediate s f a m q).toCore = coreConfigAt immediate s.toCore f.toCore a.value m.toCore q :=
  Proofs.lime_to_core immediate s f a m guard

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) {q : State} (guard : Admitted m.data q) :
    (limeConfig s f a m q).toCore = coreConfig s.toCore f.toCore a.value m.toCore q :=
  lime_to_core_at MemoryQuery.arg s f a m guard

end Silmaril.Wasm.Institution.Operational.MemoryWrite
