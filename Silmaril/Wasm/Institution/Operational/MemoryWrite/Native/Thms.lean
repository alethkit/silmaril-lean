module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Core
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.V1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

section V1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H} {s : Wasm.V1.Execution.Store H}
variable {f : Frame} {addr : MemAddr}
variable {mem : MemInst}

theorem v1_sound (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a b : State} (edge : Edge mem.data a b) :
    Wasm.V1.Execution.Step host (v1Config s f addr mem a) (v1Config s f addr mem b) :=
  Proofs.V1.sound lookup edge

theorem v1_step_iff (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1Config s f addr mem a) target ↔
      ∃ out, Edge mem.data a out ∧ target = v1Config s f addr mem out :=
  ⟨Proofs.V1.readback lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound lookup edge⟩

theorem v1_run_iff (lookup : Wasm.V1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.V1.Execution.Config H}
    (guard : Admitted mem.data a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s f addr mem a) target ↔
      ∃ out, Runs mem.data a out ∧ Admitted mem.data out ∧ target = v1Config s f addr mem out :=
  Proofs.run_iff (v1Config s f addr mem) _ _ (fun h => v1_sound lookup h)
    (fun h => (v1_step_iff lookup).mp h) guard

end V1

section Lime1
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H} {s : Wasm.Lime1.Execution.Store H}
variable {f : Frame} {addr : MemAddr}
variable {mem : MemInst}

theorem lime_sound (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a b : State} (edge : Edge mem.data a b) :
    Wasm.Lime1.Execution.Step host (limeConfig s f addr mem a) (limeConfig s f addr mem b) :=
  Proofs.Lime1.sound lookup edge

theorem lime_step_iff (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfig s f addr mem a) target ↔
      ∃ out, Edge mem.data a out ∧ target = limeConfig s f addr mem out :=
  ⟨Proofs.Lime1.readback lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound lookup edge⟩

theorem lime_run_iff (lookup : Wasm.Lime1.Execution.frameMemory s f = some (addr, mem)) {a : State} {target : Wasm.Lime1.Execution.Config H}
    (guard : Admitted mem.data a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s f addr mem a) target ↔
      ∃ out, Runs mem.data a out ∧ Admitted mem.data out ∧ target = limeConfig s f addr mem out :=
  Proofs.run_iff (limeConfig s f addr mem) _ _ (fun h => lime_sound lookup h)
    (fun h => (lime_step_iff lookup).mp h) guard

end Lime1

section Core
variable {H : Type} {P : Wasm.Numerics.Profile} {s : Core.Store H}
variable {f : Core.Frame} {addr : Nat}
variable {mem : Core.MemInst}

theorem core_sound (lookup : CoreMemory32 s f addr mem) {a b : State} (edge : Edge mem.bytes a b) :
    Core.Step P noHost (coreConfig s f addr mem a) (coreConfig s f addr mem b) :=
  Proofs.core_sound lookup.1 edge

theorem core_step_iff (lookup : CoreMemory32 s f addr mem) {a : State} {target : Core.Config H} :
    Core.Step P noHost (coreConfig s f addr mem a) target ↔
      ∃ out, Edge mem.bytes a out ∧ target = coreConfig s f addr mem out :=
  ⟨Proofs.core_readback lookup.1, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound lookup edge⟩

theorem core_run_iff (lookup : CoreMemory32 s f addr mem) {a : State} {target : Core.Config H}
    (guard : Admitted mem.bytes a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s f addr mem a) target ↔
      ∃ out, Runs mem.bytes a out ∧ Admitted mem.bytes out ∧ target = coreConfig s f addr mem out :=
  Proofs.run_iff (coreConfig s f addr mem) _ _ (fun h => core_sound lookup h)
    (fun h => (core_step_iff lookup).mp h) guard

end Core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1Config s f a m q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f a m q :=
  Proofs.v1_to_lime s f a m q

theorem memory32_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (h : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    CoreMemory32 s.toCore f.toCore a.value m.toCore :=
  Proofs.memory32_toCore h

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) {q : State} (guard : Admitted m.data q) :
    (limeConfig s f a m q).toCore = coreConfig s.toCore f.toCore a.value m.toCore q :=
  Proofs.lime_to_core s f a m guard

end Silmaril.Wasm.Institution.Operational.MemoryWrite
