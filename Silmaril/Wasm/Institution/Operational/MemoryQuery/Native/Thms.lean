module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Core
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.V1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Transport

/-! Exact native successor and finite endpoint readback for memory32 queries.
The selected memory must resolve at module slot zero. The static offset is
unsigned 32-bit in all three renderings. Core uses the empty host and a memory
with address type i32. The alignment hint does not impose a runtime check. -/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

/-- Widening a legacy MemArg preserves its unsigned offset. Effective address
arithmetic stays in Nat, so it can go past the 32-bit address space. -/
theorem core_effective_address (address : BitVec 32) (immediate : Wasm.V1.MemArg) :
    Core.effAddr address.toNat immediate.toCore = address.toNat + immediate.offset.val := rfl

section V1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H} {s : Wasm.V1.Execution.Store H} {f : Frame}
variable {a : MemAddr} {m : MemInst}

theorem v1_sound_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query out : State} (edge : EdgeAt m.data immediate.offset.val query out) :
    Wasm.V1.Execution.Step host (v1ConfigAt immediate s f query) (v1ConfigAt immediate s f out) :=
  Proofs.V1.sound immediate lookup edge

theorem v1_sound (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query out : State} (edge : Edge m.data query out) :
    Wasm.V1.Execution.Step host (v1Config s f query) (v1Config s f out) :=
  v1_sound_at arg lookup edge

theorem v1_readback_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} (step : Wasm.V1.Execution.Step host (v1ConfigAt immediate s f query) target) :
    ∃ out, EdgeAt m.data immediate.offset.val query out ∧ target = v1ConfigAt immediate s f out := by
  obtain ⟨out, _, edge, eq⟩ := Proofs.V1.readback immediate step query (List.Sublist.refl _) lookup
  exact ⟨out, edge, eq⟩

theorem v1_readback (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} (step : Wasm.V1.Execution.Step host (v1Config s f query) target) :
    ∃ out, Edge m.data query out ∧ target = v1Config s f out :=
  v1_readback_at arg lookup step

theorem v1_step_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1ConfigAt immediate s f query) target ↔
      ∃ out, EdgeAt m.data immediate.offset.val query out ∧ target = v1ConfigAt immediate s f out :=
  ⟨v1_readback_at immediate lookup,
    fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound_at immediate lookup edge⟩

theorem v1_run_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1ConfigAt immediate s f query) target ↔
      ∃ out, Relation.ReflTransGen (EdgeAt m.data immediate.offset.val) query out ∧ target = v1ConfigAt immediate s f out :=
  Proofs.run_iff (v1ConfigAt immediate s f) _ _ immediate.offset.val (fun h => v1_sound_at immediate lookup h)
    (fun h => v1_readback_at immediate lookup h)

theorem v1_run_iff (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s f query) target ↔
      ∃ out, Relation.ReflTransGen (Edge m.data) query out ∧ target = v1Config s f out :=
  v1_run_iff_at arg lookup

end V1

section Lime1
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
variable {a : MemAddr} {m : MemInst}

theorem lime_sound_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query out : State} (edge : EdgeAt m.data immediate.offset.val query out) :
    Wasm.Lime1.Execution.Step host (limeConfigAt immediate s f query) (limeConfigAt immediate s f out) :=
  Proofs.Lime1.sound immediate lookup edge

theorem lime_sound (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query out : State} (edge : Edge m.data query out) :
    Wasm.Lime1.Execution.Step host (limeConfig s f query) (limeConfig s f out) :=
  lime_sound_at arg lookup edge

theorem lime_readback_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} (step : Wasm.Lime1.Execution.Step host (limeConfigAt immediate s f query) target) :
    ∃ out, EdgeAt m.data immediate.offset.val query out ∧ target = limeConfigAt immediate s f out := by
  obtain ⟨out, _, edge, eq⟩ := Proofs.Lime1.readback immediate step query (List.Sublist.refl _) lookup
  exact ⟨out, edge, eq⟩

theorem lime_readback (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} (step : Wasm.Lime1.Execution.Step host (limeConfig s f query) target) :
    ∃ out, Edge m.data query out ∧ target = limeConfig s f out :=
  lime_readback_at arg lookup step

theorem lime_step_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfigAt immediate s f query) target ↔
      ∃ out, EdgeAt m.data immediate.offset.val query out ∧ target = limeConfigAt immediate s f out :=
  ⟨lime_readback_at immediate lookup,
    fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound_at immediate lookup edge⟩

theorem lime_run_iff_at (immediate : Wasm.V1.MemArg) (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfigAt immediate s f query) target ↔
      ∃ out, Relation.ReflTransGen (EdgeAt m.data immediate.offset.val) query out ∧ target = limeConfigAt immediate s f out :=
  Proofs.run_iff (limeConfigAt immediate s f) _ _ immediate.offset.val (fun h => lime_sound_at immediate lookup h)
    (fun h => lime_readback_at immediate lookup h)

theorem lime_run_iff (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s f query) target ↔
      ∃ out, Relation.ReflTransGen (Edge m.data) query out ∧ target = limeConfig s f out :=
  lime_run_iff_at arg lookup

end Lime1

section Core
variable {H : Type} {P : Wasm.Numerics.Profile} {s : Core.Store H} {f : Core.Frame}
variable {a : Nat} {m : Core.MemInst}

theorem core_sound_at (immediate : Wasm.V1.MemArg) (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query out : State} (edge : EdgeAt m.bytes immediate.offset.val query out) :
    Core.Step P noHost (coreConfigAt immediate s f query) (coreConfigAt immediate s f out) :=
  Proofs.core_sound immediate lookup is32 edge

theorem core_sound (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query out : State} (edge : Edge m.bytes query out) :
    Core.Step P noHost (coreConfig s f query) (coreConfig s f out) :=
  core_sound_at arg lookup is32 edge

theorem core_readback_at (immediate : Wasm.V1.MemArg) (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} (step : Core.Step P noHost (coreConfigAt immediate s f query) target) :
    ∃ out, EdgeAt m.bytes immediate.offset.val query out ∧ target = coreConfigAt immediate s f out := Proofs.core_readback immediate lookup is32 step

theorem core_readback (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} (step : Core.Step P noHost (coreConfig s f query) target) :
    ∃ out, Edge m.bytes query out ∧ target = coreConfig s f out :=
  core_readback_at arg lookup is32 step

theorem core_step_iff_at (immediate : Wasm.V1.MemArg) (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} :
    Core.Step P noHost (coreConfigAt immediate s f query) target ↔
      ∃ out, EdgeAt m.bytes immediate.offset.val query out ∧ target = coreConfigAt immediate s f out :=
  ⟨core_readback_at immediate lookup is32,
    fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound_at immediate lookup is32 edge⟩

theorem core_run_iff_at (immediate : Wasm.V1.MemArg) (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfigAt immediate s f query) target ↔
      ∃ out, Relation.ReflTransGen (EdgeAt m.bytes immediate.offset.val) query out ∧ target = coreConfigAt immediate s f out :=
  Proofs.run_iff (coreConfigAt immediate s f) _ _ immediate.offset.val (fun h => core_sound_at immediate lookup is32 h)
    (fun h => core_readback_at immediate lookup is32 h)

theorem core_run_iff (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s f query) target ↔
      ∃ out, Relation.ReflTransGen (Edge m.bytes) query out ∧ target = coreConfig s f out :=
  core_run_iff_at arg lookup is32

end Core

theorem v1_to_lime_at {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.V1.Execution.Store H) (f : Frame) (query : State) :
    (v1ConfigAt immediate s f query).toLime =
      limeConfigAt immediate (s.mapCode Wasm.V1.Func.toLime) f query := by
  cases query <;> rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (query : State) :
    (v1Config s f query).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) f query :=
  v1_to_lime_at arg s f query

theorem lime_to_core_at {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.Lime1.Execution.Store H) (f : Frame) (query : State) :
    (limeConfigAt immediate s f query).toCore =
      coreConfigAt immediate s.toCore f.toCore query := by
  cases query <;> rfl

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (query : State) :
    (limeConfig s f query).toCore =
      coreConfig s.toCore f.toCore query :=
  lime_to_core_at arg s f query

theorem memory_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    s.toCore.mem? f.toCore index = some (a.value, m.toCore) :=
  Proofs.memory_toCore lookup

end Silmaril.Wasm.Institution.Operational.MemoryQuery
