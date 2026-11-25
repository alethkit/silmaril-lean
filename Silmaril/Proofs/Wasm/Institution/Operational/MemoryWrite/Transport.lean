module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1Config s f a m q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f a m q := by
  cases q with
  | store _ _ | trap => rfl
  | written out =>
    exact congrArg (fun store => (⟨store, f, []⟩ : Wasm.Lime1.Execution.Config H))
      (Wasm.V1.Execution.map_setMemory s a { m with data := out })

theorem memory32_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (h : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    CoreMemory32 s.toCore f.toCore a.value m.toCore :=
  ⟨MemoryQuery.memory_toCore h, rfl⟩

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) {q : State} (guard : Admitted m.data q) :
    (limeConfig s f a m q).toCore = coreConfig s.toCore f.toCore a.value m.toCore q := by
  cases q with
  | store _ _ | trap => rfl
  | written out =>
    have sameSize : out.size = m.data.size := guard
    have mem : ({ m with data := out } : MemInst).toCore = { m.toCore with bytes := out } := by
      simp [Runtime.MemInst.toCore, sameSize]
    have storeEq :
        (Wasm.Lime1.Execution.setMemory s a { m with data := out }).toCore =
          s.toCore.setMem a.value { m.toCore with bytes := out } := by
      simp [Wasm.Lime1.Execution.setMemory, Core.Store.setMem, Runtime.Store.toCore, List.map_set, mem]
    exact congrArg (fun store => (⟨store, f.toCore, []⟩ : Core.Config H)) storeEq

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) (mem : ByteArray)
    (sound : ∀ {a b}, Edge mem a b → native (emit a) (emit b))
    (readback : ∀ {a b}, native (emit a) b → ∃ out, Edge mem a out ∧ b = emit out)
    {a : State} {b : C} (guard : Admitted mem a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs mem a out ∧ Admitted mem out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, guard, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, _, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback step
      exact ⟨out, path.tail edge, closed edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ h => sound h) _ _ path

end Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs
