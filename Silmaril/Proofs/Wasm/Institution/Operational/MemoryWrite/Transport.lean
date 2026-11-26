module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)

theorem v1_to_lime {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1ConfigAt immediate s f a m q).toLime = limeConfigAt immediate (s.mapCode Wasm.V1.Func.toLime) f a m q := by
  cases q with
  | store _ _ | trap => rfl
  | written out =>
    exact congrArg (fun store => (⟨store, f, []⟩ : Wasm.Lime1.Execution.Config H))
      (Wasm.V1.Execution.map_setMemory s a { m with data := out })

theorem memory32_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (h : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    CoreMemory32 s.toCore f.toCore a.value m.toCore :=
  ⟨MemoryQuery.memory_toCore h, rfl⟩

theorem lime_to_core {H : Type} (immediate : Wasm.V1.MemArg) (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) {q : State} (guard : Admitted m.data q) :
    (limeConfigAt immediate s f a m q).toCore = coreConfigAt immediate s.toCore f.toCore a.value m.toCore q := by
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

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) (mem : ByteArray) (offset : Nat)
    (sound : ∀ {a b}, EdgeAt mem offset a b → native (emit a) (emit b))
    (readback : ∀ {a b}, native (emit a) b → ∃ out, EdgeAt mem offset a out ∧ b = emit out)
    {a : State} {b : C} (guard : Admitted mem a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, RunsAt mem offset a out ∧ Admitted mem out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, guard, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, _, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback step
      exact ⟨out, path.tail edge, closed_at edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ h => sound h) _ _ path

end Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs
