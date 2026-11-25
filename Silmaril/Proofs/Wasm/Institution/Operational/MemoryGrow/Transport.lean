module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs

open Execution
open Execution.Runtime (Frame MemAddr MemInst)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1Config s f a m q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f a m q := by
  cases q with
  | request _ | failed => rfl
  | grown bytes =>
    exact congrArg (fun t => (⟨t, f, [.source (.intConst .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩ :
      Wasm.Lime1.Execution.Config H)) (Wasm.V1.Execution.map_setMemory s a { m with data := bytes })

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (limeConfig s f a m q).toCore = coreConfig s.toCore f.toCore a.value m q := by
  cases q with
  | request _ | failed => rfl
  | grown bytes =>
    have storeEq :
        (Wasm.Lime1.Execution.setMemory s a { m with data := bytes }).toCore =
          s.toCore.setMem a.value ({ m with data := bytes } : MemInst).toCore := by
      simp [Wasm.Lime1.Execution.setMemory, Core.Store.setMem, Runtime.Store.toCore, List.map_set]
    exact congrArg (fun t => (⟨t, f.toCore, [.plain (.intConst .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩ :
      Core.Config H)) storeEq

theorem grow_toCore {m : MemInst} (admitted : Admitted m) (delta : Nat) :
    m.toCore.grow? delta = (Memory.grow? m.data m.max delta).map
      (fun bytes => ({ m with data := bytes } : MemInst).toCore) := by
  have limit : (∀ j, m.toCore.type.limits.max = some j → Memory.size m.data + delta ≤ j.val) ↔
      (m.max.isNone ∨ Memory.size m.data + delta ≤ m.max.getD 0) := by
    cases hm : m.max with
    | none => simp [Runtime.MemInst.toCore, hm]
    | some max =>
      have fit : max < 18446744073709551616 := admitted.maxFits max hm
      simp [Runtime.MemInst.toCore, hm, Nat.mod_eq_of_lt fit]
  unfold Core.MemInst.grow? Memory.grow?
  change (if Memory.size m.data + delta ≤ Memory.maxPages ∧
    (∀ j, m.toCore.type.limits.max = some j → Memory.size m.data + delta ≤ j.val) then _ else _) = _
  simp only [limit, admitted.aligned, true_and]
  split
  · simp only [Option.map_some, Runtime.MemInst.toCore, ByteArray.size_append]
    change some (⟨⟨.i32, ⟨Fin.ofNat _ (Memory.size m.data + delta), _⟩⟩, _⟩ : Core.MemInst) =
      some ⟨⟨.i32, ⟨Fin.ofNat _ ((m.data.size + (Array.replicate
        (delta * Memory.pageSize) (0 : UInt8)).size) / Memory.pageSize), _⟩⟩, _⟩
    rw [Array.size_replicate, Nat.add_mul_div_right _ _ (by decide : 0 < Memory.pageSize)]
    rfl
  · rfl

theorem set_current (memories : List MemInst) (f : Frame) {a : MemAddr} {m : MemInst}
    (lookup : (do
      let address ← f.module.memories[0]?
      let memory ← memories[address.value]?
      pure (address, memory)) = some (a, m)) :
    memories.set a.value m = memories := by
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at lookup
  obtain ⟨address, _, found, atIndex, rfl, rfl⟩ := lookup
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp atIndex
  rw [← eq]
  exact List.set_getElem_self bound

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) {m : MemInst}
    (sound : ∀ {a b}, Edge m a b → native (emit a) (emit b))
    (readback : ∀ {a b}, native (emit a) b → ∃ out, Edge m a out ∧ b = emit out)
    {a : State} {b : C} :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs m a out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback step
      exact ⟨out, path.tail edge, rfl⟩
  · rintro ⟨out, path, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ e => sound e) _ _ path

end Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs
