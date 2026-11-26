module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs.V1

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime

theorem sound (immediate : Wasm.V1.MemArg) {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (memory : frameMemory s f = some (a, m)) {query out : State}
    (edge : EdgeAt m.data immediate.offset.val query out) : Step host ⟨s, f, v1CodeAt immediate query⟩ ⟨s, f, v1CodeAt immediate out⟩ := by
  cases invert_at edge with
  | size => exact .memorySize s f a m memory
  | load addr bits read =>
    apply Step.intLoad s f .i32 none immediate addr a m (.int .i32 bits) memory
    simp [loadInt, effectiveAddress, IntType.width, read, BitVec.setWidth_eq]
  | loadTrap addr bound =>
    apply Step.intLoadTrap s f .i32 none immediate addr a m memory
    simp [loadInt, effectiveAddress, IntType.width, (load_none_iff_at (offset := immediate.offset.val) |>.mpr bound)]

private theorem pure_no_query (immediate : Wasm.V1.MemArg) {a b : List Admin} (h : PureStep a b) (q : State)
    (sub : List.Sublist a (v1CodeAt immediate q)) : False := by
  have checked := sub.subset
  have len := sub.length_le
  cases h <;> cases q <;> simp [v1CodeAt, values] at checked len

theorem readback (immediate : Wasm.V1.MemArg) {H : Type} {host : HostSemantics H} {src dst : Config H}
    (step : Step host src dst) (query : State) (sub : List.Sublist src.code (v1CodeAt immediate query))
    {addr : MemAddr} {mem : MemInst} (lookup : frameMemory src.store src.frame = some (addr, mem)) :
    ∃ out, src.code = v1CodeAt immediate query ∧ EdgeAt mem.data immediate.offset.val query out ∧
      dst = ⟨src.store, src.frame, v1CodeAt immediate out⟩ := by
  induction step generalizing query with
  | pure s f h => exact (pure_no_query immediate h query sub).elim
  | @context s s' f f' before after step saved tail ih =>
    have middle := (List.sublist_append_right (values saved) before).trans
      (List.sublist_append_left (values saved ++ before) tail)
    obtain ⟨out, exactCode, edge, target⟩ := ih query (middle.trans sub) lookup
    have len := sub.length_le
    change (values saved ++ before ++ tail).length ≤ (v1CodeAt immediate query).length at len
    change before = v1CodeAt immediate query at exactCode
    simp [exactCode, values] at len
    have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved
    subst tail
    exact ⟨out, by simpa [values] using exactCode, edge, by simpa [values] using target⟩
  | memorySize s f address m found =>
    have checked := sub.subset (List.Mem.head _)
    cases query <;> simp [v1CodeAt] at checked
    change frameMemory s f = _ at lookup
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    exact ⟨.value _, rfl, fact_at .size, rfl⟩
  | intLoad s f t packed offset i address m v found read =>
    have op := sub.subset (List.Mem.tail _ (List.Mem.head _))
    have operand := sub.subset (List.Mem.head _)
    cases query <;> simp [v1CodeAt] at op
    rename_i queryAddress
    obtain ⟨rfl, rfl, sameImmediate⟩ := op
    subst offset
    simp [v1CodeAt, value, Value.int] at operand
    have same : i = queryAddress := eq_of_heq (Wasm.V1.Instr.intConst.inj operand).2
    subst i
    change frameMemory s f = _ at lookup
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    simp [loadInt, effectiveAddress, IntType.width, BitVec.setWidth_eq] at read
    obtain ⟨bits, hread, rfl⟩ := read
    exact ⟨.value bits, rfl, fact_at (.load _ _ hread), rfl⟩
  | intLoadTrap s f t packed offset i address m found read =>
    have op := sub.subset (List.Mem.tail _ (List.Mem.head _))
    have operand := sub.subset (List.Mem.head _)
    cases query <;> simp [v1CodeAt] at op
    rename_i queryAddress
    obtain ⟨rfl, rfl, sameImmediate⟩ := op
    subst offset
    simp [v1CodeAt, value, Value.int] at operand
    have same : i = queryAddress := eq_of_heq (Wasm.V1.Instr.intConst.inj operand).2
    subst i
    change frameMemory s f = _ at lookup
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    have failed : Wasm.Execution.Memory.load mem.data (queryAddress.toNat + immediate.offset.val) 4 = none := by
      simpa [loadInt, effectiveAddress, IntType.width] using read
    exact ⟨.trap, rfl, fact_at (.loadTrap _ (load_none_iff_at.mp failed)), rfl⟩
  | _ =>
    have checked := sub.subset
    cases query <;> simp [v1CodeAt, values] at checked

end Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs.V1
