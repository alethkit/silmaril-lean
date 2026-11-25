module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs.V1

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

theorem sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) {q out : State} (edge : Edge m.data q out) :
    Step host (v1Config s f a m q) (v1Config s f a m out) := by
  cases invert edge with
  | write addr word out stored =>
    apply Step.intStore s f .i32 none MemoryQuery.arg addr word a m out lookup
    simpa [storeInt, effectiveAddress, MemoryQuery.arg, IntType.width, BitVec.setWidth_eq] using stored
  | trap addr word oob =>
    apply Step.intStoreTrap s f .i32 none MemoryQuery.arg addr word a m lookup
    simpa [storeInt, effectiveAddress, MemoryQuery.arg, IntType.width, BitVec.setWidth_eq] using
      (store_none_iff (word := word)).mpr oob

private theorem pure_no_store {a b : List Admin} (h : PureStep a b) (q : State)
    {H : Type} {s : Store H} {f : Frame} {addr : MemAddr} {m : MemInst}
    (sub : List.Sublist a (v1Config s f addr m q).code) : False := by
  have check := sub.subset
  have len := sub.length_le
  cases h <;> cases q <;> simp [v1Config, values] at check len

private theorem read {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) (q : State) {addr : MemAddr} {mem : MemInst}
    (sub : List.Sublist a.code (v1Config a.store a.frame addr mem q).code) :
    ∀ (_lookup : frameMemory a.store a.frame = some (addr, mem)),
      ∃ out, a.code = (v1Config a.store a.frame addr mem q).code ∧ Edge mem.data q out ∧
        b = v1Config a.store a.frame addr mem out := by
  induction h generalizing q with
  | pure s f h => exact fun _ => (pure_no_store h q sub).elim
  | @context s t f g before after h saved tail ih =>
    intro lookup
    have middle := (List.sublist_append_right (values saved) before).trans
      (List.sublist_append_left (values saved ++ before) tail)
    obtain ⟨out, exactCode, edge, target⟩ := ih q (middle.trans sub) lookup
    have len := sub.length_le
    change before = (v1Config s f addr mem q).code at exactCode
    change (values saved ++ before ++ tail).length ≤ (v1Config s f addr mem q).code.length at len
    simp [exactCode] at len
    have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved
    subst tail
    exact ⟨out, by simpa [values] using exactCode, edge, by simpa [values] using target⟩
  | intStore s f t packed arg i word a m out found stored =>
    intro lookup
    have opcode := sub.subset (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    cases q <;> simp [v1Config] at opcode
    rename_i queryAddress queryWord
    obtain ⟨rfl, rfl, rfl⟩ := opcode
    have same : List.Sublist
        ([.source (.intConst .i32 i), .source (.intConst .i32 word), .source (.intStore .i32 none MemoryQuery.arg)] : List Admin)
        [.source (.intConst .i32 queryAddress), .source (.intConst .i32 queryWord),
          .source (.intStore .i32 none MemoryQuery.arg)] := sub
    have eq := same.eq_of_length rfl
    simp only [List.cons.injEq, AdminInstr.source.injEq, and_true] at eq
    have iEq := eq_of_heq (Wasm.V1.Instr.intConst.inj eq.1).2
    have wordEq := eq_of_heq (Wasm.V1.Instr.intConst.inj eq.2).2
    subst i
    subst word
    change frameMemory s f = _ at lookup
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    refine ⟨.written out, rfl, fact (.write queryAddress queryWord out ?_), rfl⟩
    simpa [storeInt, effectiveAddress, MemoryQuery.arg, IntType.width, BitVec.setWidth_eq] using stored
  | intStoreTrap s f t packed arg i word a m found stored =>
    intro lookup
    have opcode := sub.subset (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    cases q <;> simp [v1Config] at opcode
    rename_i queryAddress queryWord
    obtain ⟨rfl, rfl, rfl⟩ := opcode
    have same : List.Sublist
        ([.source (.intConst .i32 i), .source (.intConst .i32 word), .source (.intStore .i32 none MemoryQuery.arg)] : List Admin)
        [.source (.intConst .i32 queryAddress), .source (.intConst .i32 queryWord),
          .source (.intStore .i32 none MemoryQuery.arg)] := sub
    have eq := same.eq_of_length rfl
    simp only [List.cons.injEq, AdminInstr.source.injEq, and_true] at eq
    have iEq := eq_of_heq (Wasm.V1.Instr.intConst.inj eq.1).2
    have wordEq := eq_of_heq (Wasm.V1.Instr.intConst.inj eq.2).2
    subst i
    subst word
    change frameMemory s f = _ at lookup
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    refine ⟨.trap, rfl, fact (.trap queryAddress queryWord ((store_none_iff (word := queryWord)).mp ?_)), rfl⟩
    simpa [storeInt, effectiveAddress, MemoryQuery.arg, IntType.width, BitVec.setWidth_eq] using stored
  | _ =>
    have check := sub.subset
    cases q <;> simp [v1Config, values] at check

private theorem nonempty {H : Type} {host : HostSemantics H} {a b : Config H}
    (step : Step host a b) : a.code ≠ [] := by
  induction step with
  | pure _ _ h => cases h <;> simp [values]
  | context _ _ _ ih =>
    intro eq
    exact ih ((List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp eq).1).2)
  | _ => simp

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {addr : MemAddr} {mem : MemInst} (lookup : frameMemory s f = some (addr, mem))
    {q : State} {b : Config H} (step : Step host (v1Config s f addr mem q) b) :
    ∃ out, Edge mem.data q out ∧ b = v1Config s f addr mem out := by
  cases q with
  | written bytes => exact (nonempty step rfl).elim
  | store i word =>
    obtain ⟨out, _, edge, eq⟩ := read step (.store i word) (List.Sublist.refl _) lookup
    exact ⟨out, edge, eq⟩
  | trap =>
    obtain ⟨out, _, edge, eq⟩ := read step .trap (List.Sublist.refl _) lookup
    exact ⟨out, edge, eq⟩

end Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs.V1
