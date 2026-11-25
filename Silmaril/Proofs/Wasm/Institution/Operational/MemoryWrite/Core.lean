module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

theorem core_sound {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    (lookup : s.mem? f MemoryQuery.index = some (a, m)) {q out : State} (edge : Edge m.bytes q out) :
    Step P noHost (coreConfig s f a m q) (coreConfig s f a m out) := by
  cases invert edge with
  | write address word out stored =>
    have hp : Memory.store m.bytes (effAddr address.toNat MemoryQuery.arg.toCore)
        (count := IntType.i32.width / 8) (BitVec.setWidth _ word) = some out := by
      change Memory.store m.bytes address.toNat (count := 4) (word.setWidth 32) = some out
      rw [BitVec.setWidth_eq]
      exact stored
    exact .memory (.storeIntVal (a := .i32) (i := address) lookup hp)
  | trap address word oob =>
    exact .memory (.storeIntOob (a := .i32) (i := address) lookup oob)

private theorem write_head {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    {input : List Admin} {dst : Config H}
    (step : MemoryStep P ⟨s, f, input⟩ dst) {address word : BitVec 32}
    (support : List.Sublist input (coreConfig s f a m (.store address word)).code)
    (lookup : s.mem? f MemoryQuery.index = some (a, m)) :
    ∃ out, input = (coreConfig s f a m (.store address word)).code ∧
      Edge m.bytes (.store address word) out ∧ dst = coreConfig s f a m out := by
  cases step with
  | @storeIntVal _ _ t x arg w i bits index mem out found stored =>
    have op := support.subset (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    simp [coreConfig] at op
    obtain ⟨rfl, rfl, rfl⟩ := op
    have code := support.eq_of_length rfl
    simp only [coreConfig, List.cons.injEq, Admin.plain.injEq, and_true] at code
    cases w
    case i64 => cases (Instr.intConst.inj code.1).1
    have first : i = address := eq_of_heq (Instr.intConst.inj code.1).2
    have second : bits = word := eq_of_heq (Instr.intConst.inj code.2).2
    subst i
    subst bits
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    change Memory.store m.bytes address.toNat (count := 4) (word.setWidth 32) = some out at stored
    rw [BitVec.setWidth_eq] at stored
    exact ⟨.written out, rfl, fact (.write address word out stored), rfl⟩
  | @storeIntOob _ _ t x arg w i bits index mem found bound =>
    have op := support.subset (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    simp [coreConfig] at op
    obtain ⟨rfl, rfl, rfl⟩ := op
    have code := support.eq_of_length rfl
    simp only [coreConfig, List.cons.injEq, Admin.plain.injEq, and_true] at code
    cases w
    case i64 => cases (Instr.intConst.inj code.1).1
    have first : i = address := eq_of_heq (Instr.intConst.inj code.1).2
    have second : bits = word := eq_of_heq (Instr.intConst.inj code.2).2
    subst i
    subst bits
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    exact ⟨.trap, rfl, fact (.trap address word bound), rfl⟩
  | _ =>
    have check := support.subset
    simp [coreConfig] at check

theorem core_readback {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    (lookup : s.mem? f MemoryQuery.index = some (a, m)) {q : State} {dst : Config H}
    (step : Step P noHost (coreConfig s f a m q) dst) :
    ∃ out, Edge m.bytes q out ∧ dst = coreConfig s f a m out := by
  cases q with
  | written bytes => exact (not_step_vals (W := []) step).elim
  | trap => exact (not_step_trap step).elim
  | store address word =>
    let op := Admin.plain (.intStore .i32 none MemoryQuery.index MemoryQuery.arg.toCore)
    let values : List Val := [.i32 address, .i32 word]
    change Step P noHost ⟨s, f, vals values ++ [op]⟩ dst at step
    rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
    · obtain ⟨saved, args, first, tail, next, fnvEq, code, headStep, rfl⟩ := fnv_headDec head
      change fnv (vals values ++ [op]) = _ at fnvEq
      simp [fnv_cons_of_none (a := op) rfl] at fnvEq
      obtain ⟨_, rfl, rfl⟩ := fnvEq
      have family := headStep.fam_inv (by change Fam.memory ≠ .control; decide)
      change vals values ++ [op] = vals saved ++ (vals args ++ [op]) at code
      have support : List.Sublist (vals args ++ [op]) (vals values ++ [op]) := by
        rw [code]
        exact List.sublist_append_right _ _
      obtain ⟨out, redex, edge, rfl⟩ := write_head family support lookup
      change vals args ++ [op] = vals values ++ [op] at redex
      rw [redex] at code
      have len := congrArg List.length code
      simp only [List.length_append, vals, List.length_map] at len
      have empty : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst saved
      exact ⟨out, edge, by simp [vals]⟩
    · obtain ⟨_, _, _, _, _, ⟨bad, _, _⟩ | ⟨_, bad, _, _⟩⟩ := fnv_bubble bubble <;>
        change fnv (vals values ++ [op]) = _ at bad <;>
        simp [fnv_cons_of_none (a := op) rfl, op] at bad

end Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs
