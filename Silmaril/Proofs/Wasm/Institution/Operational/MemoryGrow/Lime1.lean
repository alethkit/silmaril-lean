module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Transport
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs.Lime1

open Execution
open Execution.Runtime
open Wasm.Lime1.Execution

private theorem set_current_memory {H : Type} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) : setMemory s a m = s := by
  simp [setMemory, set_current s.memories f lookup]

theorem sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) {q b : State} (edge : Edge m q b) :
    Step host (limeConfig s f a m q) (limeConfig s f a m b) := by
  cases invert edge with
  | grow delta bytes grown => exact .memoryGrow s f a m delta _ bytes lookup (.success bytes grown)
  | fail delta =>
    have step := Step.memoryGrow (host := host) s f a m delta (-1) m.data lookup .failure
    cases m
    simp only [set_current_memory lookup] at step
    exact step

private theorem pure_no_grow {types : List Wasm.Lime1.FuncType} {a b : List Admin} (h : PureStep types a b)
    (q : State) {H : Type} {s : Store H} {f : Frame} {address : MemAddr} {m : MemInst}
    (sub : List.Sublist a (limeConfig s f address m q).code) : False := by
  have check := sub.subset
  have len := sub.length_le
  cases h <;> cases q <;> simp [limeConfig, values] at check len

private theorem read {H : Type} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) (q : State) {address : MemAddr} {m : MemInst}
    (sub : List.Sublist a.code (limeConfig a.store a.frame address m q).code) :
    ∀ (_lookup : frameMemory a.store a.frame = some (address, m)),
      ∃ out, a.code = (limeConfig a.store a.frame address m q).code ∧ Edge m q out ∧
        b = limeConfig a.store a.frame address m out := by
  induction h generalizing q with
  | pure _ _ h => exact fun _ => (pure_no_grow h q sub).elim
  | @context s t f g before after h saved tail ih =>
    intro lookup
    have middle := (List.sublist_append_right (values saved) before).trans
      (List.sublist_append_left (values saved ++ before) tail)
    obtain ⟨out, exactCode, edge, target⟩ := ih q (middle.trans sub) lookup
    have len := sub.length_le
    change before = (limeConfig s f address m q).code at exactCode
    change (values saved ++ before ++ tail).length ≤ (limeConfig s f address m q).code.length at len
    simp [exactCode] at len
    have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved tail
    exact ⟨out, by simpa [values] using exactCode, edge, by simpa [values] using target⟩
  | memoryGrow s f a mem delta r bytes found grown =>
    intro lookup
    have opcode := sub.subset (List.Mem.tail _ (List.Mem.head _))
    cases q <;> simp [limeConfig] at opcode
    rename_i request
    have eq := sub.eq_of_length (by rfl)
    change [.source (.intConst .i32 delta), .source .memoryGrow] =
      ([.source (.intConst .i32 request), .source .memoryGrow] : List Admin) at eq
    have same := eq_of_heq (Wasm.Lime1.Instr.intConst.inj
      (AdminInstr.source.inj (List.cons.inj eq).1)).2
    subst request
    change frameMemory s f = _ at lookup
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    cases grown with
    | success _ grown => exact ⟨.grown bytes, rfl, fact (.grow delta bytes grown), rfl⟩
    | failure =>
      refine ⟨.failed, rfl, fact (.fail delta), ?_⟩
      cases m
      simp only [limeConfig, set_current_memory lookup]
      rfl
  | _ =>
    have check := sub.subset
    cases q <;> simp [limeConfig, values] at check

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (lookup : frameMemory s f = some (a, m))
    {q : State} {b : Config H} (step : Step host (limeConfig s f a m q) b) :
    ∃ out, Edge m q out ∧ b = limeConfig s f a m out := by
  cases q with
  | request delta =>
    obtain ⟨out, _, edge, eq⟩ := read step (.request delta) (List.Sublist.refl _) lookup
    exact ⟨out, edge, eq⟩
  | grown _ | failed =>
    obtain ⟨op, member, noValue⟩ := step.nonvalue
    simp [limeConfig] at member
    subst op
    cases noValue

end Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs.Lime1
