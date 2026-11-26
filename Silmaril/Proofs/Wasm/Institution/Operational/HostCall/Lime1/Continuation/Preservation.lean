module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (Frame ModuleInst Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {active : Frame} {results types : List NumType} {ops : List (Op H)}
  {i : LocalIdx} {index : FuncIdx} {site : Site H}

theorem checked_nil (h : Checked base active.module (active.locals.map Value.type) results types ([] : List (Op H))) :
    types = results := by cases h; rfl

theorem checked_get (h : Checked base active.module (active.locals.map Value.type) results types (.get i :: ops)) :
    ∃ type, (active.locals.map Value.type)[i.toNat]? = some type ∧
      Checked base active.module (active.locals.map Value.type) results (types ++ [type]) ops := by
  cases h with
  | get found tail => exact ⟨_, found, tail⟩

theorem checked_drop (h : Checked base active.module (active.locals.map Value.type) results types (.drop :: ops)) :
    ∃ saved type, types = saved ++ [type] ∧
      Checked base active.module (active.locals.map Value.type) results saved ops := by
  cases h with
  | drop tail => exact ⟨_, _, rfl, tail⟩

theorem checked_call
    (h : Checked base active.module (active.locals.map Value.type) results types (.call index site :: ops)) :
    ∃ saved, types = saved ++ site.type.params ∧ active.module.funcs[index.toNat]? = some site.address ∧
      site.Allocated base ∧ Checked base active.module (active.locals.map Value.type) results
        (saved ++ site.type.results) ops := by
  cases h with
  | call resolved allocated tail => exact ⟨_, rfl, resolved, allocated, tail⟩

theorem checked_if {type : IfType} {left right : List (Op H)}
    (h : Checked base active.module (active.locals.map Value.type) results types (.if_ type left right :: ops)) :
    ∃ saved, types = (saved ++ type.signature.params) ++ [.int .i32] ∧ type.Resolved active.module ∧
      Checked base active.module (active.locals.map Value.type) type.signature.results type.signature.params left ∧
      Checked base active.module (active.locals.map Value.type) type.signature.results type.signature.params right ∧
      Checked base active.module (active.locals.map Value.type) results (saved ++ type.signature.results) ops := by
  cases h with
  | if_ resolved left right tail => exact ⟨_, rfl, resolved, left, right, tail⟩

private theorem contract_tail {op : Op H} (contract : Contract mem host (op :: ops)) : Contract mem host ops := by
  cases contract <;> assumption

private theorem contract_call (contract : Contract mem host (.call index site :: ops)) : site.Contract mem host := by
  cases contract with
  | call contract _ => exact contract

theorem live_step {a b : State H} (edge : Edge mem host active a b) (live : mem.Live a.bytes) : mem.Live b.bytes := by
  cases edge <;> assumption

theorem ready_step {a b : State H} (edge : Edge mem host active a b)
    (ready : Ready mem host active results a.phase a.labels) : Ready mem host active results b.phase b.labels := by
  cases edge with
  | get found =>
    obtain ⟨type, lookup, tail⟩ := checked_get ready.2.1
    rw [List.getElem?_map, found] at lookup
    cases lookup
    exact ⟨ready.1, by simpa only [List.map_append, List.map_cons, List.map_nil] using tail, contract_tail ready.2.2⟩
  | drop =>
    obtain ⟨_, _, split, tail⟩ := checked_drop ready.2.1
    simp only [List.map_append, List.map_cons, List.map_nil] at split
    have same := (List.append_inj' split rfl).1
    exact ⟨ready.1, same ▸ tail, contract_tail ready.2.2⟩
  | @if_ bytes saved args guard type left right ops labels typed =>
    obtain ⟨savedTypes, stackEq, resolved, leftChecked, rightChecked, tail⟩ := checked_if ready.2.1
    simp only [List.map_append, List.map_cons, List.map_nil, Value.int, typed] at stackEq
    have same := List.append_cancel_right (List.append_cancel_right stackEq)
    obtain ⟨labelReady, _, contract⟩ := ready
    cases contract with
    | if_ leftContract rightContract tailContract =>
      have tailChecked : Checked base active.module (active.locals.map Value.type) (labelResults results labels)
          (saved.map Value.type ++ type.signature.results) ops := same.symm ▸ tail
      have selected : Checked base active.module (active.locals.map Value.type) type.signature.results
          type.signature.params (select guard left right) ∧ Contract mem host (select guard left right) := by
        by_cases zero : guard = 0
        · rw [show select guard left right = right from ite_eq_left zero]
          exact ⟨rightChecked, rightContract⟩
        · rw [show select guard left right = left from ite_eq_right zero]
          exact ⟨leftChecked, leftContract⟩
      exact ⟨labelReady, resolved, typed, typed.symm ▸ selected.1, selected.2, tailChecked, tailContract⟩
  | block =>
    obtain ⟨labelsReady, _, _, armChecked, armContract, tailChecked, tailContract⟩ := ready
    exact ⟨.cons tailChecked tailContract labelsReady, armChecked, armContract⟩
  | resolve typed =>
    obtain ⟨_, split, _, allocated, tail⟩ := checked_call ready.2.1
    simp only [List.map_append] at split
    rw [show _ = _ from typed] at split
    have same := List.append_cancel_right split
    exact ⟨ready.1, allocated, typed, contract_call ready.2.2, same ▸ tail, contract_tail ready.2.2⟩
  | returned _ typed _ =>
    refine ⟨ready.1, ?_, ready.2.2.2.2.2⟩
    simpa only [List.map_append, show _ = _ from typed] using ready.2.2.2.2.1
  | trapped | erase => exact ⟨ready.1, trivial⟩
  | armResult =>
    have typed := checked_nil ready.2.1
    cases ready.1 with
    | cons tail contract outer =>
      exact ⟨outer, by simpa only [List.map_append, typed, labelResults] using tail, contract⟩
  | armTrap =>
    cases ready.1 with
    | cons _ _ outer => exact ⟨outer, trivial⟩
  | labelTrap => exact ⟨.nil, rfl, trivial⟩
  | diverged | frameDone => exact ready
  | labelResult => exact ⟨.nil, rfl, checked_nil ready.2.1⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
