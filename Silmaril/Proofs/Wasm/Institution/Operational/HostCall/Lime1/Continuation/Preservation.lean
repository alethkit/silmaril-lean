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

private theorem contract_tail {op : Op H} (contract : Contract mem host (op :: ops)) : Contract mem host ops :=
  fun _ _ atSite => contract _ _ (List.mem_cons_of_mem _ atSite)

theorem live_step {a b : State H} (edge : Edge mem host active a b) (live : mem.Live a.bytes) : mem.Live b.bytes := by
  cases edge <;> assumption

theorem ready_step {a b : State H} (edge : Edge mem host active a b)
    (ready : Ready mem host active results a.phase) : Ready mem host active results b.phase := by
  cases edge with
  | get found =>
    obtain ⟨type, lookup, tail⟩ := checked_get ready.1
    rw [List.getElem?_map, found] at lookup
    cases lookup
    exact ⟨by simpa only [List.map_append, List.map_cons, List.map_nil] using tail, contract_tail ready.2⟩
  | drop =>
    obtain ⟨_, _, split, tail⟩ := checked_drop ready.1
    simp only [List.map_append, List.map_cons, List.map_nil] at split
    have same := (List.append_inj' split rfl).1
    exact ⟨same ▸ tail, contract_tail ready.2⟩
  | resolve typed =>
    obtain ⟨_, split, _, allocated, tail⟩ := checked_call ready.1
    simp only [List.map_append] at split
    rw [show _ = _ from typed] at split
    have same := List.append_cancel_right split
    exact ⟨allocated, typed, ready.2 _ _ (List.mem_cons_self ..), same ▸ tail, contract_tail ready.2⟩
  | returned _ typed _ =>
    refine ⟨?_, ready.2.2.2.2⟩
    simpa only [List.map_append, show _ = _ from typed] using ready.2.2.2.1
  | trapped | erase | labelTrap => trivial
  | diverged | frameDone => exact ready
  | labelResult => exact checked_nil ready.1

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
