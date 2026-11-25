module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value} {active : Source.Activation}

theorem prepare_spec (ready : entry.Checked program tables outer index args active) :
    entry.op.Prepared program tables (entry.cont.owner.declaration.frame args) entry.cont.owner.initial active :=
  Source.prepare_spec (by simpa only [Entry.prepare, ite_eq_left ready.typed] using ready.prepared)

private theorem checked_body (checked : entry.check program tables = true) :
    (entry.op.bind program tables entry.cont.owner.declaration.module).isSome = true ∧
      entry.op.checkTail entry.cont.owner entry.cont.owner.declaration.results []
        (Prefix.stackTypes entry.cont.owner.initial) entry.cont.code = true := by
  have body := (Bool.and_eq_true_iff.mp checked).2
  exact Bool.and_eq_true_iff.mp body

theorem prepare_exists (checked : entry.check program tables = true) (args : List Value)
    (typed : args.map Value.type = entry.cont.owner.declaration.params) :
    ∃ active, entry.prepare program tables args = some active := by
  obtain ⟨binding, tail⟩ := checked_body checked
  cases stack : entry.op.checkStack entry.cont.owner.declaration.module.types
      (Prefix.stackTypes entry.cont.owner.initial) with
  | none => simp [Source.Op.checkTail, stack] at tail
  | some next =>
    simpa only [Entry.prepare, ite_eq_left typed] using
      (Source.prepare_of_check (caller := entry.cont.owner.declaration.frame args) binding stack)

theorem resume_guard (ready : entry.Checked program tables outer index args active)
    {call : Context.Invocation} (invoked : active.invocation program = some call) :
    call.Checked program ∧ entry.cont.Checked program call.caller call.saved call.site.signature.results := by
  have prepared := prepare_spec ready
  exact ⟨Source.invocation_checked prepared.checked (Bool.and_eq_true_iff.mp ready.source).1 invoked,
    Source.resume_checked prepared invoked ready.found rfl
      (by simp [Declaration.frame, Graph.Function.localTypes, Function.comp_def, Value.zero, ready.typed]) (checked_body ready.source).2⟩

theorem resolved_entry_ref {call : Context.Invocation} (invoked : active.invocation program = some call) :
    some call.address ∈ active.binding.site.table.refs ∧ program.lookup call.address = some call.callee ∧
      active.resolve program = some (.resolved call.address) := by
  obtain ⟨address, callee, resolved, found, rfl⟩ := Source.invocation_fields invoked
  refine ⟨?_, found, resolved⟩
  cases resolve_iff.mp resolved with
  | resolved entry _ _ => exact List.mem_of_getElem? entry

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs
