module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value}

theorem site_body (entry : Entry) :
    entry.site.body = .block entry.result entry.inside.body entry.tail := by
  have same (blocks : List Context.Resume.Block) : entry.site.region blocks = entry.inside.region blocks := by
    induction blocks with
    | nil => rfl
    | cons block rest ih =>
      exact congrArg (fun body => Source.Body.block block.result body block.tail) ih
  change Source.Body.block entry.result (entry.site.region entry.inside.cont.blocks) entry.tail = _
  rw [same]
  rfl

theorem site_checked (ready : entry.Checked program tables outer index args) :
    entry.site.Checked program tables outer index args :=
  ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready.source).1).1,
    ready.found, ready.resolves, ready.typed⟩

private theorem locals_typed (ready : entry.Checked program tables outer index args) :
    (entry.site.frame args).locals.map Value.type = entry.site.cont.owner.localTypes := by
  simp [GraphEntry.Entry.frame, Declaration.frame, Graph.Function.localTypes, Function.comp_def, Value.zero, ready.typed]

theorem condition_exists (ready : entry.Checked program tables outer index args) :
    ∃ value, entry.Condition args value := by
  have typed : entry.site.cont.owner.localTypes[entry.condition.toNat]? = some (.int .i32) :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready.source).1).2
  rw [← locals_typed ready, List.getElem?_map] at typed
  cases read : (entry.site.frame args).locals[entry.condition.toNat]? with
  | none => simp [read] at typed
  | some cell =>
    have ty : cell.type = .int .i32 := by simpa [read] using typed
    cases cell with
    | mk t bits =>
      change t = .int .i32 at ty
      subst t
      exact ⟨bits, read⟩

theorem alternate_admitted (ready : entry.Checked program tables outer index args) :
    Graph.Admitted program entry.site.cont.owner (entry.alternatePhase args) :=
  .running (locals_typed ready) (Bool.and_eq_true_iff.mp ready.source).2

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Proofs
