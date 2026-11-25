module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {H : Type} {s : Store H} {entry : Entry} {program : Graph.Program} {tables : Source.Tables}
  {outer : Frame} {index : FuncIdx} {args : List Value} {active : Source.Activation}

private theorem code (entry : Entry) :
    expression entry.limeFunc.body = values entry.cont.owner.initial ++
      .source entry.op.limeInstr :: entry.cont.code.map Graph.limeEmit := by
  let fn := entry.cont.owner
  have literals := Graph.lime_body_expression { fn with code := [] }
  have tail := Graph.lime_body_expression { fn with initial := [], code := entry.cont.code }
  change expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++ []) = values fn.initial ++ [] at literals
  change expression ([] ++ Graph.Op.emitList Graph.limeCodeSyntax entry.cont.code) = [] ++ entry.cont.code.map Graph.limeEmit at tail
  change expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++
    entry.op.limeInstr :: Graph.Op.emitList Graph.limeCodeSyntax entry.cont.code) = _
  simp only [List.append_nil] at literals
  simp only [List.nil_append] at tail
  simp only [expression, List.map_append, List.map_cons] at literals tail ⊢
  rw [literals, tail]

private theorem entry_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s) {dst : Config H} :
    Step CallFrame.limeNoHost (entry.limeInvoke s outer args) dst ↔
      dst = entry.cont.limeWrap outer (active.limeSource s [] entry.cont.code) := by
  have prepare := prepare_spec ready
  have count : args.length = entry.cont.owner.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length ready.typed)
  have enter := CallFrame.lime_invoke_wasm_exact (caller := outer) (dst := dst) allocated.entry count
  change Step CallFrame.limeNoHost (entry.limeInvoke s outer args) dst ↔
    dst = ⟨s, outer, [.frame entry.cont.owner.declaration.results.length (entry.cont.owner.declaration.frame args)
      [.label entry.cont.owner.declaration.results.length [] (expression entry.limeFunc.body)]]⟩ at enter
  rw [code, ← prepare.caller_eq, prepare.stack_eq] at enter
  simpa only [Context.Resume.Continuation.limeWrap, Source.Activation.limeSource, Source.limeNest, List.foldr_nil,
    Indirect.limeSource, Source.Op.limeInstr, ← prepare.typeIndex_eq, values_append, values,
    List.map_singleton, List.append_assoc, List.singleton_append, value, Value.int] using enter

theorem prefix_exact (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.limePrefix s outer index args active out).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have data := (prepare_spec ready).checked
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr
    ⟨?_, List.isChain_cons_cons.mpr ⟨?_, .singleton _⟩⟩⟩
  · intro dst
    exact Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) ready.resolves
  · intro dst
    exact entry_iff ready allocated
  · intro dst
    exact Context.Resume.lime_resolution_allocated_iff data.site allocated.targets
      (Source.lime_table data allocated.tables) resolved

theorem run_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (GraphEntry.limeSource s outer index args) dst ↔
      dst ∈ entry.limePrefix s outer index args active (.resolved call.address) ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.limeConfig call s outer phase := by
  obtain ⟨callChecked, continuation⟩ := resume_guard ready invoked
  obtain ⟨member, found, resolved⟩ := resolved_entry_ref invoked
  let before := entry.limePrefix s outer index args active (.resolved call.address)
  let entered := entry.cont.limeConfig call s outer (.callee call.entered)
  have steps := prefix_exact ready allocated resolved
  have enter : ∀ dst, Step CallFrame.limeNoHost
      (entry.cont.limeWrap outer (active.limeResolved s [] entry.cont.code (.resolved call.address))) dst ↔
      dst = entered := by
    obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
    exact fun _ => Context.Resume.lime_entry_iff callChecked (allocated.targets address callee member found)
  have chain : (before ++ [entered]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    steps.append (.singleton entered) (by
      intro a aLast b bFirst
      change a ∈ some (entry.cont.limeWrap outer (active.limeResolved s [] entry.cont.code (.resolved call.address))) at aLast
      change b ∈ some entered at bFirst
      obtain rfl := Option.mem_some.mp aLast
      obtain rfl := Option.mem_some.mp bFirst
      exact enter)
  exact (Context.Resume.prefix_run_iff (dst := dst) before entered chain).trans
    (or_congr Iff.rfl (Context.Resume.lime_entered_run_iff callChecked allocated.links continuation))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Lime1
