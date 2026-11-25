module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H}
  {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Runtime.Frame}
  {index : FuncIdx} {args : List Value} {active : Source.Activation}

private theorem code (entry : Entry) :
    expression entry.coreFunc.body = coreValues entry.cont.owner.initial ++
      .plain entry.op.coreInstr :: entry.cont.code.map Graph.coreEmit := by
  let fn := entry.cont.owner
  have values := Graph.core_body_expression { fn with code := [] }
  have tail := Graph.core_body_expression { fn with initial := [], code := entry.cont.code }
  change expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++ []) = coreValues fn.initial ++ [] at values
  change expression ([] ++ Graph.Op.emitList Graph.coreCodeSyntax entry.cont.code) = [] ++ entry.cont.code.map Graph.coreEmit at tail
  change expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++
    entry.op.coreInstr :: Graph.Op.emitList Graph.coreCodeSyntax entry.cont.code) = _
  simp only [List.append_nil] at values
  simp only [List.nil_append] at tail
  simp only [expression, List.map_append, List.map_cons] at values tail ⊢
  rw [values, tail]

private theorem entry_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s) {dst : Config H} :
    Step P noHost (entry.coreInvoke s outer args) dst ↔ dst = entry.coreLookup s outer active .start := by
  have prepare := prepare_spec ready
  have enter := Sequence.wasm_entry_iff (P := P) (caller := outer) (dst := dst) allocated.entry ready.typed
  have frame := Sequence.core_frame_forCall entry.cont.owner.declaration.module args entry.cont.owner.declaration.locals
  change Core.Frame.forCall entry.cont.owner.declaration.module.toCore (args.map Value.toCore) entry.coreFunc.locals =
    (entry.cont.owner.declaration.frame args).toCore at frame
  rw [frame, code, ← prepare.caller_eq, prepare.stack_eq] at enter
  have selector : vals [(Value.int .i32 active.operands.selector).toCore] =
      [constI32 active.operands.selector] := rfl
  simpa only [Entry.coreInvoke, Entry.coreInstance, Declaration.type, Entry.coreLookup, Context.Resume.Continuation.coreWrap,
    Source.Activation.coreConfig, Source.coreNest, List.foldr_nil, Indirect.coreConfig, Site.coreCode,
    coreValues, Source.Op.coreInstr, ← prepare.typeIndex_eq, List.map_append, List.map_singleton,
    vals_append, selector, List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
    List.singleton_append] using enter


theorem prefix_exact (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.corePrefix s outer index args active out).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have data := (prepare_spec ready).checked
  have lookup := Context.Resume.core_resolution_allocated_exact (P := P) (cont := entry.cont) (outer := outer)
    (stack := active.operands.saved ++ active.operands.args) data.site allocated.targets
    (Source.core_table data allocated.tables) resolved
  have chain := (List.isChain_map (R := fun a b : Config H => ∀ dst, Step P noHost a dst ↔ dst = b)
    (entry.coreLookup s outer active)).mpr lookup
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_, chain⟩⟩
  · intro dst
    exact Computed.core_direct_call_iff (s := s) (P := P) (stack := args) (tail := [])
      ready.resolves allocated.entry
  · intro dst
    exact entry_iff ready allocated

theorem run_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ entry.corePrefix s outer index args active (.resolved call.address) ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.coreConfig call s outer phase := by
  obtain ⟨callChecked, continuation⟩ := resume_guard ready invoked
  obtain ⟨member, found, resolved⟩ := resolved_entry_ref invoked
  let before := entry.corePrefix s outer index args active (.resolved call.address)
  let entered := entry.cont.coreConfig call s outer (.callee call.entered)
  have steps := prefix_exact (P := P) ready allocated resolved
  have enter : ∀ dst, Step P noHost (entry.coreLookup s outer active (.call (some call.address))) dst ↔
      dst = entered := by
    obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
    exact fun _ => Context.Resume.core_entry_iff callChecked (allocated.targets address callee member found)
  have chain : (before ++ [entered]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
    steps.append (.singleton entered) (by
      intro a aLast b bFirst
      change a ∈ some (entry.coreLookup s outer active (.call (some call.address))) at aLast
      change b ∈ some entered at bFirst
      obtain rfl := Option.mem_some.mp aLast
      obtain rfl := Option.mem_some.mp bFirst
      exact enter)
  exact (Context.Resume.prefix_run_iff (dst := dst) before entered chain).trans
    (or_congr Iff.rfl (Context.Resume.core_entered_run_iff callChecked allocated.links continuation))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Core
