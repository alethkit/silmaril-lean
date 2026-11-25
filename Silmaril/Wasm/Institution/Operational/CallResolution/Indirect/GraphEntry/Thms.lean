module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Cleanup
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Common

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value} {active : Source.Activation}

/-- A checked prefix can step to the lookup stack or trap before lookup. -/
theorem operand_trace_exists (ready : entry.Checked program tables outer index args) :
    ∃ states result, entry.OperandTrace args states result :=
  Proofs.operand_trace_exists ready

theorem prepare_exists (ready : entry.Checked program tables outer index args)
    {states : List OperandState} {stack : List Value}
    (trace : entry.OperandTrace args states (.values stack)) :
    ∃ active, entry.prepare program tables args stack = some active :=
  Proofs.prepare_exists ready trace

theorem resume_guard {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    {call : Context.Invocation} (invoked : active.invocation program = some call) :
    call.Checked program ∧ entry.cont.Checked program call.caller call.saved call.site.signature.results :=
  Proofs.resume_guard ready invoked

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}

/-- The ordinary call and invocation enter the allocated body. The checked
numeric trace leads into the exact lookup phases, with one native step per pair. -/
theorem core_prefix_exact {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.corePrefix s outer index args active out states).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.prefix_exact ready allocated resolved

/-- Finite native readback begins before entry and reaches through the
callee and the checked caller tail to the caller function's exit. -/
theorem core_run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ entry.corePrefix s outer index args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.coreConfig call s outer phase :=
  Proofs.Core.run_iff ready allocated invoked

/-- Failed lookup follows the same source entry. Cleanup retains the pending
Core lowering instructions until the native trap discards them. -/
theorem core_trap_run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (entry.corePrefix s outer index args active out states).dropLast ∨
      ∃ phase, CleanupRuns (entry.coreTrapStart active out) phase ∧ dst = entry.coreCleanup s outer active.caller phase :=
  Proofs.core_trap_run_iff ready allocated resolved trap

/-- The ordinary typed call and every prefix reduction each have their exact
native successor through the final numeric result or the first trap. -/
theorem core_operands_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    (entry.coreBefore s outer index args states ++ [entry.coreOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.operands_exact ready allocated trace

/-- A prefix trap uses only the entry function's native allocation. Its cleanup
starts with the remaining numeric instructions, indirect site, and caller tail. -/
theorem core_operand_trap_run_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states : List OperandState} {saved : List Value} {rest : List CallContinuation.OuterCall.Computed.Prefix.Op}
    (trace : entry.OperandTrace args states (.trap saved rest)) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ entry.coreBefore s outer index args states ∨
      ∃ phase, CleanupRuns (.label saved (entry.coreSiteCode rest)) phase ∧
        dst = entry.coreCleanup s outer (entry.frame args) phase :=
  Proofs.core_operand_trap_run_iff ready allocated trace

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

theorem lime_prefix_exact {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.limePrefix s outer index args active out states).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.prefix_exact ready allocated resolved

theorem lime_run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ entry.limePrefix s outer index args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.limeConfig call s outer phase :=
  Proofs.Lime1.run_iff ready allocated invoked

theorem lime_trap_run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (entry.limePrefix s outer index args active out states).dropLast ∨
      ∃ phase, CleanupRuns (entry.limeTrapStart active) phase ∧ dst = entry.limeCleanup s outer active.caller phase :=
  Proofs.lime_trap_run_iff ready allocated resolved trap

theorem lime_operands_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    (entry.limeBefore s outer index args states ++ [entry.limeOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.operands_exact ready allocated trace

theorem lime_operand_trap_run_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states : List OperandState} {saved : List Value} {rest : List CallContinuation.OuterCall.Computed.Prefix.Op}
    (trace : entry.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ entry.limeBefore s outer index args states ∨
      ∃ phase, CleanupRuns (.label saved (entry.limeSiteCode rest)) phase ∧
        dst = entry.limeCleanup s outer (entry.frame args) phase :=
  Proofs.lime_operand_trap_run_iff ready allocated trace

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
