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

theorem prepare_exists (checked : entry.check program tables = true) (args : List Value)
    (typed : args.map Value.type = entry.cont.owner.declaration.params) :
    ∃ active, entry.prepare program tables args = some active :=
  Proofs.prepare_exists checked args typed

theorem resume_guard (ready : entry.Checked program tables outer index args active)
    {call : Context.Invocation} (invoked : active.invocation program = some call) :
    call.Checked program ∧ entry.cont.Checked program call.caller call.saved call.site.signature.results :=
  Proofs.resume_guard ready invoked

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}

/-- The ordinary call and invocation enter the allocated body before the
exact indirect lookup trace begins. Each adjacent pair is one native step. -/
theorem core_prefix_exact (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.corePrefix s outer index args active out).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.prefix_exact ready allocated resolved

/-- Finite native readback begins before entry and reaches through the
callee and the checked caller tail to the caller function's exit. -/
theorem core_run_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ entry.corePrefix s outer index args active (.resolved call.address) ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.coreConfig call s outer phase :=
  Proofs.Core.run_iff ready allocated invoked

/-- Failed lookup follows the same source entry. Cleanup retains the pending
Core lowering instructions until the native trap discards them. -/
theorem core_trap_run_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (entry.corePrefix s outer index args active out).dropLast ∨
      ∃ phase, CleanupRuns (entry.coreTrapStart active out) phase ∧ dst = entry.coreCleanup s outer active.caller phase :=
  Proofs.core_trap_run_iff ready allocated resolved trap

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

theorem lime_prefix_exact (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.limePrefix s outer index args active out).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.prefix_exact ready allocated resolved

theorem lime_run_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ entry.limePrefix s outer index args active (.resolved call.address) ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.limeConfig call s outer phase :=
  Proofs.Lime1.run_iff ready allocated invoked

theorem lime_trap_run_iff (ready : entry.Checked program tables outer index args active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (entry.limePrefix s outer index args active out).dropLast ∨
      ∃ phase, CleanupRuns (entry.limeTrapStart active) phase ∧ dst = entry.limeCleanup s outer active.caller phase :=
  Proofs.lime_trap_run_iff ready allocated resolved trap

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
