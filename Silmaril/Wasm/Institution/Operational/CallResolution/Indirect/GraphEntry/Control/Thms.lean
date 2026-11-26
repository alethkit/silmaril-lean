module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value}

theorem site_checked (ready : entry.Checked program tables outer index args) :
    entry.site.Checked program tables outer index args :=
  Proofs.site_checked ready

/-- A checked control prefix reaches the site or the first selected alternate. -/
theorem trace_exists (ready : entry.Checked program tables outer index args) :
    ∃ states endpoint, entry.Trace args states endpoint :=
  Proofs.trace_exists ready

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}

theorem core_front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states endpoint} (trace : entry.Trace args states endpoint) :
    (coreSource s outer index args :: entry.coreFront s outer args states ++
      [entry.coreEnd s outer args endpoint]).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.front_exact ready allocated trace

theorem core_alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states entered code} (trace : entry.Trace args states (.alternate entered code))
    (links : program.CoreLinksAllocated s) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ coreSource s outer index args :: entry.coreFront s outer args states ∨
      ∃ phase, program.FrameRuns entry.cont.address (entry.alternatePhase args entered code) phase ∧
        Graph.Admitted program entry.cont.owner phase ∧ dst = Graph.coreConfig s outer entry.cont.target phase :=
  Proofs.Core.alternate_run ready allocated trace links

theorem core_site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args path) ++ entry.site.coreSitePath s outer args active (.resolved call.address) states .operands ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.coreConfig call s outer phase :=
  Proofs.Core.site_run ready allocated control atSite tableAllocated targets links invoked

theorem core_lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ ((coreSource s outer index args :: entry.coreFront s outer args path) ++ entry.site.coreSitePath s outer args active out states .operands).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.coreTrapStart active out) phase ∧
        dst = entry.site.coreCleanup s outer active.caller phase :=
  Proofs.Core.lookup_trap ready allocated control atSite tableAllocated targets resolved trap

theorem core_operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args path) ++ entry.site.coreInside s outer args states .operands ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.coreEmit saved (entry.site.coreSiteCode rest)) phase ∧
        dst = entry.site.coreCleanup s outer (entry.site.frame args) phase :=
  Proofs.Core.operand_trap ready allocated control trace

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

theorem lime_front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states endpoint} (trace : entry.Trace args states endpoint) :
    (limeSource s outer index args :: entry.limeFront s outer args states ++
      [entry.limeEnd s outer args endpoint]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.front_exact ready allocated trace

theorem lime_alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states entered code} (trace : entry.Trace args states (.alternate entered code))
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ limeSource s outer index args :: entry.limeFront s outer args states ∨
      ∃ phase, program.FrameRuns entry.cont.address (entry.alternatePhase args entered code) phase ∧
        Graph.Admitted program entry.cont.owner phase ∧ dst = Graph.limeConfig s outer entry.cont.target phase :=
  Proofs.Lime1.alternate_run ready allocated trace links

theorem lime_site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args path) ++ entry.site.limeSitePath s outer args active (.resolved call.address) states .operands ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.limeConfig call s outer phase :=
  Proofs.Lime1.site_run ready allocated control atSite tableAllocated targets links invoked

theorem lime_lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ ((limeSource s outer index args :: entry.limeFront s outer args path) ++ entry.site.limeSitePath s outer args active out states .operands).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.limeTrapStart active) phase ∧
        dst = entry.site.limeCleanup s outer active.caller phase :=
  Proofs.Lime1.lookup_trap ready allocated control atSite tableAllocated targets resolved trap

theorem lime_operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args path) ++ entry.site.limeInside s outer args states .operands ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.limeEmit saved (entry.site.limeSiteCode rest)) phase ∧
        dst = entry.site.limeCleanup s outer (entry.site.frame args) phase :=
  Proofs.Lime1.operand_trap ready allocated control trace

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control
