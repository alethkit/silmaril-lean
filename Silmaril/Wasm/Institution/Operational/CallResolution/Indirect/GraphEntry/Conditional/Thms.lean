module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value} {value : BitVec 32}

theorem site_checked (ready : entry.Checked program tables outer index args) :
    entry.site.Checked program tables outer index args :=
  Proofs.site_checked ready

theorem condition_exists (ready : entry.Checked program tables outer index args) :
    ∃ value, entry.Condition args value :=
  Proofs.condition_exists ready

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}

theorem core_front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance) (read : entry.Condition args value) :
    (coreSource s outer index args :: entry.coreFront s outer args value ++
      [entry.coreSelected s outer args value]).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.front_exact ready allocated read

theorem core_alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value) (select : entry.choosesSite value = false)
    (links : program.CoreLinksAllocated s) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ coreSource s outer index args :: entry.coreFront s outer args value ∨
      ∃ phase, program.FrameRuns entry.site.cont.address (entry.alternatePhase args) phase ∧
        Graph.Admitted program entry.site.cont.owner phase ∧
        dst = Graph.coreConfig s outer entry.site.cont.target phase :=
  Proofs.Core.alternate_run ready allocated read select links

theorem core_site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args value) ++ entry.site.coreSitePath s outer args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.coreConfig call s outer phase :=
  Proofs.Core.site_run ready allocated read select atSite tableAllocated targets links invoked

theorem core_lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ ((coreSource s outer index args :: entry.coreFront s outer args value) ++ entry.site.coreSitePath s outer args active out states).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.coreTrapStart active out) phase ∧
        dst = entry.site.coreCleanup s outer active.caller phase :=
  Proofs.Core.lookup_trap ready allocated read select atSite tableAllocated targets resolved trap

theorem core_operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Core.Config H} :
    Core.Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args value) ++ entry.site.coreInside s outer args states ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.coreEmit saved (entry.site.coreSiteCode rest)) phase ∧
        dst = entry.site.coreCleanup s outer (entry.site.frame args) phase :=
  Proofs.Core.operand_trap ready allocated read select trace

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

theorem lime_front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance) (read : entry.Condition args value) :
    (limeSource s outer index args :: entry.limeFront s outer args value ++
      [entry.limeSelected s outer args value]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.front_exact ready allocated read

theorem lime_alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value) (select : entry.choosesSite value = false)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ limeSource s outer index args :: entry.limeFront s outer args value ∨
      ∃ phase, program.FrameRuns entry.site.cont.address (entry.alternatePhase args) phase ∧
        Graph.Admitted program entry.site.cont.owner phase ∧
        dst = Graph.limeConfig s outer entry.site.cont.target phase :=
  Proofs.Lime1.alternate_run ready allocated read select links

theorem lime_site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args value) ++ entry.site.limeSitePath s outer args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.limeConfig call s outer phase :=
  Proofs.Lime1.site_run ready allocated read select atSite tableAllocated targets links invoked

theorem lime_lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ ((limeSource s outer index args :: entry.limeFront s outer args value) ++ entry.site.limeSitePath s outer args active out states).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.limeTrapStart active) phase ∧
        dst = entry.site.limeCleanup s outer active.caller phase :=
  Proofs.Lime1.lookup_trap ready allocated read select atSite tableAllocated targets resolved trap

theorem lime_operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args value) ++ entry.site.limeInside s outer args states ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.limeEmit saved (entry.site.limeSiteCode rest)) phase ∧
        dst = entry.site.limeCleanup s outer (entry.site.frame args) phase :=
  Proofs.Lime1.operand_trap ready allocated read select trace

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional
