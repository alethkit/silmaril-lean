module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Source.Check
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Source.Nested

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Blocks.Context (Scope)
open Wasm.SingleThreaded.Det (noHost)

theorem prepare_spec {op : Op} {program : Graph.Program} {tables : Tables}
    {caller : Frame} {stack : List Value} {active : Activation}
    (prepared : op.prepare program tables caller stack = some active) :
    op.Prepared program tables caller stack active :=
  Proofs.prepare_spec prepared

theorem prepare_of_check {op : Op} {program : Graph.Program} {tables : Tables} {caller : Frame}
    {stack : List Value} {next : List NumType}
    (binding : (op.bind program tables caller.module).isSome = true)
    (typed : op.checkStack caller.module.types (Prefix.stackTypes stack) = some next) :
    ∃ active, op.prepare program tables caller stack = some active :=
  Proofs.prepare_of_check binding typed

theorem region_binding {body : Body} {program : Graph.Program} {tables : Tables}
    {fn : Graph.Function} {fallthrough : List NumType} {enclosing : Graph.EnclosingLabels} {stack : List NumType}
    (checked : body.checkRegion program tables fn fallthrough enclosing stack = true) :
    (body.operation.bind program tables fn.declaration.module).isSome = true :=
  Proofs.region_binding checked

/-- Preparation rules out checker failure. Resolution still admits the
three native lookup traps. -/
theorem resolve_total {active : Activation} {program : Graph.Program} {tables : Tables}
    (checked : active.Checked program tables) : ∃ out, active.resolve program = some out :=
  Indirect.resolve_total checked.site

theorem core_table {H : Type} {program : Graph.Program} {tables : Tables} {active : Activation}
    {s : Core.Store H} (checked : active.Checked program tables) (allocated : Tables.CoreAllocated tables s) :
    s.table? active.caller.toCore tableIndex =
      some (active.binding.address.value, active.binding.site.table.toCore) :=
  Proofs.core_table checked allocated

theorem lime_table {H : Type} {program : Graph.Program} {tables : Tables} {active : Activation}
    {s : Wasm.Lime1.Execution.Store H} (checked : active.Checked program tables)
    (allocated : Tables.LimeAllocated tables s) :
    Wasm.Lime1.Execution.frameTable s active.caller = some active.binding.site.table :=
  Proofs.lime_table checked allocated

theorem invocation_fields {active : Activation} {program : Graph.Program} {call : Context.Invocation}
    (invoked : active.invocation program = some call) :
    ∃ address callee, active.resolve program = some (.resolved address) ∧
      program.lookup address = some callee ∧
      call = ⟨active.binding.site, active.caller, active.operands.selector, active.operands.saved,
        active.operands.args, address, callee⟩ :=
  Proofs.invocation_fields invoked

theorem invocation_checked {active : Activation} {program : Graph.Program} {tables : Tables}
    {call : Context.Invocation} (checked : active.Checked program tables) (graph : program.checkDirect = true)
    (invoked : active.invocation program = some call) : call.Checked program :=
  Proofs.invocation_checked checked graph invoked

theorem invocation_core_table {H : Type} {active : Activation} {program : Graph.Program} {tables : Tables}
    {s : Core.Store H} {call : Context.Invocation} (checked : active.Checked program tables)
    (allocated : Tables.CoreAllocated tables s) (invoked : active.invocation program = some call) :
    s.table? call.caller.toCore tableIndex = some (active.binding.address.value, call.site.table.toCore) :=
  Proofs.invocation_core_table checked allocated invoked

theorem invocation_lime_table {H : Type} {active : Activation} {program : Graph.Program} {tables : Tables}
    {s : Wasm.Lime1.Execution.Store H} {call : Context.Invocation} (checked : active.Checked program tables)
    (allocated : Tables.LimeAllocated tables s) (invoked : active.invocation program = some call) :
    Wasm.Lime1.Execution.frameTable s call.caller = some call.site.table :=
  Proofs.invocation_lime_table checked allocated invoked

/-- The type effect of this source operator supplies the typed continuation
guard at the enclosing function label. -/
theorem resume_checked {op : Op} {program : Graph.Program} {tables : Tables} {caller : Frame}
    {stack : List Value} {active : Activation} {call : Context.Invocation} {cont : Context.Resume.Continuation}
    (prepared : op.Prepared program tables caller stack active) (invoked : active.invocation program = some call)
    (found : program.lookup cont.address = some cont.owner) (moduleEq : caller.module = cont.owner.declaration.module)
    (localsTyped : caller.locals.map Value.type = cont.owner.localTypes)
    (tail : op.checkTail cont.owner cont.owner.declaration.results [] (Prefix.stackTypes stack) cont.code = true) :
    cont.Checked program call.caller call.saved call.site.signature.results :=
  Proofs.resume_checked prepared invoked found moduleEq localsTyped tail

/-- Exact pending Core steps under already-entered scalar block labels.
Lookup ends at the first native trap or the pending successful invocation. -/
theorem core_resolution {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {active : Activation} {program : Graph.Program} {tables : Tables} {out : Outcome}
    (ready : active.Checked program tables) (allocated : program.CoreAllocated s)
    (tableAllocated : Tables.CoreAllocated tables s) (resolved : active.resolve program = some out)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step P noHost (active.coreConfig s scopes tail a) dst ↔ dst = active.coreConfig s scopes tail b) :=
  Proofs.core_resolution ready allocated tableAllocated resolved scopes tail

theorem core_entry {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {active : Activation} {program : Graph.Program} {tables : Tables} {call : Context.Invocation}
    (ready : active.Checked program tables) (allocated : program.CoreAllocated s)
    (invoked : active.invocation program = some call)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) (dst : Core.Config H) :
    Core.Step P noHost (active.coreConfig s scopes tail (.call (some call.address))) dst ↔
      dst = coreNest scopes (Indirect.coreEntered s call.caller call.callee call.saved call.args
        (tail.map Graph.coreEmit)) :=
  Proofs.core_entry ready allocated invoked scopes tail dst

open Wasm.Lime1.Execution in
theorem lime_resolution {H : Type} {s : Store H} {active : Activation} {program : Graph.Program}
    {tables : Tables} {out : Outcome}
    (ready : active.Checked program tables) (allocated : program.LimeAllocated s)
    (tableAllocated : Tables.LimeAllocated tables s) (resolved : active.resolve program = some out)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) (dst : Config H) :
    Step CallFrame.limeNoHost (active.limeSource s scopes tail) dst ↔ dst = active.limeResolved s scopes tail out :=
  Proofs.lime_resolution ready allocated tableAllocated resolved scopes tail dst

open Wasm.Lime1.Execution in
theorem lime_entry {H : Type} {s : Store H} {active : Activation} {program : Graph.Program}
    {tables : Tables} {call : Context.Invocation}
    (ready : active.Checked program tables) (allocated : program.LimeAllocated s)
    (invoked : active.invocation program = some call)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) (dst : Config H) :
    Step CallFrame.limeNoHost (active.limeResolved s scopes tail (.resolved call.address)) dst ↔
      dst = limeNest scopes (Indirect.limeEntered s call.caller call.callee call.saved call.args
        (tail.map Graph.limeEmit)) :=
  Proofs.lime_entry ready allocated invoked scopes tail dst

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source
