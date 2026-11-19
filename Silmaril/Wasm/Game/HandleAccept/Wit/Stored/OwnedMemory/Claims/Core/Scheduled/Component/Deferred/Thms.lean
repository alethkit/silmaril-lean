module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Thms
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Deferred

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- With no deferred callees, every run has the original eager dispatch, including
imports using the proposed control name. This equality also preserves trap labels. -/
theorem dispatch_no_deferred (bindings : List (Binding sig)) (callees : List (Callee sig))
    (control : String) (ready : HostReady (HostState sig)) :
    specDispatch ready (hostWithDeferred (grow := grow) bindings callees [] control) =
      specDispatch ready (hostWithComponent (grow := grow) bindings callees) := rfl

/-- A capacity refusal records the current ticket without queuing, lifting payloads,
or publishing. The original continuation receives the reference cancel token. -/
theorem table_full_steps {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (config : Config (core3 grow) (HostState sig)) (thread : Option Runtime.ThreadId)
    (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (pending : config.ctl = ⟨thread, .prog (refuseTableFull ticket), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (.refused ticket .subtaskTableFull)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.table_full_steps
    config thread segments rest ticket pending

/-- At the reference allocation boundary, fullness traps and locks down the reached
store, leaving the host journal (including the recorded refusal) untouched. -/
theorem reference_table_full_steps {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (config : Config (core3 grow) (HostState sig)) (thread : Option Runtime.ThreadId)
    (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (inst : InstId) (subtask : SubtaskId)
    (instance_ : InstState) (live : config.store.inst? inst = some instance_)
    (full : instance_.addHandle? (.waitable (.subtask subtask)) = none)
    (next : Nat → Session grow sig (Ret (core3 grow)))
    (pending : config.ctl = ⟨thread, .prog (handlesAddSubtask inst subtask >>= next), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .tableFull] (StepDefs.trapCfg config) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.reference_table_full_steps
    config thread segments rest inst subtask instance_ live full next pending

/-- Recycling a waitable slot for another nominal subtask cannot authorize the former
callback. The actual start import also reselects against the live table. -/
theorem recycled_slot (entry : PendingAccept) (store : CStore (core3 grow)) (index : Nat)
    (replacement : SubtaskId) (fresh : replacement ≠ entry.subtask)
    (slot : (store.inst? entry.inst).bind (·.handles.get? index) = some (.waitable (.subtask replacement))) :
    linked entry store index = false := by
  simp [linked, slot, fresh]

/-- Staging does not lift payloads or change authority. A later `canonLower` step, not
this host callback, installs the reference waitable entry. -/
theorem stage_frame (callee : Callee sig) (caller : CallerId) (ticket : Nat) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (stage callee caller ticket subtask cx args pos ft limits results) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.stage_frame
    callee caller ticket subtask cx args pos ft limits results before

/-- The pending-cancel callback does not move any owner, endpoint or error context.
Waitable state and delivery are left to the reference cancellation path. -/
theorem cancel_frame (token : Nat) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (cancel (grow := grow) (sig := sig) token) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.cancel_frame
    token before

theorem host_checked (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) :
    HostImplSafe CheckedWrite (hostWithDeferred (grow := grow) bindings callees deferred control) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.host_safe
    bindings callees deferred control

/-- Queuing, starting, cancelling and refusals share the checked writer and journal
invariant across ordinary export prefixes, including intermediate callbacks and traps. -/
theorem checked_of_session (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer ∧ PublicationDelta state final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.Deferred.checked_of_steps
    bindings callees deferred control steps (Reference.HostWrite.cfgSafe_init _ _) fun program member =>
      False.elim (ordinary program member)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Deferred
