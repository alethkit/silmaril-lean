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
