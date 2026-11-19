module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Thms
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Component.Value

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- Refusing before payload lift preserves component authorities, even if writing the
error result traps. It does not undo earlier effects or forbid result/subtask updates. -/
theorem refusal_frame (ticket : Nat) (caller : CallerId) (issue : Issue) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True)
      (refuseBeforeLift (grow := grow) (sig := sig) ticket caller issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.refusal_frame
    ticket caller issue before

/-- Given the same guarded caller record, the checked error and reference resolution
have identical continuations after the store read, including the indirect write and traps. -/
theorem resolve_error_agrees (ticket : Nat) (caller : CallerId) (snapshot : CStore (core3 grow))
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat)
    (record : ArenaField.callers.get? snapshot caller = some (.lower subtask cx args pos ft limits results))
    (type : ft.result = some resultType) (mode : results ≤ 1) :
    ∃ checked reference : CStore (core3 grow) → Session grow sig (Ret (core3 grow)),
      resolveError ticket caller = .op (S := Eff (core3 grow) (HostState sig)) .get checked ∧
      (do
        lowerOnResolve Limits.spec Quirks.none caller (some [.variant 1 none])
        pure (Ret.cancel (E := core3 grow) .none)) = .op (S := Eff (core3 grow) (HostState sig)) .get reference ∧
      checked snapshot = reference snapshot :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.resolve_error_agrees
    ticket caller snapshot subtask cx args pos ft limits results record type mode

theorem host_checked (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    HostImplSafe CheckedWrite (hostWithComponent (grow := grow) bindings callees) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.hostWithComponent_safe
    bindings callees

/-- The dispatcher conserves published roots, authority, and tickets across arbitrary
machine prefixes with checked initial continuations and checked host-frame programs.
The theorem includes typed refusals and canonical traps, not just successful returns. -/
theorem checked_of_steps (bindings : List (Binding sig)) (callees : List (Callee sig))
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.checked_of_component_steps
    bindings callees steps safe runSafe

/-- Arbitrary exports and internal scheduling from an ordinary session need no hypotheses
on the guest or its export sequence. Only injected raw programs need a write-policy proof. -/
theorem checked_of_session (bindings : List (Binding sig)) (callees : List (Callee sig))
    {prof : ProfileKind} {ready : HostReady (HostState sig)} (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer ∧ PublicationDelta state final.host :=
  checked_of_steps bindings callees steps (Component.Reference.HostWrite.cfgSafe_init _ _)
    (fun program member => (ordinary program member).elim)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall
