module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory (Tree)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {prof : ProfileKind}
  {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
  {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId}
  {segments : List (Seg (core3 grow) (HostState sig))} {rest : List (Activation (core3 grow) (HostState sig))}

theorem resolve_begin (ticket : Nat) (caller : CallerId) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (room : writer.accepted.length < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest) :
    Machine.Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 writer.accepted.length))])
          completeResolvedTree ticket tree writer.accepted.length), segments⟩ :: rest } := by
  have step := Step.hostGet (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, registered, Nat.not_le.mpr room, ite_false] at step
  exact step

private theorem complete_read (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Machine.Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          let result ← (do
            if handle != writer.accepted.length then return .error .wrongResultType
            if writer.accepted.length ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
            hostSet (({ config.host with writer } : HostState sig).record (.published ticket writer.accepted.length))
            return .ok writer.accepted.length : Session grow sig (Except Issue Nat))
          match result with
          | .error issue => reject ticket issue
          | .ok published => do
            let _ ← writeCompletion (.returned ticket published, [])
            return .cancel .none), segments⟩ :: rest } := by
  have step := Step.hostGet (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, registered, Option.any] at step
  exact step

theorem complete_commit (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau]
      { config with
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } := by
  subst handle
  refine .cons (complete_read ticket writer.accepted.length tree writer registered pending) ?_
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Nat.not_le.mpr room]
  exact .cons (.hostSet rfl) (.cons (.hostGet rfl) (.cons (.hostSet rfl) (.refl _)))

theorem complete_stale (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (stale : handle ≠ writer.accepted.length)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg
        { config with host := config.host.record (.bindingTrap ticket .wrongResultType) }) := by
  refine .cons (complete_read ticket handle tree writer registered pending) ?_
  simp only [bne_iff_ne.mpr stale, ite_true]
  exact .cons (.hostGet rfl) (.cons (.hostSet rfl) (.cons (.trap rfl) (.refl _)))

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult
