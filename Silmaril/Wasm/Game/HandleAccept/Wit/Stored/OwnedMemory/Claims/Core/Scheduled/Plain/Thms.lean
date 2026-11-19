module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

/-- A successful body evaluation is a silent reference execution, with the actual
parked Core continuation, resumers, and saved activations left in place. -/
theorem runBody_steps {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (success : runBody body start.store start.host = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body_steps_at
    body start updated host result finish thread segs rest profile ready dispatch focused none (.inl rfl) success

/-- A body that reads the current thread still gives silent machine steps when
that read takes its answer from the actual activation. -/
theorem runBody_thread_steps {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (success : runBody body start.store start.host (some thread) = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body_steps_at
    body start updated host result finish thread segs rest profile ready dispatch focused (some thread) (.inr rfl) success

/-- A resolved memory binding checks the actual caller and live `mayLeave` bit
before lifting. An ordinary refusal has the same canonical store and authority
as entry; the only effect is its typed reply in the journal. -/
theorem invoke_memory {sig : Stored.Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) (thread : Option ThreadId) :
    let binding : Binding sig := ⟨contract.name.2, contract.inst, .accept contract memory⟩
    runBody (do Scheduled.finish ticket (← Scheduled.invoke ticket binding args)) reference host (some thread) =
      match callerInstance reference thread with
      | .error issue => (reference, host, .error issue)
      | .ok caller =>
        if caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave) then
          runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference host (some thread)
        else
          (reference, host.record (.refused ticket .wrongContext), .ok [i32Flat 1, i32Flat 0]) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.invoke_memory
    ticket contract memory args reference host thread

/-- The memory accept body writes exactly the checked arena result. It records a
publication followed by a successful return, or a typed refusal without publishing. -/
theorem accept_body {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) :
    let call := Endpoints.Core.Scheduled.nodeCall contract reference args
    let attempt := Core.attempt contract memory ⟨reference, host.writer⟩ call
    let state : HostState sig := { host with writer := attempt.1.writer }
    let reply := match attempt.2 with
      | .ok handle => (state.record (.published ticket handle.toNat), completion ticket (.ok handle.toNat))
      | .error issue => (state, completion ticket (.error (.accept issue)))
    runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference host =
      (attempt.1.reference, reply.1.record reply.2.1, .ok reply.2.2) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body
    ticket contract memory args reference host

/-- Once the binding admits the caller, both memory accept paths have the same
canonical store effects, status and handle, embedded writer state and typed refusal. -/
theorem memory_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (oldHost : Endpoints.Core.Scheduled.HostState sig.val)
    (journal : HostState sig.val)
    (writer : journal.writer = (Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
      Endpoints.Core.World grow sig.val)).writer) :
    let old := Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost reference args
    let new := runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference journal
    let refused := new.2.1.newestFirst.head?.bind fun event => match event with
      | .refused _ issue => oldIssue issue
      | _ => none
    new.1 = old.1 ∧
      new.2.1.writer = (Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Endpoints.Core.World grow sig.val)).writer ∧
      new.2.2 = .ok old.2.2 ∧ old.2.1.refusals = refused.toList ++ oldHost.refusals :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.memory_plain
    sig ticket contract memory args reference oldHost journal writer

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain
