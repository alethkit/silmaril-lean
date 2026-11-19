module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract checkChildren)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled (nodeCall)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (NodeArgs)

theorem body_steps_at {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (activation : Option (Option ThreadId)) (matchesThread : activation = none ∨ activation = some thread)
    (success : Plain.runBody body start.store start.host activation = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } := by
  induction body generalizing start with
  | pure value =>
    simp only [Plain.runBody, Prod.mk.injEq, Except.ok.injEq] at success
    obtain ⟨store_eq, host_eq, result_eq⟩ := success
    subst updated host result
    have frame : { start with ctl := ⟨thread, .prog (finish value), segs⟩ :: rest } = start := by
      cases start
      congr
      exact focused.symm
    rw [frame]
    exact ⟨[], rfl, .refl _⟩
  | op op next ih =>
    cases op <;> simp only [Plain.runBody] at success
    case get =>
      obtain ⟨labels, silent, tail⟩ := ih start.store
        { start with ctl := ⟨thread, .prog (next start.store >>= finish), segs⟩ :: rest } rfl success
      exact ⟨.tau :: labels, silent, .cons (.get focused) tail⟩
    case modify update =>
      obtain ⟨labels, silent, tail⟩ := ih ()
        { start with store := update start.store, ctl := ⟨thread, .prog (next () >>= finish), segs⟩ :: rest }
        rfl success
      exact ⟨.tau :: labels, silent, .cons (.modify focused) tail⟩
    case hostGet =>
      obtain ⟨labels, silent, tail⟩ := ih start.host
        { start with ctl := ⟨thread, .prog (next start.host >>= finish), segs⟩ :: rest } rfl success
      exact ⟨.tau :: labels, silent, .cons (.hostGet focused) tail⟩
    case hostSet newHost =>
      obtain ⟨labels, silent, tail⟩ := ih ()
        { start with host := newHost, ctl := ⟨thread, .prog (next () >>= finish), segs⟩ :: rest }
        rfl success
      exact ⟨.tau :: labels, silent, .cons (.hostSet focused) tail⟩
    case currentThread =>
      rcases matchesThread with missing | known
      · rw [missing] at success
        cases success
      · rw [known] at success
        obtain ⟨labels, silent, tail⟩ := ih thread
          { start with ctl := ⟨thread, .prog (next thread >>= finish), segs⟩ :: rest } rfl
          (by simpa only [known] using success)
        exact ⟨.tau :: labels, silent, .cons (.currentThread focused) tail⟩
    all_goals cases success

theorem resolve_caller {E : CoreEngine} {Host Result : Type} (rest : Option InstId → P E Host Result)
    (reference : CStore E) (host : Host) (thread : Option ThreadId) :
    Plain.runBody (currentInst? >>= rest) reference host (some thread) =
      match Plain.callerInstance reference thread with
      | .ok caller => Plain.runBody (rest caller) reference host (some thread)
      | .error issue => (reference, host, .error issue) := by
  cases thread with
  | none => rfl
  | some thread =>
    cases active : ArenaField.threads.get? reference thread with
    | none =>
      simp [currentInst?, currentTask?, currentThread, getThread, getObj, getStore,
        perform, internal, trap, Plain.runBody, Plain.callerInstance, active,
        Prog.bind_assoc]
    | some activeThread =>
      cases task : ArenaField.tasks.get? reference activeThread.task <;>
        simp [currentInst?, currentTask?, currentThread, getThread, getTask, getObj, getStore,
          perform, internal, trap, Plain.runBody, Plain.callerInstance, active, task,
          Prog.bind_assoc]

theorem invoke_memory {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) (thread : Option ThreadId) :
    let binding : Binding sig := ⟨contract.name.2, contract.inst, .accept contract memory⟩
    Plain.runBody (do finish ticket (← invoke ticket binding args)) reference host (some thread) =
      match Plain.callerInstance reference thread with
      | .error issue => (reference, host, .error issue)
      | .ok caller =>
        if caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave) then
          Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference host (some thread)
        else
          (reference, host.record (.refused ticket .wrongContext), .ok [i32Flat 1, i32Flat 0]) := by
  dsimp only
  simp only [invoke, Prog.bind_eq, Prog.bind_assoc]
  rw [← Prog.bind_eq, resolve_caller]
  cases evaluated : Plain.callerInstance reference thread with
  | error _ => rfl
  | ok caller =>
    by_cases same : caller = some contract.inst
    · subst caller
      cases available : (reference.inst? contract.inst).any (·.mayLeave) <;>
        simp [getStore, perform, Plain.runBody, available, finish, writeCompletion, hostGet, hostSet, completion]
    · simp [same, bne_iff_ne, finish, writeCompletion, completion, hostGet, hostSet, perform, Plain.runBody]

private theorem bind_ok {Error Input Output : Type} {input : Except Error Input}
    {next : Input → Except Error Output} {output : Output} (success : input >>= next = .ok output) :
    ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | error _ => cases success
  | ok value => exact ⟨value, rfl, success⟩

private theorem children_room {sig : Signature} (tag : sig.Tag) (length pointer count : Nat)
    (success : checkChildren sig tag length pointer count = .ok ()) : length + 1 < 2 ^ 32 := by
  unfold checkChildren at success
  dsimp only at success
  by_contra! exhausted
  split at success <;> try cases success
  split at success <;> try cases success
  split at success <;> cases success

private theorem preflight_room {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig) (memory : Option Nat) (world : Claims.Core.World grow sig) (call : UCall Nat)
    {operands : NodeArgs sig.Tag × List (Tree sig)}
    (success : Claims.Core.preflight contract memory world call = .ok operands) :
    world.writer.accepted.length + 1 < 2 ^ 32 := by
  unfold Claims.Core.preflight at success
  dsimp only at success
  split at success
  · cases success
  generalize checked_eq : contract.preflightOperands checkSchema memory world.writer.accepted call = checked at success
  cases checked with
  | error _ => cases success
  | ok result =>
    unfold Contract.preflightOperands at checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, room, _⟩ := bind_ok checked_eq
    exact children_room _ _ _ _ room

private theorem load_room {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig) (memory : Option Nat) (world : Claims.Core.World grow sig) (call : UCall Nat)
    {store : CStore (core3 grow)} {tree : Tree sig}
    (success : Claims.Core.load contract memory world call = (store, .ok tree)) :
    world.writer.accepted.length + 1 < 2 ^ 32 := by
  unfold Claims.Core.load at success
  split at success
  next => cases success
  next checked => exact preflight_room contract memory world call checked

private theorem register_length {sig : Signature} {before after : Claims.State sig} {tree : Tree sig}
    (success : before.register tree = .ok after) : after.accepted.length = before.accepted.length + 1 := by
  unfold Claims.State.register at success
  dsimp only at success
  split at success
  · cases success
    rfl
  · cases success

theorem body {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) :
    let call := nodeCall contract reference args
    let attempt := Claims.Core.attempt contract memory ⟨reference, host.writer⟩ call
    let state : HostState sig := { host with writer := attempt.1.writer }
    let reply := match attempt.2 with
      | .ok handle => (state.record (.published ticket handle.toNat), completion ticket (.ok handle.toNat))
      | .error issue => (state, completion ticket (.error (.accept issue)))
    Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference host =
      (attempt.1.reference, reply.1.record reply.2.1, .ok reply.2.2) := by
  dsimp only
  unfold Claims.Core.attempt
  change Plain.runBody
      ((match (Claims.Core.load contract memory ⟨reference, host.writer⟩
          (nodeCall contract reference args)).2 with
        | .error issue => pure (.error (.accept issue))
        | .ok tree => publishRoot ticket tree) >>= finish ticket)
      (Claims.Core.load contract memory ⟨reference, host.writer⟩
        (nodeCall contract reference args)).1 host = _
  generalize loaded : Claims.Core.load contract memory ⟨reference, host.writer⟩
    (nodeCall contract reference args) = lifted
  obtain ⟨updated, result⟩ := lifted
  cases result with
  | error _ => rfl
  | ok tree =>
    have room := load_room contract memory ⟨reference, host.writer⟩ _ loaded
    change Plain.runBody
        ((match host.writer.register tree with
          | .error issue => pure (.error (.accept (.claims issue)))
          | .ok writer =>
            if writer.accepted.length ≥ 2 ^ 32 then pure (.error (.accept (.boundary .exhaustedHandles)))
            else do
              hostSet (({ host with writer } : HostState sig).record (.published ticket writer.accepted.length))
              pure (.ok writer.accepted.length)) >>= finish ticket) updated host = _
    dsimp only [Except.bind]
    generalize registered : host.writer.register tree = registration
    cases registration with
    | error _ => rfl
    | ok writer =>
      have fits : writer.accepted.length < 2 ^ 32 := (register_length registered).symm ▸ room
      have handle : (BitVec.ofNat 32 writer.accepted.length).toNat = writer.accepted.length :=
        Nat.mod_eq_of_lt fits
      simp only [Except.mapError, handle, Nat.not_le.mpr fits, ite_false]
      rfl

theorem memory_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (oldHost : Stored.Endpoints.Core.Scheduled.HostState sig.val)
    (journal : HostState sig.val)
    (writer : journal.writer = (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
      Stored.Endpoints.Core.World grow sig.val)).writer) :
    let old := Stored.Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost reference args
    let new := Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference journal
    let refused := new.2.1.newestFirst.head?.bind fun event => match event with
      | .refused _ issue => Plain.oldIssue issue
      | _ => none
    new.1 = old.1 ∧
      new.2.1.writer = (Claims.Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer ∧
      new.2.2 = .ok old.2.2 ∧ old.2.1.refusals = refused.toList ++ oldHost.refusals := by
  dsimp only
  rw [body]
  rw [writer]
  have agreed := Claims.Core.Plain.attempt_plain sig contract memory
    (⟨reference, oldHost.writer⟩ : Stored.Endpoints.Core.World grow sig.val) (nodeCall contract reference args)
  dsimp only at agreed
  unfold Stored.Endpoints.Core.Scheduled.acceptAttempt
  generalize old_eq : contract.attempt memory ⟨reference, oldHost.writer⟩
    (nodeCall contract reference args) = old at agreed ⊢
  generalize new_eq : Claims.Core.attempt contract memory
    (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ : Stored.Endpoints.Core.World grow sig.val))
    (nodeCall contract reference args) = new at agreed
  have new_eq_body : Claims.Core.attempt contract memory
      ⟨reference, (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer⟩ (nodeCall contract reference args) = new := new_eq
  rw [new_eq_body]
  obtain ⟨oldWorld, oldResult⟩ := old
  obtain ⟨newWorld, newResult⟩ := new
  obtain ⟨frame, result⟩ := agreed
  dsimp only at frame result
  subst newWorld
  cases oldResult <;> cases newResult
  case error.error oldReason newReason =>
    have reason : Claims.Core.Plain.oldIssue newReason = some oldReason := Except.error.inj result
    simp [Stored.Endpoints.Core.Scheduled.HostState.finish, Except.mapError, Except.map,
      Claims.Core.Plain.embedWorld, completion, HostState.record, Plain.oldIssue, reason]
  case error.ok => cases result
  case ok.error => cases result
  case ok.ok oldHandle newHandle =>
    have handle : newHandle = oldHandle := Except.ok.inj result
    subst newHandle
    simp [Stored.Endpoints.Core.Scheduled.HostState.finish, Except.mapError, Except.map,
      Claims.Core.Plain.embedWorld, completion, HostState.record]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled
