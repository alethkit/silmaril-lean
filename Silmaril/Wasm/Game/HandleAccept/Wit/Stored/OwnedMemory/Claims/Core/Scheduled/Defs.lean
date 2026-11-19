module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Channel.endKind)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

inductive Issue where
  | accept (issue : Core.Issue)
  | claim (issue : Claims.Issue)
  | wrongContext
  | wrongType
  | unlinkedImport
  | ambiguousBinding
  | badSelection
  deriving DecidableEq, Repr

/-- Import tickets distinguish reentrant calls to the same binding. A canonical trap is
observed in the machine's labels; the started call has no status return in this journal. -/
inductive Event where
  | entered (ticket : Nat) (name : String) (type : V1.FuncType) (args : List FlatValue)
  | returned (ticket : Nat) (value : Nat)
  | refused (ticket : Nat) (issue : Issue)
  | bindingTrap (ticket : Nat) (issue : Issue)
  deriving BEq

structure HostState (sig : Signature) where
  writer : State sig := {}
  nextTicket : Nat := 0
  newestFirst : List Event := []

variable {sig : Signature}

def HostState.transcript (state : HostState sig) : List Event := state.newestFirst.reverse

def HostState.refusals (state : HostState sig) : List Issue :=
  state.newestFirst.filterMap fun
    | .refused _ issue | .bindingTrap _ issue => some issue
    | _ => none

def HostState.enter (state : HostState sig) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : HostState sig :=
  { state with
    nextTicket := state.nextTicket + 1
    newestFirst := .entered state.nextTicket name type args :: state.newestFirst }

def HostState.record (state : HostState sig) (event : Event) : HostState sig :=
  { state with newestFirst := event :: state.newestFirst }

def completion (ticket : Nat) : Except Issue Nat → Event × List FlatValue
  | .ok value => (.returned ticket value, [i32Flat 0, i32Flat value])
  | .error issue => (.refused ticket issue, [i32Flat 1, i32Flat 0])

/-- The journal is append-only; neither a callback nor a trap can roll back its entries. -/
def Extends (before after : HostState sig) : Prop :=
  before.transcript <+: after.transcript ∧ before.nextTicket ≤ after.nextTicket

/-- The only changes to authority are publication of a newly lifted root and spending a
specific identity. A new successful lift may reacquire an endpoint, but a resource arena
identity already observed in an accepted root cannot be registered again. -/
inductive WriterStep : State sig → State sig → Prop where
  | same (state : State sig) : WriterStep state state
  | publish {before after : State sig} (tree : Tree sig)
      (registered : before.register tree = .ok after) : WriterStep before after
  | spend (state : State sig) (update : Spend) : WriterStep state (update.apply state)

inductive WriterRun : State sig → State sig → Prop where
  | refl (state : State sig) : WriterRun state state
  | cons {before next after : State sig} (step : WriterStep before next)
      (rest : WriterRun next after) : WriterRun before after

def CheckedWrite (before after : HostState sig) : Prop :=
  Extends before after ∧ WriterStep before.writer after.writer

abbrev Session (grow : SingleThreaded.GrowOracle) (sig : Signature) (Result : Type) :=
  P (core3 grow) (HostState sig) Result

/-- Import capabilities fix the destination and nominal type at link time. Core passes
an accepted tree index and a position within that root's observations, never an arena ID. -/
inductive Action (sig : Signature) where
  | accept (contract : Contract sig) (memory : Option Nat)
  | giveOwner (resource : RtId)
  | dropOwner (resource : RtId)
  | giveEndpoint (channel : Channel) (element : Element)

structure Binding (sig : Signature) where
  name : String
  inst : InstId
  action : Action sig

variable {grow : SingleThreaded.GrowOracle}

def Binding.accept (contract : Contract sig) (linked : ModuleInst) (memoryIndex : Nat) : Binding sig :=
  ⟨contract.name.2, contract.inst, .accept contract linked.mems[memoryIndex]?⟩

def Binding.type (binding : Binding sig) : V1.FuncType :=
  match binding.action with
  | .accept contract _ => Endpoints.Core.Scheduled.acceptType contract
  | _ => Endpoints.Core.Scheduled.giveType

def finish (ticket : Nat) (result : Except Issue Nat) : Session grow sig (List FlatValue) := do
  let (event, flat) := completion ticket result
  hostSet ((← hostGet).record event)
  return flat

def publishRoot (tree : Tree sig) : Session grow sig (Except Issue Nat) := do
  let current ← hostGet
  match current.writer.register tree with
  | .error issue => return .error (.accept (.claims issue))
  | .ok writer =>
    hostSet { current with writer }
    return .ok ((BitVec.ofNat 32 writer.accepted.length).toNat)

def accept (contract : Contract sig) (memory : Option Nat) (args : List FlatValue) :
    Session grow sig (Except Issue Nat) := do
  let state ← hostGet
  let reference ← getStore
  let call := Endpoints.Core.Scheduled.nodeCall contract reference args
  let (updated, result) := load contract memory ⟨reference, state.writer⟩ call
  modifyStore fun _ => updated
  match result with
  | .error issue => return .error (.accept issue)
  | .ok tree => publishRoot tree

def select (handle : BitVec 32) : Session grow sig (Option (Tree sig)) := do
  return Endpoints.Core.childFromHistory (← hostGet).writer.accepted handle

/-- Embed the claims program without snapshotting diagnostics. In particular the update
that spends an owner precedes a possibly reentrant canonical destructor call. -/
def claims : Access (core3 grow) (HostState sig) sig where
  read := return (← hostGet).writer
  spend update := do
    let current ← hostGet
    hostSet { current with writer := update.apply current.writer }

def withTree (args : List FlatValue) (use : Tree sig → Nat → Session grow sig (Except Issue Nat)) :
    Session grow sig (Except Issue Nat) := do
  match args with
  | [.int .i32 handle, .int .i32 position] =>
    let some tree ← select handle | return .error .badSelection
    use tree position.toNat
  | _ => return .error .wrongType

/-- Canonical give and drop run in the live scheduler. Typed refusals are status pairs;
an actual destructor or canonical lower trap is not converted into an ordinary refusal. -/
def invoke (binding : Binding sig) (args : List FlatValue) : Session grow sig (Except Issue Nat) := do
  if (← currentInst?) != some binding.inst || !((← getStore).inst? binding.inst).any (·.mayLeave) then
    return .error .wrongContext
  let cx : LiftLowerContext (core3 grow) := { opts := {}, inst := binding.inst }
  match binding.action with
  | .accept contract memory =>
    if contract.inst != binding.inst then return .error .wrongContext
    accept contract memory args
  | .giveOwner resource => withTree args fun tree position => do
    let some receipt := (rootReceipts tree)[position]? | return .error .badSelection
    return (← claims.give Limits.spec cx resource (receiptId receipt)).mapError .claim
  | .dropOwner resource => withTree args fun tree position => do
    let some receipt := (rootReceipts tree)[position]? | return .error .badSelection
    let result ← claims.drop (destructorCall Limits.spec Quirks.none) resource (receiptId receipt)
    return result.mapError .claim |>.map (fun _ => 0)
  | .giveEndpoint channel element => withTree args fun tree position => do
    let some id := (rootEndpoints tree)[position]? | return .error .badSelection
    return (← claims.giveEndpoint Limits.spec cx channel element ⟨id⟩).mapError .claim

def rejectBinding (ticket : Nat) (issue : Issue) : Session grow sig (List FlatValue) := do
  hostSet ((← hostGet).record (.bindingTrap ticket issue))
  trap (.hostTrap "invalid mixed acceptor import binding")

def route (ticket : Nat) (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : Session grow sig (List FlatValue) := do
  match bindings.filter (·.name == name) with
  | [] => rejectBinding ticket .unlinkedImport
  | [binding] =>
    if type != binding.type then return ← rejectBinding ticket .wrongType
    finish ticket (← invoke binding args)
  | _ => rejectBinding ticket .ambiguousBinding

def dispatchImport (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : Session grow sig (List FlatValue) := do
  let state ← hostGet
  hostSet (state.enter name type args)
  route state.nextTicket bindings name type args

def host (bindings : List (Binding sig)) : HostImpl (core3 grow) (HostState sig) :=
  { HostImpl.none with embedder := dispatchImport bindings }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
