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

structure HostState (sig : Signature) where
  writer : State sig := {}
  refusals : List Issue := []

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

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def Binding.accept (contract : Contract sig) (linked : ModuleInst) (memoryIndex : Nat) : Binding sig :=
  ⟨contract.name.2, contract.inst, .accept contract linked.mems[memoryIndex]?⟩

def Binding.type (binding : Binding sig) : V1.FuncType :=
  match binding.action with
  | .accept contract _ => Endpoints.Core.Scheduled.acceptType contract
  | _ => Endpoints.Core.Scheduled.giveType

def finish (result : Except Issue Nat) : Session grow sig (List FlatValue) := do
  match result with
  | .ok value => return [i32Flat 0, i32Flat value]
  | .error issue =>
    let state ← hostGet
    hostSet { state with refusals := issue :: state.refusals }
    return [i32Flat 1, i32Flat 0]

def accept (contract : Contract sig) (memory : Option Nat) (args : List FlatValue) :
    Session grow sig (Except Issue Nat) := do
  let state ← hostGet
  let reference ← getStore
  let call := Endpoints.Core.Scheduled.nodeCall contract reference args
  let (updated, result) := attempt contract memory ⟨reference, state.writer⟩ call
  modifyStore fun _ => updated.reference
  hostSet { state with writer := updated.writer }
  return result.mapError .accept |>.map BitVec.toNat

def select (handle : BitVec 32) : Session grow sig (Option (Tree sig)) := do
  return Endpoints.Core.childFromHistory (← hostGet).writer.accepted handle

/-- Embed the claims program without snapshotting diagnostics. In particular the update
that spends an owner precedes a possibly reentrant canonical destructor call. -/
def claims : Access (core3 grow) (HostState sig) sig where
  read := return (← hostGet).writer
  write writer := do hostSet { (← hostGet) with writer }

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

def rejectBinding (issue : Issue) : Session grow sig (List FlatValue) := do
  let _ ← finish (.error issue)
  trap (.hostTrap "invalid mixed acceptor import binding")

def dispatchImport (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : Session grow sig (List FlatValue) := do
  match bindings.filter (·.name == name) with
  | [] => rejectBinding .unlinkedImport
  | [binding] =>
    if type != binding.type then return ← rejectBinding .wrongType
    finish (← invoke binding args)
  | _ => rejectBinding .ambiguousBinding

def host (bindings : List (Binding sig)) : HostImpl (core3 grow) (HostState sig) :=
  { HostImpl.none with embedder := dispatchImport bindings }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
