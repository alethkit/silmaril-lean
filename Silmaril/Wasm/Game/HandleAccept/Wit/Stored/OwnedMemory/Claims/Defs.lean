module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Endpoint Channel.endKind)

/-- Accepted trees are durable observations. Owners and readable endpoints have separate
one-shot claims. An existing child is not lifted or claimed again. -/
structure State (sig : Signature) where
  accepted : List (Tree sig) := []
  held : List Receipt := []
  endpoints : List EndId := []

inductive Issue where
  | lift (issue : OwnedMemory.Issue)
  | alias
  | unclaimed
  | unclaimedEndpoint
  | endpointTransfer (issue : Async.Transfer.Issue)
  | wrongResourceType
  deriving DecidableEq, Repr

def rootReceipts {sig : Signature} : Tree sig → List Receipt
  | .atom impossible => impossible.elim
  | .tag payload _ _ => payload.2.val.owners

def rootEndpoints {sig : Signature} : Tree sig → List EndId
  | .atom impossible => impossible.elim
  | .tag payload _ _ => Endpoints.endpointIds payload.2.val.value

def receiptId (receipt : Receipt) : HandleObjId := receipt.2.identity

/-- Validate all the root's claims together before publishing either class of claim or the
tree. Endpoints can come back through a new legitimate lift; a past observation is not a claim. -/
def State.register {sig : Signature} (state : State sig) (tree : Tree sig) : Except Issue (State sig) :=
  let receipts := rootReceipts tree
  let owners := receipts.map receiptId
  let known := (state.accepted.flatMap rootReceipts ++ state.held).map receiptId
  let endpoints := rootEndpoints tree
  if owners.Nodup ∧ !(owners.any known.contains) ∧
      endpoints.Nodup ∧ !(endpoints.any state.endpoints.contains) then
    .ok ⟨tree :: state.accepted, receipts ++ state.held, endpoints ++ state.endpoints⟩
  else .error .alias

/-- Look up the nominal type and representation from the held receipt, not from the caller.
The result is a prospective update; the caller chooses when to commit it. -/
def State.prepare {sig : Signature} (state : State sig) (resource : RtId) (id : HandleObjId) :
    Except Issue (Nat × State sig) :=
  match state.held.find? (fun entry => receiptId entry == id) with
  | none => .error .unclaimed
  | some receipt =>
    if receipt.1 != resource then .error .wrongResourceType
    else .ok (receipt.2.representation,
      { state with held := state.held.filter (fun entry => receiptId entry != id) })

def State.spendEndpoint {sig : Signature} (state : State sig) (id : EndId) : Except Issue (State sig) :=
  if id ∈ state.endpoints then .ok { state with endpoints := state.endpoints.filter (· != id) }
  else .error .unclaimedEndpoint

variable {E : CoreEngine}

/-- The shared canonical loader resolves owners and endpoints in one payload. Whole-schema
validation precedes lifting; a later trap does not publish any of the incomplete node's claims. -/
def acceptNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E (State sig) (Except Issue (Tree sig)) := do
  match ← buildNode sig limits quirks cx tag input children with
  | .error issue => return .error (.lift issue)
  | .ok tree =>
    match (← hostGet).register tree with
    | .error issue => return .error issue
    | .ok registered =>
      hostSet registered
      return .ok tree

/-- Use canonical `lower_own` to issue a fresh guest handle. The original claim is spent
only after insertion succeeds. A canonical trap retains its own effects. -/
def give {sig : Signature} (limits : Component.Limits) (cx : LiftLowerContext E)
    (resource : RtId) (id : HandleObjId) : P E (State sig) (Except Issue Nat) := do
  match (← hostGet).prepare resource id with
  | .error issue => return .error issue
  | .ok (representation, spent) =>
    let slot ← lowerOwn limits cx resource representation
    hostSet spent
    return .ok slot

/-- Canonical lower of an endpoint can transfer its owner before a failing table insertion.
Commit spending before that effect, after validating the arena identity and whole element type. -/
def giveEndpoint {sig : Signature} (limits : Component.Limits) (cx : LiftLowerContext E)
    (channel : Channel) (element : Element) (endpoint : Endpoint (channel.endKind .read) element) :
    P E (State sig) (Except Issue Nat) := do
  match (← hostGet).spendEndpoint endpoint.id with
  | .error issue => return .error issue
  | .ok spent =>
    match Async.Transfer.readyToGive (← getStore) channel element endpoint with
    | .error issue => return .error (.endpointTransfer issue)
    | .ok () =>
      hostSet spent
      return .ok (← lowerAsyncValue limits (channel.endKind .read) cx endpoint.id)

/-- Spend the host claim before entering the actual resource destructor, so a trapping
or reentrant destructor cannot make the same claim available a second time. -/
def drop {sig : Signature} (destructor : InstId → DtorRequest E → P E (State sig) Unit)
    (resource : RtId) (id : HandleObjId) : P E (State sig) (Except Issue Unit) := do
  match (← hostGet).prepare resource id with
  | .error issue => return .error issue
  | .ok (representation, spent) =>
    let inst ← Builtins.resourceEnter
    let some request ← dropHandleTail resource { rt := resource, rep := representation, own := true }
      | internal "an owning resource drop must request its destructor"
    hostSet spent
    destructor inst request
    return .ok ()

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
