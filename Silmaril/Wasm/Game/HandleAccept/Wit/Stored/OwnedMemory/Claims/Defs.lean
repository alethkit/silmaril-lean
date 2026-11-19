module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

/-- Accepted trees are durable observations. Only `held` can authorize giving or dropping
an owner. A child already built by another call is not lifted or claimed again. -/
structure State (sig : Signature) where
  accepted : List (Tree sig) := []
  held : List Receipt := []

inductive Issue where
  | lift (issue : OwnedMemory.Issue)
  | needsEndpointClaims
  | alias
  | unclaimed
  | wrongResourceType
  deriving DecidableEq, Repr

def rootReceipts {sig : Signature} : Tree sig → List Receipt
  | .atom impossible => impossible.elim
  | .tag payload _ _ => payload.2.val.owners

def receiptId (receipt : Receipt) : HandleObjId := receipt.2.identity

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

variable {E : CoreEngine}

/-- This resource-claims API does not yet compose with endpoint claims. Reject an endpoint or
error context anywhere in the schema, before the reference loader moves any handle. -/
def acceptNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E (State sig) (Except Issue (Tree sig)) := do
  if contains (fun | .future _ | .stream _ | .errorContext => true | _ => false) (sig.payload tag) then
    return .error .needsEndpointClaims
  match ← buildNode sig limits quirks cx tag input children with
  | .error issue => return .error (.lift issue)
  | .ok tree =>
    let state ← hostGet
    let receipts := rootReceipts tree
    let identities := receipts.map receiptId
    let known := (state.accepted.flatMap rootReceipts ++ state.held).map receiptId
    if identities.Nodup ∧ !(identities.any known.contains) then
      hostSet ⟨tree :: state.accepted, receipts ++ state.held⟩
      return .ok tree
    else return .error .alias

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
