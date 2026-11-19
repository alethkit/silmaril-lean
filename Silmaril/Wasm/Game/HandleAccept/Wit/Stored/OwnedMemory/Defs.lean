module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value

abbrev Receipt := (resource : RtId) × Resources.Owned resource

/-- A reference value observed together with the real identities of its owned leaves.
Receipts follow the active leaves in canonical traversal order; representations are not keys.
This observation does not itself authorize a second transfer. -/
structure Observed where
  value : Val
  owners : List Receipt

def Observed.ordinary (value : Val) : Observed := ⟨value, []⟩

def Observed.aggregate (ctor : List Val → Val) (items : List Observed) : Observed :=
  ⟨ctor (items.map Observed.value), items.flatMap Observed.owners⟩

def Observed.variant (index : Nat) (payload : Option Observed) : Observed :=
  ⟨.variant index (payload.map Observed.value), (payload.map Observed.owners).getD []⟩

def Observed.own (resource : RtId) (identity : HandleObjId) (rep : Nat) : Observed :=
  ⟨.own rep, [⟨resource, ⟨identity, rep⟩⟩]⟩

mutual
  def ownerRepresentations : Val → List Nat
    | .record fields | .list fields => ownerRepresentationsIn fields
    | .variant _ (some value) => ownerRepresentations value
    | .own representation => [representation]
    | _ => []
  termination_by structural value => value

  def ownerRepresentationsIn : List Val → List Nat
    | [] => []
    | field :: fields => ownerRepresentations field ++ ownerRepresentationsIn fields
  termination_by structural fields => fields
end

def Observed.Complete (observed : Observed) : Prop :=
  observed.owners.map (fun receipt => receipt.2.representation) = ownerRepresentations observed.value

abbrev Payload (type : TypeOf) :=
  { observed : Observed // observed.value.HasType type ∧ observed.Complete }

def ast (sig : Signature) : AstSig :=
  ⟨sig.Tag, fun tag => Payload (sig.payload tag), sig.arity⟩

abbrev Tree (sig : Signature) := AST (ast sig)

inductive Issue where
  | schema (issue : Stored.Issue)
  | flatOwnerUnsupported
  | incompleteReceipts
  deriving DecidableEq, Repr

def checkSchema (type : TypeOf) : Except Stored.Issue Unit :=
  if containsBorrow type then .error .storedBorrow
  else if ABI.ValType.WellFormedCM type then .ok ()
  else .error .malformedType

variable {E : CoreEngine} {World : Type}

/-- Interpret only owner leaves differently from the ordinary memory load. `takeWith` uses
the identity returned by the reference removal; no handle slot is reread or reconstructed. -/
def carrier (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) :
    LoadCarrier E World Observed :=
  let ref : LoadCarrier E World Val := .reference limits quirks cx
  { prim := fun prim ptr => Observed.ordinary <$> ref.prim prim ptr
    flags := fun labels ptr => Observed.ordinary <$> ref.flags labels ptr
    own := fun resource ptr => do
      let slot := (← loadInt cx ptr 4).toNat
      Resources.takeWith cx resource slot (Observed.own resource)
    borrow := fun resource ptr => Observed.ordinary <$> ref.borrow resource ptr
    stream := fun type ptr => Observed.ordinary <$> ref.stream type ptr
    future := fun type ptr => Observed.ordinary <$> ref.future type ptr
    errorContext := fun ptr => Observed.ordinary <$> ref.errorContext ptr
    list := Observed.aggregate Val.list
    record := Observed.aggregate Val.record
    variant := Observed.variant }

def checkValue (type : TypeOf) (value : Observed) : Except Issue (Payload type) :=
  if typed : value.value.HasType type then
    if complete : value.owners.map (fun receipt => receipt.2.representation) =
        ownerRepresentations value.value then .ok ⟨value, typed, complete⟩
    else .error .incompleteReceipts
  else .error (.schema .decodedType)

/-- Check the whole schema before lifting a handle. Once memory lifting starts, failures
have reference trap semantics, not the Core checked import's call-local rejection semantics. -/
def lift (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (input : Input) : P E World (Except Issue (Payload type)) :=
  match checkSchema type with
  | .error issue => pure (.error (.schema issue))
  | .ok () =>
    match input with
    | .memory ptr => do
      let width ← ptrType cx
      let layout := ABI.layout width type
      checkAligned ptr layout.alignment.bytes
      checkInBounds cx ptr layout.size
      let value ← loadAtWith limits cx width (carrier limits quirks cx) type ptr
      return checkValue type value
    | .flat values => do
      let plain ← Stored.lift limits quirks cx type (.flat values)
      return match plain with
      | .ok payload => checkValue type (Observed.ordinary payload.val)
      | .error .ownedResourceNeedsIdentity => .error .flatOwnerUnsupported
      | .error issue => .error (.schema issue)

def buildNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E World (Except Issue (Tree sig)) := do
  if !(sig.arity tag).Admits children.length then return .error (.schema .childArity)
  let payload ← lift limits quirks cx (sig.payload tag) input
  return payload.map fun value => AST.node tag value children

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
