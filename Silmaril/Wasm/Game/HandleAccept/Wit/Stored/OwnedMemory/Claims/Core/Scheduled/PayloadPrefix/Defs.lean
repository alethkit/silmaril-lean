module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value
open Stored.Endpoints.RecordLower (Field)

inductive Outcome (Result : Type) where
  | returned (value : Result)
  | refused (issue : Stored.Endpoints.RecordLower.Issue)
  | trapped (reason : TrapReason)

structure Cursor {E : CoreEngine} (Host : Type) where
  thread : Option ThreadId
  frames : List (Seg E Host)
  rest : List (Activation E Host)

def Cursor.control {E : CoreEngine} {Host : Type} (cursor : Cursor (E := E) Host)
    (body : P E Host (Ret E)) : List (Activation E Host) :=
  ⟨cursor.thread, .prog body, cursor.frames⟩ :: cursor.rest

def visible {E : CoreEngine} {Host : Type} (labels : List (Label E Host)) : List (Label E Host) :=
  labels.filter fun label => match label with | .tau => false | _ => true

/-- Two finite prefixes compared with independently saved continuations.
Success enters both continuations. A typed refusal leaves the reference at
an actual prefix with no fictitious result. A trap records the common final
trap label and the stores after lockdown. -/
def Reaches {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (left right : Config E Host) (checkCursor canonCursor : Cursor (E := E) Host)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → P E Host (Ret E))
    (canonNext : Result → P E Host (Ret E)) : Prop :=
  ∃ outcome : Outcome Result, ∃ checkLabels canonLabels checkEnd canonEnd,
    Steps profile ready dispatch left checkLabels checkEnd ∧
    Steps profile ready dispatch right canonLabels canonEnd ∧
    checkEnd.store = canonEnd.store ∧ visible checkLabels = visible canonLabels ∧
    match outcome with
    | .returned value => checkEnd.ctl = checkCursor.control (checkNext (.ok value)) ∧
        canonEnd.ctl = canonCursor.control (canonNext value)
    | .refused issue => checkEnd.ctl = checkCursor.control (checkNext (.error issue))
    | .trapped reason => checkEnd.ctl = [] ∧ canonEnd.ctl = [] ∧
        ∃ leading, visible canonLabels = leading ++ [.trap reason]

/-- Compare a closed segment at any common reached store. This finite rule
does not cover callbacks that can suspend or never return. -/
def Compare {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (checked : P E Host (Except Stored.Endpoints.RecordLower.Issue Result))
    (canonical : P E Host Result) : Prop :=
  ∀ (left right : Config E Host), left.store = right.store →
    ∀ (checkCursor canonCursor : Cursor (E := E) Host), checkCursor.thread = canonCursor.thread →
      ∀ (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → P E Host (Ret E)) (canonNext : Result → P E Host (Ret E)),
        left.ctl = checkCursor.control (checked >>= checkNext) →
        right.ctl = canonCursor.control (canonical >>= canonNext) →
        Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext

mutual
/-- The closed flat fragment whose leaves need no allocator or host query
after the checked transfer guard. Nested records, tuples and fixed lists
use the same flattening traversal. -/
def HandleField : Field → Prop
  | .aggregate _ fields | .fixed _ _ fields => HandleFields fields
  | field => CanonicalHandle field
termination_by structural field => field

def HandleFields : List Field → Prop
  | [] => True
  | field :: rest => HandleField field ∧ HandleFields rest
termination_by structural fields => fields
end

def flatReply {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (schema : TypeOf) (ticket : Nat)
    (verdict : Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) : Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion ((GiveEffectRoute.flat schema).reply destination ticket verdict))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
