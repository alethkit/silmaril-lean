module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
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

/-- Compare the programs at a given common reached store and two saved cursors. -/
def CompareAt {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (left right : Config E Host)
    (checked : P E Host (Except Stored.Endpoints.RecordLower.Issue Result)) (canonical : P E Host Result) : Prop :=
  left.store = right.store →
    ∀ (checkCursor canonCursor : Cursor (E := E) Host), checkCursor.thread = canonCursor.thread →
      ∀ (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → P E Host (Ret E)) (canonNext : Result → P E Host (Ret E)),
        left.ctl = checkCursor.control (checked >>= checkNext) →
        right.ctl = canonCursor.control (canonical >>= canonNext) →
        Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext

/-- Compare a closed segment at any common reached store. This finite rule
does not cover callbacks that can suspend or never return. -/
def Compare {E : CoreEngine} {Host Result : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (checked : P E Host (Except Stored.Endpoints.RecordLower.Issue Result))
    (canonical : P E Host Result) : Prop :=
  ∀ left right, CompareAt profile ready dispatch left right checked canonical

section

variable (tagFits : Nat → Nat → Prop)

mutual
/-- The closed flat fragment whose leaves need no allocator or host query
after the checked transfer guard. A sum's tag rule is independent of which
leaves are in the fragment; coercing slots can still emit canonical choices. -/
def HandleFieldWhere : Field → Prop
  | .aggregate _ fields | .fixed _ _ fields => HandleFieldsWhere fields
  | .sum _ arms tag selected => tagFits tag arms.length ∧ HandleArmWhere selected
  | field => CanonicalHandle field
termination_by structural field => field

def HandleFieldsWhere : List Field → Prop
  | [] => True
  | field :: rest => HandleFieldWhere field ∧ HandleFieldsWhere rest
termination_by structural fields => fields

def HandleArmWhere : Option Field → Prop
  | none => True
  | some field => HandleFieldWhere field
termination_by structural selected => selected
end

end

abbrev HandleShape := HandleFieldWhere (fun _ _ => True)

abbrev HandleField := HandleFieldWhere Nat.lt

def MemoryHandleRoot : Field → Prop
  | .sum _ _ _ none => True
  | .sum _ _ _ (some item) => CanonicalHandle item
  | item => CanonicalHandle item

def flatReply {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (schema : TypeOf) (ticket : Nat)
    (verdict : Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) : Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion ((GiveEffectRoute.flat schema).reply destination ticket verdict))

def memoryReply {grow : SingleThreaded.GrowOracle} {sig : Signature}
    (destination : RecordDestination) (pointer : FlatValue) (ticket : Nat)
    (verdict : Except Stored.Endpoints.RecordLower.Issue Unit) : Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion ((GiveEffectRoute.memory pointer).reply destination ticket verdict))

/-- `Canon.store` treats root placement as a precondition; the public route
checks it explicitly. An invalid placement has no matching canonical step. -/
def placement {grow : SingleThreaded.GrowOracle} (destination : RecordDestination) (store : CStore (core3 grow))
    (area : Layout) (ptr : Nat) : Except TrapReason Unit := do
  if ptr % area.alignment.bytes != 0 then throw .unalignedPointer
  let some size := (core3 grow).memSize? store.core destination.memory
    | throw (.internal "dangling memory address")
  if ptr + area.size > size then throw .outOfBounds

def MemoryReaches {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (left right : Config E Host)
    (checkCursor canonCursor : Cursor (E := E) Host) (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → P E Host (Ret E))
    (canonNext : Unit → P E Host (Ret E)) (placementVerdict : Except TrapReason Unit) : Prop :=
  Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext ∨
    ∃ reason count reached, placementVerdict = .error reason ∧
      Steps profile ready dispatch left (List.replicate count .tau ++ [.trap reason]) reached ∧
      reached.ctl = [] ∧ reached.store = StepDefs.lockdownSt left.store

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
