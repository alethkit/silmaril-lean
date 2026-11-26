module

public import Silmaril.Semantics.Operational.Environment
public import Silmaril.SSA.PEG.Semantics.Defs

/-! # An explicit heap token for a Java-inspired field-access profile -/

@[expose] public section

namespace Silmaril.SSA.Peggy.FieldHeap

open Silmaril.Semantics.Operational (Environment)
open RVSDG (Tuple)

abbrev ObjectId := Nat
abbrev Field := Nat
abbrev Object := Environment Field Int
abbrev Heap := Environment ObjectId Object

inductive Receiver where
  | null
  | object (id : ObjectId)
  deriving DecidableEq, Repr

inductive Fault where
  | nullReceiver
  | unallocated (id : ObjectId)
  | absentField (id : ObjectId) (field : Field)
  deriving DecidableEq, Repr

/-- An immutable heap snapshot with the first fault, if one has occurred. -/
structure State where
  heap : Heap
  fault : Option Fault

def State.initial (heap : Heap) : State := ⟨heap, none⟩

structure ReadResult where
  state : State
  value : Option Int

/-- The resolved object and the previous contents of one declared field. -/
structure Cell where
  id : ObjectId
  fields : Object
  value : Int

/-- Resolving a field never creates an object or a field. -/
def Heap.locate (heap : Heap) (receiver : Receiver) (field : Field) : Except Fault Cell :=
  match receiver with
  | .null => .error .nullReceiver
  | .object id =>
    match heap id with
    | none => .error (.unallocated id)
    | some fields =>
      match fields field with
      | none => .error (.absentField id field)
      | some value => .ok ⟨id, fields, value⟩

/-- An already faulted token carries its earlier fault past later accesses. -/
def State.locate (state : State) (receiver : Receiver) (field : Field) : Except Fault Cell :=
  match state.fault with
  | some fault => .error fault
  | none => Heap.locate state.heap receiver field

/-- The token is live and the receiver names an allocated object with the indicated field. -/
def Accessible (state : State) (receiver : Receiver) (field : Field) : Prop :=
  ∃ id fields old, receiver = .object id ∧ state.fault = none ∧
    state.heap id = some fields ∧ fields field = some old

/-- Two field addresses are disjoint if their receivers or their resolved field identifiers differ. -/
def Disjoint (left : Receiver) (lfield : Field) (right : Receiver) (rfield : Field) : Prop :=
  left ≠ right ∨ lfield ≠ rfield

def ReadResult.ofAccess (state : State) : Except Fault Int → ReadResult
  | .error fault => ⟨{ state with fault := some fault }, none⟩
  | .ok value => ⟨state, some value⟩

def getField (state : State) (receiver : Receiver) (field : Field) : ReadResult :=
  ReadResult.ofAccess state ((state.locate receiver field).map Cell.value)

def setField (state : State) (receiver : Receiver) (field : Field) (value : Int) : State :=
  match state.locate receiver field with
  | .error fault => { state with fault := some fault }
  | .ok cell =>
    { state with heap := Environment.set state.heap cell.id (Environment.set cell.fields field value) }

/-- Forward a known read value while consuming the same state token. A faulted token suppresses
that value and retains both the fault and the heap. -/
def forwardRead (state : State) (value : Int) : ReadResult :=
  ⟨state, match state.fault with | none => some value | some _ => none⟩

inductive DataSort where
  | state
  | receiver
  | int
  | read
  | readValue
  deriving DecidableEq

abbrev stateTy : PEG.Ty DataSort := .data .state
abbrev receiverTy : PEG.Ty DataSort := .data .receiver
abbrev intTy : PEG.Ty DataSort := .data .int
abbrev readTy : PEG.Ty DataSort := .data .read
abbrev readValueTy : PEG.Ty DataSort := .data .readValue

/-- Field identifiers are resolved in the opcode. Receivers and heap tokens are dynamic. -/
inductive Op : PEG.InstructionSet DataSort where
  | getField (field : Field) : Op [stateTy, receiverTy] readTy
  | setField (field : Field) : Op [stateTy, receiverTy, intTy] stateTy
  | forwardRead : Op [stateTy, intTy] readTy
  | readState : Op [readTy] stateTy
  | readValue : Op [readTy] readValueTy

def Carrier : DataSort → Type
  | .state => State
  | .receiver => Receiver
  | .int => Int
  | .read => ReadResult
  | .readValue => Option Int

/-- Every opcode is executable on defined operands. A field fault is a defined token value.
Figure 11 supplies strict lifting and its separate bottom for unavailable operands. -/
def interpretation : PEG.Interpretation.{0,0,0} Op where
  carrier := Carrier
  run
    | .getField f, .cons s (.cons r .nil) => some (getField s r f)
    | .setField f, .cons s (.cons r (.cons v .nil)) => some (setField s r f v)
    | .forwardRead, .cons s (.cons v .nil) => some (forwardRead s v)
    | .readState, .cons r .nil => some r.state
    | .readValue, .cons r .nil => some r.value

/-- Ordered ports for a completed field access. Consumers observe the final token first. -/
abbrev observationTypes : List (PEG.Ty DataSort) := [stateTy, readValueTy]

abbrev Observation := Tuple (fun t => Option (interpretation.Value t)) observationTypes

/-- The first port retains heap and fault. At the second port `some none` means that the read
completed with a fault, whereas `none` means that the PEG result itself is bottom. -/
def ReadResult.ordered (result : ReadResult) : Observation :=
  .cons (some result.state) (.cons (some result.value) .nil)

noncomputable def observe {params : List (PEG.Ty DataSort)} {nodes loops : Nat}
    (graph : PEG.Graph Op params observationTypes nodes loops) (env : Tuple interpretation.Value params)
    (wf : WellFounded graph.Demand) (index : PEG.Index loops) : Observation :=
  graph.observe interpretation (graph.denote interpretation env wf) index

end Silmaril.SSA.Peggy.FieldHeap
