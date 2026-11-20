module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- Records and tuples align from the current cursor. Arrays advance at the
validated element stride; the canonical array body does not read the width
to place the next element. Indirect maps use a separate per-entry rule. -/
inductive Track where
  | fields
  | elements (stride : Nat)

def Track.slot (mode : Track) (width : AddrType) (item : Field) (cursor : Nat) : Nat × Nat :=
  match mode with
  | .fields =>
    let area := layout width item.type
    let start := alignTo cursor area.alignment
    (start, start + area.size)
  | .elements stride => (cursor, cursor + stride)

def Track.checked (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field)
    (index cursor : Nat) : Session grow sig (Except RecordLower.Issue Unit) :=
  match mode with
  | .fields => Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
      items cursor index
  | .elements stride => Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
      items stride cursor index

def Track.canonical (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field)
    (cursor : Nat) : Session grow sig Unit :=
  match mode with
  | .fields => CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width items cursor
  | .elements stride => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width items .value stride cursor

def Track.readLabels : Track → List (Label (core3 grow) (HostState sig))
  | .fields => [.tau]
  | .elements _ => []

abbrev CheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))

abbrev CanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) := Unit → Session grow sig (Ret (core3 grow))

abbrev Finish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop

abbrev FieldComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
    Cursor (E := core3 grow) (HostState sig) → CheckNext grow sig → CanonNext grow sig → Finish grow sig → Prop

def FieldRule (compare : FieldComparison grow sig) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat) : Prop :=
  ∀ index (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) left right check canon,
    ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width item index (.memory address) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory address) >>= canonNext) →
    ∀ finish : Finish grow sig, (∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon) →
    compare item index address left right check canon checkNext canonNext finish

def Track.Slots (mode : Track) (width : AddrType) (rule : Field → Nat → Prop) : List Field → Nat → Prop
  | [], _ => True
  | item :: rest, cursor =>
    let (address, next) := mode.slot width item cursor
    rule item address ∧ mode.Slots width rule rest next

def checkTail (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (finish : CheckNext grow sig) : CheckNext grow sig
  | .error issue => finish (.error issue)
  | .ok () => mode.checked destination inst items index cursor >>= finish

def canonTail (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (cursor : Nat)
    (finish : CanonNext grow sig) : CanonNext grow sig := fun () => mode.canonical destination inst items cursor >>= finish

def focus (mode : Track) (destination : RecordDestination) (inst : InstId) (item : Field) (cursor : Nat)
    (right : State grow sig) (canon : Cursor (E := core3 grow) (HostState sig)) (finish : CanonNext grow sig) : State grow sig :=
  { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
    item (.memory (mode.slot destination.width item cursor).1) >>= finish) }

/-- Follow the actual memory programs in field order. With each sibling, the
canonical cursor read precedes the child; only common success starts the rest. -/
def Replay (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (mode : Track) (destination : RecordDestination) (inst : InstId) (compare : FieldComparison grow sig)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig) :
    List Field → Nat → Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, cursor, left, right, check, canon =>
    let slot := mode.slot destination.width item cursor
    let nextCheck := checkTail mode destination inst rest (index + 1) slot.2 checkNext
    let nextCanon := canonTail mode destination inst rest slot.2 canonNext
    let reference := focus mode destination inst item cursor right canon nextCanon
    Steps profile ready (specDispatch ready (host bindings)) right mode.readLabels reference ∧
    compare item index slot.1 left reference check canon nextCheck nextCanon
      (Replay profile ready bindings mode destination inst compare checkNext canonNext finish rest (index + 1) slot.2)

def MixedSlot (destination : RecordDestination) (bytes : Nat) (item : Field) (address : Nat) : Prop :=
  CanonicalHandle item ∨ StringField.Fits destination item ∧
    address % (layout destination.width item.type).alignment.bytes = 0 ∧ address + (layout destination.width item.type).size ≤ bytes

def mixed (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    FieldComparison grow sig := fun item index address left right check canon checkNext canonNext finish =>
  (CanonicalHandle item ∧ HandleFieldThen profile ready bindings item index (.memory address) left right check canon checkNext canonNext
    (fun () => finish)) ∨
  (∃ value : StringField, value.field = item ∧ StringFieldThen profile ready bindings older destination inst value.value (.memory address)
    left right check canon checkNext canonNext (fun () => finish))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
