module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints
open Stored.Endpoints.RecordLower

/-- Compose actual paired scheduler prefixes at the reached store. Only a
successful child advances either traversal; refusal and trap retain the
child's prefixes. -/
theorem Compare.bind {E : CoreEngine} {Host Result Next : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (rest : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with | .error issue => pure (.error issue) | .ok value => checkTail value)
      (canonical >>= canonTail) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.sequential first checkTail canonTail rest

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

/-- Compare the actual flat lowering programs recursively for records,
tuples, fixed lists and well-tagged sums made from own, stream, future and
error-context leaves. The writers need not agree: each checked leaf re-reads
its live writer. -/
theorem flat_field (destination : RecordDestination) (inst : InstId) (item : Field)
    (fragment : HandleField item) (index : Nat) :
    Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.flatField destination inst item fragment index

/-- Compose a selected arm comparison with the actual flat coercion and
padding program. Coercion runs only on common success, and its canonical
choices and traps stay visible on both sides. -/
theorem flat_sum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index : Nat) (selected : Option Field) (valid : tag < arms.length)
    (child : ∀ item, selected = some item → Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat)) :
    Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) .flat) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.flatSum
    destination inst type arms tag index selected valid child

/-- The canonical side reads width at this cursor. Both sides write the
actual discriminant, then enter the selected child at the computed address
only if the write returns. A later refusal does not undo the tag write. -/
theorem memory_sum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index ptr : Nat) (selected : Option Field)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn right.store (destination.context inst) = destination.width)
    (child : ∀ item address, selected = some item → Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CompareAt profile ready dispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) (.memory ptr)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memorySum
    destination inst type arms tag index ptr selected left right width child

/-- The compiler's layout certificate supplies the tag bounds at every
selected sum in the handle-only fragment. -/
theorem checked_fragment {field : Field} {type : TypeOf} (layout : Field.LayoutMatches field type)
    (shape : HandleShape field) : HandleField field :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.certifyField layout shape

/-- The linked public `giveFlat` call reaches the same flat words as
`lowerFlatAt` for compiled handle-only aggregates, fixed lists and sums, or
stops at a typed refusal or common canonical trap. The same canonical choice
answers are recorded on both sides. Returned verdicts reach the
original ticketed reply program, not a claim that the enclosing export returns. -/
theorem parked_giveFlat (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (destination : RecordDestination) (inst : InstId) (schema : TypeOf)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleShape field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .giveFlat destination schema⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (schemaChecked : rootHasSchema (.tag ⟨tag, payload⟩ arity children) schema = true)
    (canonicalAt : reference.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile ready (specDispatch ready (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (flatReply destination schema start.host.nextTicket) canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.parkedFlat
    bindings name type handleWord destination inst schema tag payload children field plan compiled fragment start reference
    sameStore canonCursor canonNext sameThread parked calling linked caller mayLeave destinationChecked selected
    schemaChecked canonicalAt

/-- The public indirect route pairs its compiled handle leaf or selected
handle sum with actual `Canon.store`. The linked check establishes the width;
the checked route's extra alignment and bounds guards may trap before the
reference starts, since raw `store` treats placement as a precondition. -/
theorem parked_givePayload (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (pointer : FlatValue) (destination : RecordDestination) (inst : InstId)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory (flatNat pointer)) = .ok (field, plan)) (fragment : MemoryHandleRoot field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord, pointer])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .givePayload destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (pointerChecked : Stored.flatType pointer = pointerType destination.width)
    (canonicalAt : reference.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) (flatNat pointer) >>= canonNext)) :
    MemoryReaches profile ready (specDispatch ready (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (memoryReply destination pointer start.host.nextTicket) canonNext
      (placement destination start.store (layout destination.width (sig.payload tag)) (flatNat pointer)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.parkedMemory
    bindings name type handleWord pointer destination inst tag payload children field plan compiled fragment start reference
    sameStore canonCursor canonNext sameThread parked calling linked caller mayLeave destinationChecked selected
    pointerChecked canonicalAt

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
