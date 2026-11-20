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

/-- After the initial dry run admits this collection, the actual recursive
programs install the same allocator request; a certified scheduler prefix
preserves the checked width. The saved checked continuation
validates range first and then re-reads the live plan. `mode` excludes the
memory-map case, whose entry offsets use allocation-time placement. -/
theorem collection_install (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    {initial labels} (prefixRun : CoreGrowthSteps profile ready dispatch initial labels right)
    (checkedDestination : destination.check initial.store = .ok ())
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let cx := destination.context (grow := grow) inst
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig),
      let active := fun resume => ({ cursor with frames := .prog resume :: cursor.frames }).control (dispatch request)
      let checkCall := { left with ctl := active checkResume }
      let canonCall := { right with ctl := active canonResume }
      (∀ pointer, checkResume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
        checkedCollectionTail destination inst entries area index output ptr live >>= checkNext)) ∧
      (∀ pointer, canonResume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        canonicalCollectionTail destination inst entries area output ptr >>= canonNext)) ∧
      Machine.Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
      Machine.Steps profile ready dispatch right [.tau, .tau] canonCall ∧
      HostFrame.Paired checkResume canonResume checkCall canonCall :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionInstall
    destination inst type element entries output index left right cursor checkNext canonNext same prefixRun
    checkedDestination mode prepared checkAt canonAt

/-- From an actual paired return, use the reached memory and live writer.
Invalid ranges trap on both sides. A typed live refusal leaves the reference
before the element traversal. Otherwise compose the reached child rules and
the real descriptor, including a possible trap after its pointer write. -/
theorem collection_return (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionReturn
    destination inst entries area output index pointer left right checkCursor canonCursor checkNext canonNext
    checkResume canonResume paired sameThread leftAt rightAt checkBody canonBody sized compared

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
