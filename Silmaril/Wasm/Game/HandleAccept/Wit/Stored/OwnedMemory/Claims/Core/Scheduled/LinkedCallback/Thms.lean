module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints Stored.Endpoints.RecordLower
open PayloadPrefix

variable {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}
  {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}

/-- A readiness policy independent of the writer needs no agreement premise
at any reached synchronous read. -/
theorem ReadyAgreement.fixed (policy : Nat → Bool) (start : State grow sig) (inst : InstId) :
    ReadyAgreement (fun _ => policy) start inst := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- An unaligned reached pointer never enters the traversal. -/
theorem ReachedCollectionTail.unaligned (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat) (reached : State grow sig)
    (invalid : pointer ≠ alignTo pointer area.alignment) :
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer reached :=
  fun _ _ _ _ aligned => False.elim (invalid aligned)

/-- A failed fresh dry run does not need a rule for an unvisited child. -/
theorem ReachedCollectionTail.refused (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat) (reached : State grow sig) {issue}
    (refused : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .error issue) :
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer reached :=
  fun _ _ _ _ _ _ accepted => by rw [refused] at accepted; contradiction

/-- Replay a checked prefix through reached closed give callouts and synchronous
readiness observations. Each callout executes its own refusal and resumes its
actual Core continuation. The paired states retain growth evidence and visible labels. -/
theorem Prefix.replay {left right last : State grow sig} {visibleLabels}
    (path : Prefix profile ready bindings first left visibleLabels last)
    (paired : HostFrame.Paired first second left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.replay path paired

/-- Classify the actual two store reads of a live, unresolved synchronous lift
task and its readiness read. The continuation may be a choice or an empty-choice
trap: the rule does not assume the existence of a runnable thread. -/
theorem Prefix.syncLift {start last : State grow sig} {labels task thread frames rest} {entry : Task (core3 grow)}
    (focused : start.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest)
    (found : ArenaField.tasks.get? start.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : ReadyAgreement ready start entry.inst)
    (path : Prefix profile ready bindings first { start with ctl := ⟨thread,
      .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) entry.inst)), frames⟩ :: rest }
      labels last) : Prefix profile ready bindings first start labels last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.syncLift focused found waiting agrees path

/-- Replay a classified finite prefix through its observed pop. The designated
case exposes both reached continuations; an equal but unrelated frame is just
an ordinary pop. Neither branch assumes the continuation will return. -/
theorem Prefix.return_cut {left right last : State grow sig} {seen value}
    (path : Prefix profile ready bindings first left seen last) (paired : HostFrame.Paired first second left right)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure value)) :
    CallbackReturn profile ready bindings first second left right last cursor value seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.returnCut path paired cursor leftAt

/-- The next canonical string allocation installs paired saved continuations
on a common scheduler frame. `Prefix.replay` then compares a classified
callback, even if it has not returned. -/
theorem string_realloc_pair (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (checkAt : left.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left cursor
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right cursor
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Paired (stringPlanResume cx steps checkNext) (stringPlanResume cx steps canonNext) leftEntry rightEntry :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.stringReallocPair
    cx ptr oldSize alignment size steps checkNext canonNext left right cursor same checkAt canonAt

/-- The real allocate/resize steps can install another callback even while
older active and blocked frames still differ. The resulting relation is
replayable until an actual host-read or saved-return boundary. -/
theorem ChildFrameOver.string_realloc_pair {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left check
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right canon
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes (stringPlanResume cx steps checkNext)
      (stringPlanResume cx steps canonNext)) leftEntry rightEntry :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.childStringRealloc
    cx ptr oldSize alignment size steps checkNext canonNext frame checkAt canonAt

/-- A reached allocating list or map can likewise install on distinct
residual frames, keeping the memory-map placement mode and its live recheck
in the real saved continuations. -/
theorem ChildFrameOver.collection_install_pair {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let area := layout destination.width element
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left check first
    let canonCall := collectionEntry destination inst area entries.length dispatch right canon second
    Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
    Steps profile ready dispatch right [.tau, .tau] canonCall ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes first second) checkCall canonCall :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.childCollectionInstall
    destination inst type element entries output index checkNext canonNext frame reachedWidth prepared checkAt canonAt

/-- Replay to the actual child-entry cut, with the reached memory region,
live verdict and residual scheduler frames. A range trap or common pop
does not enter the child program. No child comparison or return guarantee
is a premise of this cut. -/
theorem Prefix.range_cut (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat)
    (plan : List Object) {left right last : State grow sig} {seen}
    (path : Prefix profile ready bindings first left seen last)
    (paired : HostFrame.Paired first second left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : second (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.rangeCut
    destination inst area count pointer plan path paired cursor leftAt present sized checkNext canonNext checkBody canonBody

/-- Derive entry and return cuts from the two actual dynamic-field programs.
The canonical continuation keeps the memory-map entry mode chosen at
allocation time; an allocating child can be visited next without supplying
a comparison of the entire collection suffix. -/
theorem collection_descend (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index : Nat) (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? right.store.core destination.memory = some bytes)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    CollectionDescent profile ready bindings destination inst type element entries output index left right cursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionDescent
    destination inst type element entries output index left right cursor checkNext canonNext same present sized prepared checkAt canonAt

/-- Compose the classified callback from the reached allocator entry with
the natural return at its far end. Use that reached store for range checks
and that reached writer for live claim revalidation before the child rules.
A coincidentally equal unswapped frame can also just take an ordinary pop;
in that case the machines remain paired without claiming a collection return. -/
theorem Prefix.collection_return (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    {left right last : State grow sig} {labels} (path : Prefix profile ready bindings first left labels last)
    (paired : HostFrame.Paired first second left right) (checkCursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { checkCursor with frames := .prog first :: checkCursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : second (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionReturn destination inst
    entries area output index pointer path paired checkCursor leftAt present sized checkNext canonNext
    checkBody canonBody compared

/-- Start at the two actual dynamic lowering programs. The allocator entry
and both saved continuations are derived from those programs, not supplied
as matching-callback hypotheses. The remaining path evidence classifies
only the reached checked run. Value-mode entries share the child comparisons. -/
theorem Prefix.collection (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {initial left right last : State grow sig} {before seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (prefixRun : CoreGrowthSteps profile ready (specDispatch ready (host (grow := grow) bindings)) initial before right)
    (checkedDestination : destination.check initial.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? initial.store.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last →
    CollectionCut profile ready bindings checkResume canonResume left right
      { last with ctl := reached.control (checkResume (.nat pointer)) } reached checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collection destination inst type element entries
    output index pointer cursor reached checkNext canonNext same prefixRun checkedDestination sized mode prepared checkAt canonAt

/-- Compare an admitted dynamic value-mode child from its actual emitted
programs, through a classified allocator path and the reached live recheck.
Success carries Core growth from the enclosing prefix through the entries
and descriptor. A common-frame pop remains a suspended comparison. -/
theorem Prefix.collection_memory (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {origin : CStore (core3 grow)} {left right last : State grow sig} {seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    (∀ item ∈ entries, MemoryChildRule profile ready dispatch destination inst item element) →
    CollectionCutKeeping profile ready bindings (fun store => Core3.Grows origin.core store.core)
      checkResume canonResume left right { last with ctl := reached.control (checkResume (.nat pointer)) }
      reached checkNext canonNext seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionMemory destination inst type element entries
    output index pointer cursor reached checkNext canonNext same growth memoryWidth sized mode prepared checkAt canonAt

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
