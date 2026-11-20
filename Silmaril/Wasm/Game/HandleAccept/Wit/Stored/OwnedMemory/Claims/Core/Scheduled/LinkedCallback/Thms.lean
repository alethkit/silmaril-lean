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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
