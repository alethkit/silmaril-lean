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
    (destinationChecked : destination.check left.store = .ok ()) {bytes : Nat}
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
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile ready (specDispatch ready (host (grow := grow) bindings))
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback.collectionReturn destination inst
    entries area output index pointer path paired checkCursor leftAt destinationChecked sized checkNext canonNext
    checkBody canonBody compared

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
