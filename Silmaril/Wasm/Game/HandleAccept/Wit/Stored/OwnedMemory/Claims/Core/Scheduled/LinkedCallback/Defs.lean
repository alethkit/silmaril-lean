module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open PayloadPrefix
open Stored.Endpoints.RecordLower (Object Field)

abbrev State (grow : SingleThreaded.GrowOracle) (sig : Signature) := Config (core3 grow) (HostState sig)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- Evidence for a give import actually reached within a closed instance.
It includes the reached caller and binding, not agreement of the two writers. -/
structure ClosedGive (bindings : List (Binding sig)) (start : State grow sig) where
  name : String
  type : V1.FuncType
  args : List FlatValue
  inst : InstId
  destination : RecordDestination
  schema : Option TypeOf
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  entry : InstState
  parked : start.ctl = ⟨thread, .core core next, frames⟩ :: rest
  calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args
  linked : resolveBinding bindings name type = .ok ⟨name, inst,
    schema.elim (.givePayload destination) (.giveFlat destination)⟩
  caller : Plain.callerInstance start.store thread = .ok (some inst)
  live : start.store.inst? inst = some entry
  closed : entry.mayLeave = false

/-- The checked path records its own ticketed refusal and resumes the actual
Core activation. The allocator's original saved continuation stays parked. -/
def ClosedGive.resume {bindings : List (Binding sig)} {start : State grow sig}
    (callout : ClosedGive bindings start) : State grow sig :=
  let reply := callout.schema.elim (completion start.host.nextTicket (.error .wrongContext))
    (fun payload => flatCompletion start.host.nextTicket (ABI.flatten callout.destination.width payload)
      (.error .wrongContext))
  { start with
    host := (start.host.enter callout.name callout.type callout.args).record reply.1
    ctl := ⟨callout.thread,
      .core ((core3 grow).resume start.store.core callout.core (.values reply.2)) callout.next,
      callout.frames⟩ :: callout.rest }

/-- Only host predicates consulted when filtering this reached instance's
blocked threads must be independent of the writer. Host-independent readiness
policies satisfy this without any invariant on claim, ticket, or journal data. -/
def ReadyAgreement (ready : HostReady (HostState sig)) (start : State grow sig) (inst : InstId) : Prop :=
  ∀ entry, start.store.inst? inst = some entry → ∀ thread ∈ entry.threads.elements,
    ∀ suspended, start.store.thread? thread = some suspended → suspended.blocked = true →
      ∀ query, suspended.readyCond = some (.host query) → ∀ other, ready start.host query = ready other query

/-- A finite checked callback prefix described by reached scheduler steps and
classified linked reentries. It is indexed by visible labels, not a shared
count of internal steps. Unclassified reads are not replayed by this relation. -/
inductive Prefix (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) :
    State grow sig → List (Label (core3 grow) (HostState sig)) → State grow sig → Prop where
  | done (cfg : State grow sig) : Prefix profile ready bindings resume cfg [] cfg
  | step {start next last : State grow sig} {label labels} :
      HostFrame.Interior resume start → CoreUpdateGrows start →
      Step profile ready (specDispatch ready (host (grow := grow) bindings)) start label next →
      Prefix profile ready bindings resume next labels last →
      Prefix profile ready bindings resume start (PayloadPrefix.visible [label] ++ labels) last
  | closedGive {start last : State grow sig} {labels} (callout : ClosedGive bindings start) :
      Prefix profile ready bindings resume callout.resume labels last →
      Prefix profile ready bindings resume start labels last
  | syncReady {start last : State grow sig} {labels task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : ReadyAgreement ready start inst) :
      Prefix profile ready bindings resume { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest }
        labels last →
      Prefix profile ready bindings resume start labels last

/-- Continue a designated allocator return using its measured width and size.
The tail rule receives the alignment, bounds, and live-plan facts only after
the corresponding checks actually accept. -/
def ReachedCollectionTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (destination : RecordDestination) (inst : InstId)
    (entries : List Stored.Endpoints.RecordLower.Field) (area : Layout) (output : Stored.Lower.Output)
    (index pointer : Nat) (checked : State grow sig) : Prop :=
  ∀ (reference : State grow sig) (bytes : Nat),
    ptrTypeIn checked.store (destination.context inst) = destination.width →
    (core3 grow).memSize? checked.store.core destination.memory = some bytes →
    PayloadPrefix.CollectionTailAt profile ready (specDispatch ready (host bindings)) destination inst entries area
      output index pointer bytes checked reference

/-- The observed pop was of an unchanged frame and the two allocator
executions are still paired. -/
def CollectionCommonPop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right afterPop : State grow sig) (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  ∃ leftLabels rightLabels other,
    Steps profile ready dispatch left leftLabels afterPop ∧ Steps profile ready dispatch right rightLabels other ∧
    HostFrame.Paired first second afterPop other ∧
    PayloadPrefix.visible leftLabels = seen ∧ PayloadPrefix.visible rightLabels = seen

/-- The frame at a reached child entry. Blocked activations and the cursor
tails can still contain substituted return frames; only the store and the
pending, result, and cancellation data must be equal. -/
structure ChildFrame (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig)) : Prop where
  store : left.store = right.store
  pending : left.pending = right.pending
  results : left.results = right.results
  cancels : left.cancels = right.cancels
  blocked : List.Forall₂ (ReturnFrame.Saved first second) left.conts right.conts
  thread : check.thread = canon.thread
  frames : List.Forall₂ (ReturnFrame.Segment first second) check.frames canon.frames
  rest : List.Forall₂ (ReturnFrame.Active first second) check.rest canon.rest

/-- A classified callback has reached a pop. Only a pop of the substituted
frame enters the two distinct continuations. No validation or tail code
has run yet, and both continuations use their reached stores. -/
inductive CallbackReturn (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (value : Ret (core3 grow)) (seen : List (Label (core3 grow) (HostState sig))) : Prop where
  | designated {reference : State grow sig} {canonCursor : Cursor (E := core3 grow) (HostState sig)}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (frame : ChildFrame first second last reference cursor canonCursor)
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (first value) })
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right canonLabels
        { reference with ctl := canonCursor.control (second value) })
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      CallbackReturn profile ready bindings first second left right last cursor value seen
  | common {reference : State grow sig} {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (checked : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (first value) })
      (canonical : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right canonLabels reference)
      (paired : HostFrame.Paired first second { last with ctl := cursor.control (first value) } reference)
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      CallbackReturn profile ready bindings first second left right last cursor value seen

/-- The actual activation entered by one canonical string allocation step. -/
def stringReallocEntry (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat)
    (steps : List StoreStep) (finish : Nat → Session grow sig (Ret (core3 grow)))
    (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) : State grow sig :=
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  let entered := { cursor with frames := .prog (stringPlanResume cx steps finish) :: cursor.frames }
  { start with ctl := entered.control (specDispatch ready (host bindings) request) }

/-- Stop at the reached range/recheck cut without executing any children.
On a valid range the checked continuation receives the real live verdict
(which can refuse); the canonical continuation receives only the pointer.
Neither side rewinds callback effects. -/
inductive RangeCut (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : Layout) (count pointer : Nat) (plan : List Object)
    (checkNext : Nat → Except Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) (seen : List (Label (core3 grow) (HostState sig))) : Prop where
  | reached {reference : State grow sig} {canonCursor : Cursor (E := core3 grow) (HostState sig)} {bytes : Nat}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (width : (core3 grow).memAddrType? last.store.core destination.memory = some destination.width)
      (sized : (core3 grow).memSize? last.store.core destination.memory = some bytes)
      (aligned : pointer = alignTo pointer area.alignment) (bounds : pointer + count * area.size ≤ bytes)
      (frame : ChildFrame first second last reference cursor canonCursor)
      (growth : Core3.Grows left.store.core last.store.core)
      (checked : Steps profile ready (specDispatch ready (host bindings)) left checkLabels
        { last with ctl := cursor.control (checkNext pointer (Record.prepare last.store last.host.writer plan)) })
      (canonical : Steps profile ready (specDispatch ready (host bindings)) right canonLabels
        { reference with ctl := canonCursor.control (canonNext pointer) })
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen
  | trapped {reference : State grow sig} {reason : TrapReason}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (stores : last.store = reference.store)
      (checked : Steps profile ready (specDispatch ready (host bindings)) left checkLabels (StepDefs.trapCfg last))
      (canonical : Steps profile ready (specDispatch ready (host bindings)) right canonLabels (StepDefs.trapCfg reference))
      (checkSeen : visible checkLabels = seen ++ [.trap reason]) (canonSeen : visible canonLabels = seen ++ [.trap reason]) :
      RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen
  | common (pop : CollectionCommonPop profile ready bindings first second left right
      { last with ctl := cursor.control (first (.nat pointer)) } seen) :
      RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen

/-- Allocator descent from the two actual dynamic-field programs. The cut
hands the entry interpreters back to the caller rather than requiring
that any allocating descendants return. -/
def CollectionDescent (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf) (entries : List Field)
    (output : Stored.Lower.Output) (index : Nat) (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) : Prop :=
  let dispatch := specDispatch ready (host bindings)
  let area := layout destination.width element
  let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext mode
  let installed := collectionEntry destination inst area entries.length dispatch left cursor first
  let reference := collectionEntry destination inst area entries.length dispatch right cursor second
  Steps profile ready dispatch left [.tau, .tau, .tau] installed ∧
  Steps profile ready dispatch right [.tau, .tau] reference ∧
  HostFrame.Paired first second installed reference ∧
  ∀ {last seen}, Prefix profile ready bindings first installed seen last →
    ∀ (reached : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat),
      last.ctl = { reached with frames := .prog first :: reached.frames }.control (pure (.nat pointer)) →
      RangeCut profile ready bindings first second installed reference last reached destination area entries.length pointer
        (Field.listObjects entries)
        (fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext)
        (fun ptr => canonicalCollectionTail destination inst entries area output ptr mode >>= canonNext) seen

/-- Either the collection comparison has reached its continuations (or a
refused/trapping prefix), or the observed pop was of an unchanged frame. -/
def CollectionCut {Result : Type} (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right afterPop : State grow sig) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  (∃ canonCursor, canonCursor.thread = cursor.thread ∧
    PayloadPrefix.Reaches profile ready dispatch left right cursor canonCursor checkNext canonNext) ∨
  CollectionCommonPop profile ready bindings first second left right afterPop seen

/-- A cut that supplies a reached continuation invariant on successful
completion, without treating other cuts as completion. -/
def CollectionCutKeeping {Result : Type} (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (keep : CStore (core3 grow) → Prop)
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (left right afterPop : State grow sig) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (seen : List (Label (core3 grow) (HostState sig))) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  (∃ canonCursor, canonCursor.thread = cursor.thread ∧
    PayloadPrefix.ReachesKeeping profile ready dispatch keep left right cursor canonCursor checkNext canonNext) ∨
  CollectionCommonPop profile ready bindings first second left right afterPop seen

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
