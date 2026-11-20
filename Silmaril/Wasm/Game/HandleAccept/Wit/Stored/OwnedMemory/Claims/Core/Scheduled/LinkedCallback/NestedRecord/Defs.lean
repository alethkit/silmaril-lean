module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

/-- A dynamic list field at the head of a memory record/tuple cursor. -/
structure Site where
  destination : RecordDestination
  inst : InstId
  schema : TypeOf
  element : TypeOf
  entries : List Field
  following : List Field
  base : Nat
  index : Nat

def Site.head (site : Site) : Field := .dynamic (.list site.element) site.element site.entries

def Site.fields (site : Site) : List Field := site.head :: site.following

def Site.headLayout (site : Site) : Layout := layout site.destination.width site.head.type

def Site.address (site : Site) : Nat := alignTo site.base site.headLayout.alignment

def Site.advance (site : Site) : Nat := site.address + site.headLayout.size

def Site.entryLayout (site : Site) : Layout := layout site.destination.width site.element

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

def Site.checkedTail (site : Site) : Session grow sig (Except RecordLower.Issue Unit) :=
  Record.Effects.memory recordClaims Limits.spec Quirks.none (site.destination.context site.inst)
    site.destination.width site.following site.advance (site.index + 1)

def Site.canonicalTail (site : Site) : Session grow sig Unit :=
  CanonicalTree.memory Limits.spec Quirks.none (site.destination.context site.inst)
    site.destination.width site.following site.advance

abbrev CheckNext (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))

abbrev CanonNext (grow : SingleThreaded.GrowOracle) (sig : Signature) := Unit → Session grow sig (Ret (core3 grow))

def Site.checkResume (site : Site) (finish : CheckNext grow sig) : ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  checkedCollectionResume site.destination site.inst site.entries site.entryLayout site.index (.memory site.address)
    (checkedSequenceNext id (fun _ => site.checkedTail) finish)

def Site.canonResume (site : Site) (finish : CanonNext grow sig) : ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  canonicalCollectionResume site.destination site.inst site.entries site.entryLayout (.memory site.address)
    (fun _ => site.canonicalTail >>= finish)

/-- The region established by the compiled aggregate's enclosing guard. -/
structure Site.Region (site : Site) (origin : CStore (core3 grow)) (bytes : Nat) : Prop where
  layoutMatch : Field.LayoutMatches (.aggregate site.schema site.fields) site.schema
  width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width
  sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes
  aligned : (layout site.destination.width site.schema).alignment.bytes ∣ site.base
  fits : site.base + (layout site.destination.width site.schema).size ≤ bytes

/-- A failed initial check refuses before allocation. An admitted head is
compared only along a supplied, actually reached callback cut; it need not
return. A common-frame pop does not advance the enclosing record cursor. -/
def Site.Outcome (site : Site) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (origin : CStore (core3 grow))
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) : Prop :=
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows origin.core store.core
  match Record.prepare left.store left.host.writer (Field.listObjects site.entries) with
  | .error _ => ReachesKeeping profile ready dispatch keep left right cursor cursor checkNext canonNext
  | .ok () =>
    let checkResume := site.checkResume checkNext
    let canonResume := site.canonResume canonNext
    let call := collectionEntry site.destination site.inst site.entryLayout site.entries.length dispatch left cursor checkResume
    (∀ (last : State grow sig) (seen : List (Label (core3 grow) (HostState sig))),
      Prefix profile ready bindings checkResume call seen last →
      ∃ checkLabels canonLabels other,
        Steps profile ready dispatch left checkLabels last ∧ Steps profile ready dispatch right canonLabels other ∧
        HostFrame.Paired checkResume canonResume last other ∧
        visible checkLabels = seen ∧ visible canonLabels = seen ∧ keep last.store) ∧
    (∀ (pointer : Nat) (last : State grow sig) (seen : List (Label (core3 grow) (HostState sig)))
        (reached : Cursor (E := core3 grow) (HostState sig)),
      Prefix profile ready bindings checkResume call seen last →
      last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
      CollectionCutKeeping profile ready bindings keep checkResume canonResume left right
        { last with ctl := reached.control (checkResume (.nat pointer)) } reached checkNext canonNext seen)

def publicSite {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer))
    (element : TypeOf) (entries following : List Field) : Site :=
  ⟨call.destination, call.inst, sig.payload call.tag, element, entries, following, flatNat pointer, 0⟩

def publicReply {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer)) : CheckNext grow sig :=
  fun verdict => call.reply (verdict.mapError (.nested 0))

def publicBody {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer)) (site : Site) :
    Session grow sig (Ret (core3 grow)) :=
  Record.Effects.memory recordClaims Limits.spec Quirks.none (site.destination.context site.inst)
    site.destination.width site.fields site.base site.index >>= publicReply call

/-- A public checked-only stop at admission or placement, or a comparison at
the compiled memory body with the original parked caller and reply ticket. -/
def PublicOutcome {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer))
    (element : TypeOf) (entries following : List Field) (next : call.ReferenceNext)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  let site := publicSite call element entries following
  let entered := call.withBody (publicBody call site)
  PayloadRoot.Cut call profile ready bindings
    (Steps profile ready (specDispatch ready (host (grow := grow) bindings)) call.checked [.tau] entered ∧
      site.Outcome profile ready bindings call.start.store entered (call.reference next) call.cursor (publicReply call) next)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord
