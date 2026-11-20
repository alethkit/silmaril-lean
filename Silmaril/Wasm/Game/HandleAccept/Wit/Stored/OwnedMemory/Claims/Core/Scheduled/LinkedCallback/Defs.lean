module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core

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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
