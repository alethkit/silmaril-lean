module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Publication.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- Successive writer actions never publish a nominal owner twice. Spending an owner or reusing
an endpoint does not change this history. -/
theorem WriterRun.published_owners_unique {before after : State sig} (run : WriterRun before after)
    (unique : before.publishedOwners.Nodup) : after.publishedOwners.Nodup :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.run_preserves run unique

/-- Every held receipt continues to come from the publication history. -/
theorem WriterRun.claims_backed {before after : State sig} (run : WriterRun before after)
    (backed : before.ClaimsBacked) : after.ClaimsBacked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.run_backed run backed

/-- A checked give or drop reads the nominal type and representation of the exact
published receipt it will spend; a matching representation alone is not evidence. -/
theorem prepare_from_published_root {state spent : State sig} {resource : RtId}
    {id : HandleObjId} {representation : Nat} (backed : state.ClaimsBacked)
    (success : state.prepare resource id = .ok (representation, spent)) :
    ∃ tree ∈ state.accepted, ∃ receipt ∈ rootReceipts tree,
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.prepared_from_history backed success

/-- Committing the prepared writer state retires the published identity, even though
the accepted tree and all of its observations remain available. -/
theorem prepare_retires {state spent : State sig} {resource : RtId} {id : HandleObjId} {representation : Nat}
    (backed : state.ClaimsBacked) (success : state.prepare resource id = .ok (representation, spent)) :
    spent.retiredOwner id :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.prepared_retires backed success

/-- Retrying a retired owner after arbitrary checked writer actions is still a typed
refusal, even if the requested nominal type is different. -/
theorem WriterRun.retired_owner_refuses {before after : State sig} {id : HandleObjId}
    (run : WriterRun before after) (retired : before.retiredOwner id) (resource : RtId) :
    after.prepare resource id = .error .unclaimed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.retired_refuses
    (run.owner_retired retired) resource

/-- The checked component scheduler preserves root-publication uniqueness across arbitrary
export prefixes, including rejected calls, canonical traps and deferred cancellation. -/
theorem ComponentCall.Deferred.published_owners_unique (bindings : List (Binding sig))
    (callees : List (ComponentCall.Callee sig)) (deferred : List HostFuncId) (control : String)
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (ComponentCall.Deferred.hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    (unique : state.writer.publishedOwners.Nodup) : final.host.writer.publishedOwners.Nodup :=
  (ComponentCall.Deferred.checked_of_session bindings callees deferred control store state steps ordinary).2.1
    |>.published_owners_unique unique

/-- Across arbitrary checked export prefixes, every held owner is backed by a published
receipt. This includes prefixes ending at a refusal, canonical trap, or cancellation. -/
theorem ComponentCall.Deferred.claims_backed (bindings : List (Binding sig))
    (callees : List (ComponentCall.Callee sig)) (deferred : List HostFuncId) (control : String)
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (ComponentCall.Deferred.hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    (backed : state.writer.ClaimsBacked) : final.host.writer.ClaimsBacked :=
  (ComponentCall.Deferred.checked_of_session bindings callees deferred control store state steps ordinary).2.1
    |>.claims_backed backed

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
