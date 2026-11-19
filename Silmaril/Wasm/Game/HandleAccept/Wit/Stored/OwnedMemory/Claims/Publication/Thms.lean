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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
