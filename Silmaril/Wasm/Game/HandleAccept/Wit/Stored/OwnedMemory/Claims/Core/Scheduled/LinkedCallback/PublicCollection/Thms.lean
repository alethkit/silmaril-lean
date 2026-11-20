module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

/-- Both parked public give routes reach the actual dynamic collection allocator
or stop before allocation. On a classified callback path, the return comparison
uses reached memory bounds and rechecks live claims before the child traversal. -/
theorem Site.parked {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature}
    (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings) :
    Outcome site profile ready bindings next (site.ChildrenCompare profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection.parked site profile ready bindings next linked id

/-- For a dynamic list of handles, the placed children need no additional
comparison premise. The actual leaf programs can still refuse or trap. -/
theorem Site.parked_handles {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature}
    (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    (handles : ∀ item ∈ site.entries, CanonicalHandle item) : Outcome site profile ready bindings next True :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection.parked site profile ready bindings next linked
    (fun _ item member address pos => PayloadPrefix.memory_handle site.destination site.inst item pos address (handles item member))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection
