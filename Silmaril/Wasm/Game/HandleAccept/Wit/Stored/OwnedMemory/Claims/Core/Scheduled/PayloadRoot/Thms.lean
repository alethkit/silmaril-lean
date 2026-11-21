module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Either public give reaches a typed refusal, traps at the ABI placement
guard, or enters the compiled effect body with the real reply continuation. -/
theorem Site.parked (site : Site grow sig route) (linked : site.Linked bindings) : Cut site profile ready bindings :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.parked site linked

/-- Use the actual public allocation guard only on the placed branch.
The refusal and placement-trap branches never require a body comparison. -/
theorem Site.parked_after_fit (site : Site grow sig route) (linked : site.Linked bindings) (body : Prop)
    (afterFit : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
      site.payload.val.value = true → body) : Cut site profile ready bindings body :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.parkedAfterFit site linked body afterFit

theorem Site.reference_at (site : Site grow sig route) (linked : site.Linked bindings) (next : site.ReferenceNext) :
    (site.reference next).ctl = site.cursor.control
      (CanonicalTree.field Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
        site.field route.output >>= next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.referenceAt site bindings linked next

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot
