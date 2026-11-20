module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core

variable {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}
  {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}

/-- Replay a checked prefix through any finite number of reached closed give
callouts. Each callout executes its own refusal and resumes its actual Core
continuation; the paired states retain growth evidence and visible labels. -/
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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
