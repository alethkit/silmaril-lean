module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

theorem lower_preflight_error {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type)
    (output : Stored.Lower.Output) {issue : Issue}
    (reject : preflight cx type payload output = .error issue) :
    (lower limits quirks cx type payload output : P E (State sig) _) = pure (.error issue) := by
  simp only [lower, reject]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
