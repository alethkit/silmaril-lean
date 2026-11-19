module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints

theorem lower_preflight_error {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) {issue : RecordLower.Issue}
    (reject : preflight cx type payload output = .error issue) :
    lower access limits quirks cx type payload output = pure (.error issue) := by
  simp only [lower, RecordLower.Internal.lowerCompiled, RecordLower.Internal.lowerWithPlan, reject]

theorem lowerValue_preflight_error {E : CoreEngine} {World : Type} {sig : Signature}
    (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (payload : Payload type) (output : Stored.Lower.Output) {issue : RecordLower.Issue}
    (reject : preflightValue cx type payload output = .error issue) :
    lowerValue access limits quirks cx type payload output = pure (.error issue) := by
  simp only [lowerValue, RecordLower.Internal.lowerWithPlan, reject]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
