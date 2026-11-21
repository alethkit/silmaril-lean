module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {schema : TypeOf}

/-- A structural certificate, not a run-time bound or an allocation guard.
Leaves are strings; the traversed branches are records, tuples or fixed lists. -/
def Shape (depth : Nat) (field : Field) : Prop :=
  FlatNestedFits (fun field => ∃ item : StringField, item.field = field) depth field

/-- The parked call has no substituted frames to begin with. Its checked
continuation keeps the original reply ticket. Reaching that continuation
is distinct from delivering the reply or any pending event. -/
def Body (call : PayloadRoot.Site grow sig (.flat schema)) (depth : Nat) (next : call.ReferenceNext)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  let compare := nestedFlatComparison (stringFlatComparison profile ready bindings older call.destination call.inst)
    older call.destination call.inst depth
  compare call.field 0 call.checked (call.reference next) call.cursor call.cursor call.reply next
    (fun words reached reference check canon => ChildFrameOver older reached reference check canon ∧
      reached.ctl = check.control (call.reply (.ok words)) ∧ reference.ctl = canon.control (next words))

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings
