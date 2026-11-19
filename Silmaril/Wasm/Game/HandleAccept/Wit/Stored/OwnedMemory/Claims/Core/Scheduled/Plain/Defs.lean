module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (LocalIssue)

/-- Evaluate the non-suspending body of a checked import after dispatch admits the
caller. Only the store and host-state operations are handled; every other request
is rejected explicitly and retains all preceding effects. -/
def runBody {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (reference : CStore E) (host : Host) : CStore E × Host × Except LocalIssue Result :=
  match body with
  | .pure result => (reference, host, .ok result)
  | .op op next =>
    match op with
    | .get => runBody (next reference) reference host
    | .modify update => runBody (next ()) (update reference) host
    | .hostGet => runBody (next host) reference host
    | .hostSet updated => runBody (next ()) reference updated
    | .trap reason => (reference, host, .error (.trapped reason))
    | .choose _ => (reference, host, .error .choice)
    | .callCore _ _ => (reference, host, .error .coreCall)
    | .call _ => (reference, host, .error .canonicalCall)
    | .currentThread | .newThread _ | .block _ | .resumeThread _ =>
      (reference, host, .error .scheduling)
    | .emit _ => (reference, host, .error .hostEffect)
termination_by structural body

/-- The endpoint-only diagnostic matched by a scheduled receipt-aware refusal.
`none` does not turn a new diagnostic into old success. -/
def oldIssue : Issue → Option Endpoints.Core.Scheduled.Issue
  | .accept issue => Core.Plain.oldIssue issue |>.map .accept
  | .wrongContext => some .wrongContext
  | .wrongType => some .wrongType
  | .ambiguousBinding => some .ambiguousBinding
  | .badSelection => some .badSelection
  | _ => none

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain
