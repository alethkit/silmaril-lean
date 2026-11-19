module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Async.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Async.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine}

def initial (body : P E Unit (Ret E)) : Machine.Config E Unit where
  store := { CStore.empty with
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := ()
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) body]

def noHostReady : HostReady Unit := fun _ _ => false

def noForeignCalls (_ : Canon.Call E) : P E Unit (Ret E) :=
  internal "unexpected foreign call in endpoint session"

def invoke (call : Async.Call E) := call.program (World := Unit) Component.Limits.spec Quirks.none

/-- The unit future writer initially blocks. The read makes the writer ready, then
delivering that completion lets both ends close without leaving a table entry. -/
def futureSession : P E Unit (Ret E) := do
  let _ ← invoke (.create .future none)
  let writable ← Endpoint.inspect .writableFuture none ⟨0⟩ 2
  let writeReply ← invoke (.futureCopy .write none { async_ := true } 2 0)
  trapIf (writeReply != [i32Flat blocked]) (.internal "future write did not block")
  let readReply ← invoke (.futureCopy .read none {} 1 0)
  trapIf (readReply != [i32Flat (futureCopyPayload .completed)]) (.internal "future read did not complete")
  trapIf (!(← Runtime.Waitable.hasPendingEvent (.end_ writable.id))) (.internal "no future write ready")
  let completed ← Runtime.Waitable.getPendingEvent (.end_ writable.id)
  trapIf (completed.payload != futureCopyPayload .completed) (.internal "future write did not complete")
  let _ ← invoke (.close .future .read none 1)
  let _ ← invoke (.close .future .write none 2)
  pure .unit

def run (X : E.Exec) (body : P E Unit (Ret E)) :=
  Machine.run noHostReady noForeignCalls X Machine.Oracle.first 128 (initial body)

theorem future_session_resolves_and_releases_slots (X : E.Exec) :
    let result := run X futureSession
    (result.outcome, (result.config.store.insts.get? 0).map (fun inst =>
      (inst.handles.get? 1, inst.handles.get? 2))) = (.resolved, some (none, none)) := by
  dsimp only
  kernel_rfl

theorem future_session_sound (X : E.Exec) :
    Machine.Steps .deterministic noHostReady noForeignCalls (initial (futureSession (E := E)))
      (run X futureSession).labels (run X futureSession).config :=
  Machine.run_sound noHostReady noForeignCalls X Machine.Oracle.first 128 (initial futureSession)

def closedSlotSession : P E Unit (Ret E) := do
  let _ ← invoke (.create .stream none)
  let _ ← invoke (.close .stream .read none 1)
  let _ ← Endpoint.inspect .readableStream none ⟨0⟩ 1
  pure .unit

theorem closed_slot_traps (X : E.Exec) :
    (run X closedSlotSession).labels.any (fun label => match label with
      | .trap (.unknownHandle 1) => true
      | _ => false) = true := rfl

/-- Cancelling a pending stream read returns its cancellation result and releases the buffer.
The same endpoint can then close normally. -/
def cancellationSession : P E Unit (Ret E) := do
  let _ ← invoke (.create .stream none)
  let readReply ← invoke (.streamCopy .read none { async_ := true } 1 0 2)
  trapIf (readReply != [i32Flat blocked]) (.internal "stream read did not block")
  let cancelReply ← invoke (.cancel .stream .read none true 1)
  trapIf (cancelReply != [i32Flat (packStreamCopyResult .cancelled 0)])
    (.internal "stream read did not cancel")
  let _ ← invoke (.close .stream .read none 1)
  let _ ← invoke (.close .stream .write none 2)
  pure .unit

theorem cancellation_session_resolves (X : E.Exec) :
    (run X cancellationSession).outcome = .resolved := by kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Async.Examples
