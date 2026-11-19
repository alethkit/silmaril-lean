module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

private def resource : RtId := ⟨0⟩

private def sig : Signature :=
  ⟨Bool, fun mixed => if mixed then .result (some (.own resource)) (some (.future none))
    else .tuple [.own resource, .own resource], fun _ => .fixed 0⟩

private abbrev World := State sig

private def limits : Component.Limits := Component.Limits.spec

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0 }, inst := ⟨0⟩ }

private noncomputable def acquire : P Mock.mock World Unit := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let .error .needsEndpointClaims ← acceptNode sig limits Quirks.none context true
    (.flat [i32Flat 0, i32Flat 1]) [] | internal "inactive endpoint schema was accepted"
  let .ok _ ← acceptNode sig limits Quirks.none context false (.flat [i32Flat 1, i32Flat 2]) []
    | internal "the two owned leaves were not accepted"

private noncomputable def destructor (id : HandleObjId) (inst : InstId)
    (request : DtorRequest Mock.mock) : P Mock.mock World Unit := do
  let state ← hostGet
  if state.held.any (fun receipt => receiptId receipt == id) then
    internal "destructor entered before consuming its claim"
  else if inst != ⟨0⟩ || request.rt != resource || request.rep != 77 then
    internal "incorrect destructor request"
  else pure ()

private noncomputable def roundTrip : P Mock.mock World (Ret Mock.mock) := do
  acquire
  let .error .wrongResourceType ← give limits context ⟨1⟩ ⟨0⟩
    | internal "nominal type mismatch did not reject"
  let .ok 2 ← give limits context resource ⟨0⟩
    | internal "the guest handle was not reissued"
  let .error .unclaimed ← give limits context resource ⟨0⟩
    | internal "spent claim could be given again"
  let .ok () ← drop (destructor ⟨1⟩) resource ⟨1⟩
    | internal "the other owner was not dropped"
  let .error .unclaimed ← drop (destructor ⟨1⟩) resource ⟨1⟩
    | internal "spent claim could be dropped again"
  pure .unit

private noncomputable def trapDuringDrop : P Mock.mock World (Ret Mock.mock) := do
  acquire
  let _ ← drop (fun inst request => do
    destructor ⟨1⟩ inst request
    trap (.unknownHandle 42)) resource ⟨1⟩
  pure .unit

private noncomputable def reacquire : P Mock.mock World (Ret Mock.mock) := do
  let _ ← roundTrip
  let _ ← Builtins.resourceNew limits resource 77
  let .ok _ ← acceptNode sig limits Quirks.none context false (.flat [i32Flat 2, i32Flat 1]) []
    | internal "fresh owner identities in reused guest slots were not accepted"
  let .error .unclaimed ← drop (destructor ⟨0⟩) resource ⟨0⟩
    | internal "reacquisition revived the old claim"
  let .ok () ← drop (destructor ⟨2⟩) resource ⟨2⟩
    | internal "the reacquired owner was not dropped"
  pure .unit

private noncomputable def initial (program : P Mock.mock World (Ret Mock.mock)) :
    Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ByteArray.empty⟩] }
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := {}
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) program]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock World (Ret Mock.mock) :=
  internal "unexpected component call"

private noncomputable def run (X : Mock.mock.Exec) (program : P Mock.mock World (Ret Mock.mock)) :=
  Machine.run noReady noCalls X Machine.Oracle.first 256 (initial program)

theorem machine_session_sound (X : Mock.mock.Exec) :
    Machine.Steps .deterministic noReady noCalls (initial roundTrip)
      (run X roundTrip).labels (run X roundTrip).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 256 (initial roundTrip)

theorem give_and_drop_spend_distinct_equal_rep_owners_once (X : Mock.mock.Exec) :
    let result := run X roundTrip
    (result.outcome, result.config.host.accepted.length, result.config.host.held.map receiptId,
      (result.config.store.insts.get? 0).bind (fun inst => inst.handles.get? 2)) =
      (.resolved, 1, [], some (.resource ⟨2⟩)) := by
  dsimp only
  kernel_rfl

theorem reacquire_reused_slots_without_reviving_spent_claims (X : Mock.mock.Exec) :
    let result := run X reacquire
    (result.outcome, result.config.host.accepted.length, result.config.host.held.map receiptId) =
      (.resolved, 2, [⟨3⟩]) := by
  dsimp only
  kernel_rfl

theorem trapping_destructor_keeps_other_owner_and_tree (X : Mock.mock.Exec) :
    let result := run X trapDuringDrop
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 42) => true | _ => false),
      result.config.host.accepted.length, result.config.host.held.map receiptId) =
      (true, 1, [⟨0⟩]) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Examples
