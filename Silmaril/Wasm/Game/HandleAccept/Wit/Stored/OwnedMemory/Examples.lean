module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value

private def resource : RtId := ⟨0⟩

private def signature : Stored.Signature :=
  ⟨Unit, fun _ => .record [("items", .list (.own resource)), ("last", .option (.own resource))],
    fun _ => .fixed 0⟩

private abbrev World := List (OwnedMemory.Tree signature)

private def limits : Component.Limits := Component.Limits.spec

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0 }, inst := ⟨0⟩ }

private def data (lastSlot : UInt8) : ByteArray :=
  ⟨#[16, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, lastSlot, 0, 0, 0, 1, 0, 0, 0]⟩

private noncomputable def liftBoth (input : Input := .memory 0) : P Mock.mock World (Ret Mock.mock) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let .ok tree ← buildNode signature limits Quirks.none context () input []
    | internal "ownership tree was not lifted"
  hostSet [tree]
  pure .unit

private noncomputable def initial (lastSlot : UInt8)
    (input : Input := .memory 0) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, data lastSlot⟩] }
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (liftBoth input)]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock World (Ret Mock.mock) :=
  internal "unexpected call during owner lift"

private noncomputable def run (X : Mock.mock.Exec) (lastSlot : UInt8)
    (input : Input := .memory 0) :=
  Machine.run noReady noCalls X Machine.Oracle.first 224 (initial lastSlot input)

private noncomputable def observed : OwnedMemory.Tree signature → Observed
  | .atom impossible => impossible.elim
  | .tag payload _ _ => payload.2.val

private def receiptSummary (entry : Receipt) : HandleObjId × Nat :=
  (entry.2.identity, entry.2.representation)

theorem machine_session_sound (X : Mock.mock.Exec) (lastSlot : UInt8) :
    Machine.Steps .deterministic noReady noCalls (initial lastSlot)
      (run X lastSlot).labels (run X lastSlot).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 224 (initial lastSlot)

theorem nested_owners_with_equal_rep_keep_distinct_identities (X : Mock.mock.Exec) :
    let result := run X 2
    (result.outcome, result.config.host.map (fun tree =>
      let payload := observed tree
      (payload.value, payload.owners.map receiptSummary))) =
        (.resolved, [(.record [.list [.own 77], .variant 1 (some (.own 77))],
          [(⟨0⟩, 77), (⟨1⟩, 77)])]) := by
  dsimp only
  kernel_rfl

theorem double_move_traps_without_reversing_first_removal (X : Mock.mock.Exec) :
    let result := run X 1
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.isEmpty,
      (result.config.store.insts.get? 0).map (fun inst =>
        (inst.handles.get? 1, inst.handles.get? 2))) =
      (true, true, some (none, some (.resource ⟨1⟩))) := by
  dsimp only
  kernel_rfl

theorem inactive_borrow_rejected :
    checkSchema (.result (some (.own resource)) (some (.list (.borrow resource)))) =
      .error .storedBorrow := rfl

private def otherResource : RtId := ⟨1⟩

private def nominalPayloadType : TypeOf :=
  .record [("entries", .map .u8 (.own resource)),
    ("choice", .result (some (.own otherResource)) (some (.own resource)))]

private def nominalPayload : Val :=
  .record [.list [.record [.int .u8 3, .own 77]], .variant 0 (some (.own 77))]

private def nominalReceipts : List Receipt :=
  [⟨resource, ⟨⟨4⟩, 77⟩⟩, ⟨otherResource, ⟨⟨9⟩, 77⟩⟩]

theorem equal_rep_receipts_in_nominal_order_are_admitted :
    (checkValue nominalPayloadType ⟨nominalPayload, nominalReceipts⟩).isOk = true := by decide

theorem equal_rep_receipts_in_wrong_nominal_order_are_refused :
    (match checkValue nominalPayloadType ⟨nominalPayload, nominalReceipts.reverse⟩ with
      | .error .incompleteReceipts => true
      | _ => false) = true := by decide

private def flatInput (lastSlot : Nat) : Input :=
  .flat ([16, 1, 1, lastSlot].map i32Flat)

theorem flat_session_sound (X : Mock.mock.Exec) (lastSlot : Nat) :
    Machine.Steps .deterministic noReady noCalls (initial 0 (flatInput lastSlot))
      (run X 0 (flatInput lastSlot)).labels (run X 0 (flatInput lastSlot)).config :=
  Machine.run_sound noReady noCalls X Machine.Oracle.first 224 (initial 0 (flatInput lastSlot))

theorem flat_lift_preserves_direct_and_indirect_owners (X : Mock.mock.Exec) :
    let result := run X 0 (flatInput 2)
    (result.outcome, result.config.host.map (fun tree =>
      let payload := observed tree
      (payload.value, payload.owners.map receiptSummary))) =
        (.resolved, [(.record [.list [.own 77], .variant 1 (some (.own 77))],
          [(⟨0⟩, 77), (⟨1⟩, 77)])]) := by
  dsimp only
  kernel_rfl

theorem repeated_flat_slot_does_not_revive_an_indirect_move (X : Mock.mock.Exec) :
    let result := run X 0 (flatInput 1)
    (result.labels.any (fun label => match label with | .trap (.unknownHandle 1) => true | _ => false),
      result.config.host.isEmpty,
      (result.config.store.insts.get? 0).map (fun inst =>
        (inst.handles.get? 1, inst.handles.get? 2))) =
      (true, true, some (none, some (.resource ⟨1⟩))) := by
  dsimp only
  kernel_rfl

private noncomputable def rejectThenRetry : P Mock.mock World (Ret Mock.mock) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let invalid := Input.flat [i32Flat 16, i32Flat 1, i32Flat 0, .int .i64 2]
  let .error (.schema .flatTypes) ← buildNode signature limits Quirks.none context () invalid []
    | internal "an incompatible flat vector was not rejected before lifting"
  let .ok tree ← buildNode signature limits Quirks.none context () (flatInput 2) []
    | internal "the typed refusal did not leave both owners available"
  hostSet [tree]
  pure .unit

theorem malformed_inactive_slot_rejects_before_a_move_and_can_retry (X : Mock.mock.Exec) :
    let start := { initial 0 with ctl := [Machine.Activation.ofProg (some ⟨0⟩) rejectThenRetry] }
    let result := Machine.run noReady noCalls X Machine.Oracle.first 256 start
    (result.outcome, result.config.host.map (fun tree => (observed tree).owners.map receiptSummary)) =
      (.resolved, [[(⟨0⟩, 77), (⟨1⟩, 77)]]) := by
  dsimp only
  kernel_rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Examples
