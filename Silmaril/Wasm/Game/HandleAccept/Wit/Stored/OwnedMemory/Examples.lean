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

private noncomputable def liftBoth : P Mock.mock World (Ret Mock.mock) := do
  let _ ← Builtins.resourceNew limits resource 77
  let _ ← Builtins.resourceNew limits resource 77
  let .ok tree ← buildNode signature limits Quirks.none context () (.memory 0) []
    | internal "ownership tree was not lifted"
  hostSet [tree]
  pure .unit

private noncomputable def initial (lastSlot : UInt8) : Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, data lastSlot⟩] }
    insts := [{}]
    resourceTypes := [{ impl := some ⟨0⟩ }]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) liftBoth]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock World (Ret Mock.mock) :=
  internal "unexpected call during owner lift"

private noncomputable def run (X : Mock.mock.Exec) (lastSlot : UInt8) :=
  Machine.run noReady noCalls X Machine.Oracle.first 224 (initial lastSlot)

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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Examples
