module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Examples

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit

noncomputable section

private def resource : RtId := ⟨3⟩
private def context : LiftLowerContext Mock.mock := { opts := {}, inst := ⟨0⟩ }

private def store : CStore Mock.mock := { CStore.empty with
  insts := [({} : InstState).addHandle (.resource ⟨0⟩) |>.addHandle (.resource ⟨1⟩)]
  resHandles := List.replicate 2 { rt := resource, rep := 77, own := true } }

private def table : RT := snapshot store context.inst

private def sig : WitSig :=
  ⟨Unit, fun _ => [.record [("first", .option (.own 3)), ("rest", .list (.own 3))]], fun _ => .fixed 0⟩

private def input (second : UInt32) : Op (Nested.rawSignature sig) :=
  ⟨(), ((some (1 : UInt32), ([second], ())), ())⟩

private def removed (reference : CStore Mock.mock) (slot : Nat) : CStore Mock.mock :=
  ArenaField.insts.modify reference context.inst (InstState.removeHandle slot)

theorem nested_owner_commit :
    Commit Limits.spec context store [1, 2]
      [⟨resource, ⟨⟨0⟩, 77⟩⟩, ⟨resource, ⟨⟨1⟩, 77⟩⟩] (removed (removed store 1) 2) := by
  refine .cons (updated := removed store 1) ?_ ?_ (.cons ?_ ?_ (.nil _)) <;> kernel_rfl

theorem recursive_reservations_keep_the_two_slots :
    (Nested.reserveOp sig table (input 2)).map (·.2.val) = .ok [2, 1] := by
  kernel_rfl

theorem duplicate_rejected_before_commit :
    Nested.reserveOp sig table (input 1) = .error (.resource .duplicate) := by
  kernel_rfl

theorem eager_duplicate_keeps_the_first_removal :
    Stored.Endpoints.Core.runLocal (Resources.take Limits.spec context resource 1) (removed store 1) =
      (removed store 1, .error (.trapped (.unknownHandle 1))) := by
  kernel_rfl

end

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Examples
