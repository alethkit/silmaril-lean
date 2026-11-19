module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Thms

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Examples

open Silmaril.Formats Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core

def signature : WitSig := ⟨Unit, fun _ => [.option (.own 7)], fun _ => .fixed 0⟩

noncomputable def contract : Contract signature Nat where
  code := 0
  name := ("wit", "node")
  tagOf := fun _ => some ()
  mode := {}
  node before op _ _ _ after :=
    let representation : Option Nat := op.2.1
    after = before + representation.getD 0
  other _ _ _ _ := False

def call (marker : UInt8) : UCall Nat :=
  ⟨0, { mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[1, 0, 0, 0, 1, 0, 0, 0, marker]⟩⟩] },
    [.i32 0, .i32 0, .i32 0, .i32 0]⟩

def before : State Nat := ⟨RT.single 1 7 77, 0⟩

def afterMove : State Nat := ⟨before.resources.killAll [1], 77⟩

theorem resolved_owner_reaches_writer :
    Answer contract (some 0) before (call 0) ⟨(call 0).store, .values [.i32 3]⟩ afterMove :=
  .returnHandle (op := (⟨(), (some (77 : Nat), ())⟩ : Op signature)) (children := [])
    rfl rfl ⟨rfl, rfl⟩ rfl

theorem retry_traps_with_later_memory_and_consumed_owner :
    Answer contract (some 0) afterMove (call 99) ⟨(call 99).store, .trap⟩ afterMove :=
  .reject (issue := .resource (.dead 1)) rfl rfl

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Examples
