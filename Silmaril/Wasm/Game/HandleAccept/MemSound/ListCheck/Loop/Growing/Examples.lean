module

import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
import Silmaril.Wasm.SingleThreaded.Exec.Interp
import Silmaril.Wasm.Verify.Check.Defs
meta import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
meta import Silmaril.Wasm.SingleThreaded.Exec.Interp
meta import Silmaril.Wasm.Verify.Check.Defs

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Game.HandleAccept.MemSound.Text (bytesList)

/-- The second operand is the minimum page count, not a byte address. The signed
failure result from `memory.grow` is trapped before the first reader import. -/
private def reserve : List Instr :=
  [.localGet ⟨1⟩, .memorySize ⟨0⟩, .intRelOp .i32 (.gt .unsigned), .if_ .empty
    [.localGet ⟨1⟩, .memorySize ⟨0⟩, .intBinOp .i32 .sub, .memoryGrow ⟨0⟩,
      .intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq, .if_ .empty [.unreachable] []] [],
    .intConst .i32 0, .localSet ⟨1⟩]

private def module_ : Module :=
  { Loop.mod Checker.blobs.imports with funcs := [⟨⟨0⟩, [.i32, .i32], reserve ++ body⟩] }

private def beginCheck (store : Store Nat) (pages : BitVec 32) : Config Nat :=
  invoke store 3 [.i32 7, .i32 pages]

private def largeBytes : List UInt8 := List.replicate 65529 173

private def acceptingCall (oracle : GrowOracle) (store : Store Nat) : Except String (Store Nat) := do
  let mut active := beginCheck store 2
  for (expected, args) in [(0, [.i32 7, .i32 0]), (1, [.i32 41, .i32 0]),
      (0, [.i32 7, .i32 0]), (2, [.i32 7])] do
    let (paused, _) := Exec.runI oracle 128 active
    let some (context, _, actual, operands) := decompose? paused.store paused.code |
      throw s!"missing checker import {expected}"
    unless expected == actual && args == operands do throw "unexpected checker import or operands"
    let some memory := paused.store.mems[0]? | throw "missing grown memory"
    unless memory.pages == 2 do throw "checker reached import before reserving two pages"
    let next ← match expected with
      | 0 => (writeItemsReply memory.bytes [41]).mapError (fun _ => "items reply did not fit")
      | 1 => do
        let bytes ← (writeByteReply memory.bytes largeBytes).mapError (fun _ => "child reply did not fit")
        unless bytesList bytes 0 == some largeBytes do throw "the linked child decoder changed the blob"
        pure bytes
      | _ => do
        unless Execution.Memory.load memory.bytes 65536 1 == some 173 do
          throw "the items reread erased the final child byte"
        pure memory.bytes
    active := ⟨paused.store.setMem 0 { memory with bytes := next }, paused.frame, context.fill []⟩
  let (final, _) := Exec.runI oracle 128 active
  unless final.code.isEmpty do throw "checker did not return after accepting"
  pure final.store

private def regression : Except String Unit := do
  let some (_, instance_, _) := Verify.specInstance? module_ | throw "the growing checker did not validate"
  unless instance_.store.mems[0]?.map (·.pages) == some 1 do throw "expected one initial page"
  let allow : GrowOracle := fun _ _ _ _ => false
  let refuse : GrowOracle := fun _ _ _ _ => true
  let (failed, _) := Exec.runI refuse 128 (beginCheck instance_.store 2)
  match failed.code with
  | [.trap] => pure ()
  | _ => throw "growth refusal did not trap before the first import"
  unless failed.store.mems[0]?.map (·.bytes) == instance_.store.mems[0]?.map (·.bytes) do
    throw "growth refusal changed memory"
  let grown ← acceptingCall allow failed.store
  let (overflow, _) := Exec.runI allow 128 (beginCheck grown 65537)
  match overflow.code with
  | [.trap] => pure ()
  | _ => throw "request beyond memory32 did not trap"
  unless overflow.store.mems[0]?.map (·.bytes) == grown.mems[0]?.map (·.bytes) do
    throw "out-of-range growth changed memory"
  let _ ← acceptingCall refuse overflow.store

#eval show IO Unit from
  match regression with
  | .ok () => pure ()
  | .error issue => throw (IO.userError issue)

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Examples
