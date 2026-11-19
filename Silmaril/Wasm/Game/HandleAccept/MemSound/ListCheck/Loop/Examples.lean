module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Thms
import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Verify.Check.Defs
import Silmaril.Wasm.Validation.Check.Validate

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList)
open Silmaril.Wasm.Resource (runTo?)

private def vectorReply : ByteArray :=
  ⟨#[8, 0, 0, 0, 3, 0, 0, 0, 41, 0, 0, 0, 67, 1, 0, 0, 5, 0, 0, 0]⟩

theorem symbol_checker_validates : (Silmaril.Wasm.Validation.validate? (mod {})).isSome := by
  decide +kernel

theorem blob_checker_validates : (Silmaril.Wasm.Validation.validate? (mod blobImports)).isSome := by
  decide +kernel

theorem final_word_fits : Addressable 4294967292 0 := by unfold Addressable; decide

theorem rejects_wrap_at_last_byte : ¬ Addressable 4294967293 0 := by unfold Addressable; decide

theorem rejects_wrap_in_offset : ¬ Addressable 0 1073741824 := by unfold Addressable; decide

theorem reads_three_distinct_words :
    itemsList vectorReply 0 = some [41, 323, 5] := by decide +kernel

private def childReply (size : Nat) (byte : UInt8) : ByteArray :=
  ⟨#[8, 0, 0, 0, 1, 0, 0, 0, byte]⟩ ++ ⟨Array.replicate (min size 20 - 9) 0⟩

private def replyMemory (handles : List (BitVec 32)) (children : List (BitVec 32 × UInt8))
    (importIdx : Nat) (args : List Val) (memory : ByteArray) : Option ByteArray :=
  if importIdx = 0 && args == [.i32 7, .i32 0] then (writeItemsReply memory handles).toOption
  else if importIdx = 1 then do
    let [.num ⟨.int .i32, handle⟩, retptr] := args | none
    if retptr != .i32 0 then none else do
      let byte ← children.lookup handle
      Execution.Memory.writeBytes memory 0 (childReply memory.size byte)
  else none

private def replay (handles : List (BitVec 32)) (children : List (BitVec 32 × UInt8)) :
    Nat → Config Nat → Option (List (Nat × List Val))
  | 0, config =>
    let final := (Exec.runI Silmaril.Wasm.Verify.refOracle 64 config).1
    if final.code.isEmpty then some [] else none
  | fuel + 1, config => do
    let (stopped, context, _, importIdx, args) ← runTo? 64 config
    let store := stopped.store
    let nextStore ← if importIdx = 2 && args == [.i32 7] then some store else do
      let memory ← store.mems[0]?
      let bytes ← replyMemory handles children importIdx args memory.bytes
      some { store with mems := [{ memory with bytes }] }
    let rest ← replay handles children fuel ⟨nextStore, stopped.frame, context.fill []⟩
    some ((importIdx, args) :: rest)

/-- Script a vector of any length that fits the guest memory, using the checked reply encoder
at each reread. `scratch = none` uses the module's initialized page; a replacement scratch
memory is only for small kernel regressions and is not a specification instance. -/
public def vectorReplay (handles : List (BitVec 32)) (children : List (BitVec 32 × UInt8))
    (scratch : Option ByteArray := none) :
    Option (List (Nat × List Val)) := do
  let (_, inst, _) ← Silmaril.Wasm.Verify.specInstance? (mod blobImports)
  let memory ← inst.store.mems[0]?
  let store := match scratch with
    | none => inst.store
    | some bytes => { inst.store with mems := [{ memory with bytes }] }
  replay handles children (2 * handles.length + 2) (invoke store 3 [.i32 7])

public def distinctChildrenReplay (scratch : Option ByteArray := none) :
    Option (List (Nat × List Val)) :=
  vectorReplay [41, 323, 5] [(41, 65), (323, 66), (5, 67)] scratch

public def distinctChildrenTrace : List (Nat × List Val) :=
  [(0, [.i32 7, .i32 0]), (1, [.i32 41, .i32 0]),
   (0, [.i32 7, .i32 0]), (1, [.i32 323, .i32 0]),
   (0, [.i32 7, .i32 0]), (1, [.i32 5, .i32 0]),
   (0, [.i32 7, .i32 0]), (2, [.i32 7])]

theorem visits_three_distinct_children_and_returns :
    distinctChildrenReplay (some vectorReply) = some distinctChildrenTrace := by decide +kernel

theorem calls_accept_for_empty_vector_without_child_calls :
    vectorReplay [] [] (some ⟨Array.replicate 8 0⟩) =
      some [(0, [.i32 7, .i32 0]), (2, [.i32 7])] := by decide +kernel

theorem visits_repeated_child_at_its_own_position :
    vectorReplay [41, 323, 5, 41] [(41, 65), (323, 66), (5, 67)]
        (some ⟨Array.replicate 24 0⟩) =
      some (distinctChildrenTrace.take 7 ++ [(1, [.i32 41, .i32 0]),
        (0, [.i32 7, .i32 0]), (2, [.i32 7])]) := by decide +kernel

theorem refuses_short_reply_memory :
    writeItemsReply ⟨Array.replicate 19 0⟩ [41, 323, 5] = .error .insufficientSpace := by
  apply rejects_short_memory <;> decide +kernel

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Examples
