module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
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

private def childReply (byte : UInt8) : ByteArray :=
  ⟨#[8, 0, 0, 0, 1, 0, 0, 0, byte, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def replyPrefix (importIdx : Nat) (args : List Val) : Option ByteArray :=
  if importIdx = 0 && args == [.i32 7, .i32 0] then some vectorReply
  else if importIdx = 1 then
    if args == [.i32 41, .i32 0] then some (childReply 65)
    else if args == [.i32 323, .i32 0] then some (childReply 66)
    else if args == [.i32 5, .i32 0] then some (childReply 67)
    else none
  else none

private def replay : Nat → Config Nat → Option (List (Nat × List Val))
  | 0, config =>
    let final := (Exec.runI Silmaril.Wasm.Verify.refOracle 64 config).1
    if final.code.isEmpty then some [] else none
  | fuel + 1, config => do
    let (stopped, context, _, importIdx, args) ← runTo? 64 config
    let store := stopped.store
    let nextStore ← if importIdx = 2 && args == [.i32 7] then some store else do
      let replyBytes ← replyPrefix importIdx args
      let memory ← store.mems[0]?
      let bytes ← Execution.Memory.writeBytes memory.bytes 0 replyBytes
      some { store with mems := [{ memory with bytes }] }
    let rest ← replay fuel ⟨nextStore, stopped.frame, context.fill []⟩
    some ((importIdx, args) :: rest)

/-- Run the actual export with host replies that replace the whole vector prefix after each
child call. `scratch = none` uses the module's initialized memory page; the small scratch
memory is for kernel evaluation of the interpreter trace, not a specification instance. -/
def distinctChildrenReplay (scratch : Option ByteArray := none) : Option (List (Nat × List Val)) := do
  let (_, inst, _) ← Silmaril.Wasm.Verify.specInstance? (mod blobImports)
  let memory ← inst.store.mems[0]?
  let store := match scratch with
    | none => inst.store
    | some bytes => { inst.store with mems := [{ memory with bytes }] }
  replay 8 (invoke store 3 [.i32 7])

def distinctChildrenTrace : List (Nat × List Val) :=
  [(0, [.i32 7, .i32 0]), (1, [.i32 41, .i32 0]),
   (0, [.i32 7, .i32 0]), (1, [.i32 323, .i32 0]),
   (0, [.i32 7, .i32 0]), (1, [.i32 5, .i32 0]),
   (0, [.i32 7, .i32 0]), (2, [.i32 7])]

theorem visits_three_distinct_children_and_returns :
    distinctChildrenReplay (some vectorReply) = some distinctChildrenTrace := by decide +kernel

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Examples
