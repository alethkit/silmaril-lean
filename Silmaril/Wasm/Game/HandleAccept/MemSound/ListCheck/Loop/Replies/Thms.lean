module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopReplies

public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList)

theorem rejects_oversized_memory {memory : ByteArray} {handles : List (BitVec 32)}
    (tooLarge : 2 ^ 32 < memory.size) : writeItemsReply memory handles = .error .oversizedMemory32 := by
  unfold writeItemsReply
  rw [ite_eq_left tooLarge]

theorem rejects_short_memory {memory : ByteArray} {handles : List (BitVec 32)}
    (width : memory.size ≤ 2 ^ 32) (short : memory.size < 8 + 4 * handles.length) :
    writeItemsReply memory handles = .error .insufficientSpace := by
  unfold writeItemsReply
  rw [ite_eq_right (Nat.not_lt.mpr width), ite_eq_left short]

/-- Every vector fitting this compact memory32 reply has an exact encoding, with the same
memory size and both of the checker's pointer guards satisfied at every child. -/
theorem writeItemsReply_roundtrip {memory : ByteArray} {handles : List (BitVec 32)}
    (width : memory.size ≤ 2 ^ 32) (space : 8 + 4 * handles.length ≤ memory.size) :
    ∃ updated, writeItemsReply memory handles = .ok updated ∧ updated.size = memory.size ∧
      itemsList updated 0 = some handles ∧
      ∀ index, index < handles.length → Addressable 8 (BitVec.ofNat 32 index) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopReplies.roundtrip width space

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
