module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Publication.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication

open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

private theorem register_preserves {sig : Signature} {before after : State sig} {tree : OwnedMemory.Tree sig}
    (registered : before.register tree = .ok after) (unique : before.publishedOwners.Nodup) :
    after.publishedOwners.Nodup := by
  unfold State.register at registered
  dsimp only at registered
  split at registered
  next allowed =>
    cases registered
    simp only [State.publishedOwners, List.flatMap_cons, List.map_append]
    refine List.nodup_append.mpr ⟨allowed.1, unique, ?_⟩
    intro newOwner fresh oldOwner known same
    subst oldOwner
    have allKnown : newOwner ∈ ((before.accepted.flatMap rootReceipts ++ before.held).map receiptId) := by
      rw [List.map_append]
      exact List.mem_append_left _ known
    have noneKnown : ((rootReceipts tree).map receiptId).any
        (((before.accepted.flatMap rootReceipts ++ before.held).map receiptId).contains) = false := by
      simpa using allowed.2.1
    have absent := List.any_eq_false.mp noneKnown newOwner fresh
    rw [List.contains_iff_mem.mpr allKnown] at absent
    contradiction
  next => contradiction

theorem run_preserves {sig : Signature} {before after : State sig} (run : WriterRun before after)
    (unique : before.publishedOwners.Nodup) : after.publishedOwners.Nodup := by
  induction run with
  | refl => exact unique
  | cons step _ ih =>
    apply ih
    cases step with
    | same => exact unique
    | publish _ registered => exact register_preserves registered unique
    | spend update => cases update <;> exact unique

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication
