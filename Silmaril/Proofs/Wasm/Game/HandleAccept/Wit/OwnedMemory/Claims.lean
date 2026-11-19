module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims

open Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

theorem prepare_provenance {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    ∃ receipt ∈ state.held,
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation := by
  unfold State.prepare at success
  split at success
  · contradiction
  next receipt found =>
    split at success
    · contradiction
    next sameType =>
      cases success
      exact ⟨receipt, List.mem_of_find?_eq_some found, by simpa using List.find?_some found,
        by simpa using sameType, rfl⟩

theorem prepare_spends {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) :
    spent.accepted = state.accepted ∧
      ∀ receipt, receipt ∈ spent.held ↔ receipt ∈ state.held ∧ receiptId receipt ≠ id := by
  unfold State.prepare at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · cases success
      exact ⟨rfl, fun _ => by simp⟩

theorem prepare_no_repeat {sig : Signature} {state spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (success : state.prepare resource id = .ok (representation, spent)) (other : RtId) :
    spent.prepare other id = .error .unclaimed := by
  have missing : (spent.held.find? (fun entry => receiptId entry == id)) = none :=
    List.find?_eq_none.mpr fun receipt member => by
      have different := ((prepare_spends success).2 receipt |>.mp member).2
      simp [different]
  simp only [State.prepare, missing]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims
