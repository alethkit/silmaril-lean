module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

open Silmaril.Wasm.Component.Runtime

/-- Nominal identities introduced by published roots, newest first. Existing child trees are
references to earlier observations, so their receipts are not introduced again by the parent.
Representations, Core handles, and canonical guest table slots are not identities. -/
def State.publishedOwners {sig : Signature} (state : State sig) : List HandleObjId :=
  (state.accepted.flatMap rootReceipts).map receiptId

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
