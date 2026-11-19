module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Game.HandleAccept.Wit

variable {E : CoreEngine}

/-- The legacy lookup is exactly erasure of the live owner witness, not its inverse. -/
theorem lookup_ownerAt (store : CStore E) (inst : InstId) (resource : RtId) (slot : BitVec 32) :
    (snapshot store inst).lookup resource.idx slot =
      (ownerAt store inst resource slot).map Resources.Owned.representation :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable.lookup_ownerAt store inst resource slot

/-- Atomic reservation and eager canonical removal agree on one successful leaf and
the resulting live lookup view after commit. The canonical result also records the
arena identity. This is a move-level refinement, not agreement on unsuccessful loads. -/
theorem reserve_refines_take (limits : Component.Limits) (cx : LiftLowerContext E) (store : CStore E)
    (table : RT) (resource : RtId) (slot : BitVec 32) (before after : Nested.Reservations) (rep : Nat)
    (matched : Matches table store cx.inst)
    (reserved : (Nested.reserve table resource.idx slot).run before = .ok (rep, after)) :
    ∃ owner : Resources.Owned resource,
      ownerAt store cx.inst resource slot = some owner ∧ owner.representation = rep ∧
      let updated := ArenaField.insts.modify store cx.inst (InstState.removeHandle slot.toNat)
      Stored.Endpoints.Core.runLocal (Resources.take limits cx resource slot.toNat) store = (updated, .ok owner) ∧
      Matches (table.killAll [slot]) updated cx.inst :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable.reserve_refines_take
    limits cx store table resource slot before after rep matched reserved

/-- Unlike the checked Core reservation, canonical lift removes a resource entry even
if its type, lending, or ownership checks fail. The local result is the store before
the reference machine's trap step applies lockdown. -/
theorem take_removes_first (limits : Component.Limits) (cx : LiftLowerContext E)
    (store : CStore E) (slot : BitVec 32) (resource : RtId) (instanceState : InstState)
    (identity : HandleObjId) (handle : ResourceHandle)
    (instanceGet : store.inst? cx.inst = some instanceState)
    (entryGet : instanceState.handles.get? slot.toNat = some (.resource identity))
    (objectGet : store.resHandle? identity = some handle) :
    Stored.Endpoints.Core.runLocal (Resources.take limits cx resource slot.toNat) store =
      (ArenaField.insts.modify store cx.inst (InstState.removeHandle slot.toNat),
        if handle.rt != resource then .error (.trapped .resourceTypeMismatch)
        else if handle.numLends != 0 then .error (.trapped .ownLent)
        else if !handle.own then .error (.trapped .notOwnHandle)
        else .ok ⟨identity, handle.rep⟩) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable.take_removes_first
    limits cx store slot resource instanceState identity handle instanceGet entryGet objectGet

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable
