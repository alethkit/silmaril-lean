module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit

/-- A live slot witness includes the arena identity, not just the legacy representation.
This is a view of the current table, not authority to use the slot again after a call. -/
def atSlot {E : CoreEngine} (store : CStore E) (inst : InstId) (slot : BitVec 32) :
    Option (HandleObjId × ResourceHandle) :=
  match (store.inst? inst).bind (fun state => state.handles.get? slot.toNat) with
  | some (.resource identity) => (store.resHandle? identity).map (identity, ·)
  | _ => none

/-- Legacy table observations erase the identity. Non-owning or lent entries are not
movable; the checked side can reject them without removing the reference entry. -/
def snapshot {E : CoreEngine} (store : CStore E) (inst : InstId) : RT :=
  fun slot => (atSlot store inst slot).map fun (_, handle) =>
    ⟨handle.rt.idx, handle.rep, handle.own && handle.numLends == 0⟩

/-- Match all usable representation-valued lookups. Dead legacy entries may persist
after a move even though the corresponding reference slot has been cleared. -/
def Matches {E : CoreEngine} (table : RT) (store : CStore E) (inst : InstId) : Prop :=
  ∀ resource slot, table.lookup resource slot = (snapshot store inst).lookup resource slot

/-- The typed witness available before a move. No table or arena effects occur here. -/
def ownerAt {E : CoreEngine} (store : CStore E) (inst : InstId) (resource : RtId)
    (slot : BitVec 32) : Option (Resources.Owned resource) := do
  let (identity, handle) ← atSlot store inst slot
  guard (handle.rt == resource && handle.own && handle.numLends == 0)
  return ⟨identity, handle.rep⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable
