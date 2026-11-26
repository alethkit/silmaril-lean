module

public import Silmaril.Machine.SQLite.GlobalState.Store.Thms
public import Silmaril.Machine.SQLite.GlobalState.StructThms
import Std.Data.ExtHashMap.Lemmas

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState.IndexedStore

/-- Add a caller-supplied live/zombie state to each present struct. The
existing kind store supplies the finite set of tagged keys. -/
def toObjects (store : IndexedStore) (state : TaggedId → PresentState) :
    Objects TaggedId ObjectFields :=
  Std.ExtHashMap.filterMap (fun id _ =>
    (store.lookup id.localId).map fun fields => ⟨id.kind, state id, fields⟩) store.erasePayloads

@[simp] theorem lookup_toObjects (store : IndexedStore) (state : TaggedId → PresentState)
    (id : TaggedId) : (store.toObjects state).lookup id =
    (store.lookup id.localId).map (fun fields => ⟨id.kind, state id, fields⟩) := by
  refine (Std.ExtHashMap.getElem?_filterMap' (m := store.erasePayloads)).trans ?_
  change (store.erasePayloads.lookup id).bind _ = _
  rw [store.lookup_erasePayloads id]
  cases store.lookup id.localId <;> rfl

@[simp] theorem toObjects_toKinds (store : IndexedStore) (state : TaggedId → PresentState) :
    (store.toObjects state).toKinds = store.erasePayloads := by
  apply ObjectStore.ext fun id => ?_
  rw [Objects.lookup_toKinds, lookup_toObjects, lookup_erasePayloads]
  cases store.lookup id.localId <;> rfl

/-- Dropping fields before dropping the live/zombie state gives the same
kind store as erasing the indexed structs directly. -/
theorem toObjects_toStates_toKinds (store : IndexedStore) (state : TaggedId → PresentState) :
    (store.toObjects state).toStates.toKinds = store.erasePayloads :=
  (Objects.toKinds_map (store.toObjects state) (fun _ _ => ())).trans (store.toObjects_toKinds state)

end Silmaril.Machine.SQLite.GlobalState.IndexedStore
