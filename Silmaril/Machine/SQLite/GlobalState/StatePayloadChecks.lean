module

import Silmaril.Machine.SQLite.GlobalState.StatePayload

namespace Silmaril.Machine.SQLite.GlobalState.StatePayloadChecks

private def connection : LocalId .connection := ⟨0⟩
private def file : LocalId .file := ⟨0⟩
private def missing : LocalId .file := ⟨1⟩
private def dbFields : ConnectionFields := ⟨none, none, []⟩
private def fileFields : FileFields := ⟨some "main.db", some .readOnly⟩

private def structs : IndexedStore :=
  (IndexedStore.empty.insert connection dbFields).insert file fileFields

private def state (id : TaggedId) : PresentState :=
  if id = connection.tagged then .zombie else .live

example : (structs.toObjects state).lookup connection.tagged =
    some ⟨.connection, .zombie, dbFields⟩ := by
  rw [IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).lookup file.tagged = some ⟨.file, .live, fileFields⟩ := by
  rw [IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).lookup missing.tagged = none := by
  rw [IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).lookupLive connection.tagged = none := by
  rw [Objects.lookupLive, IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).toStates.lookup connection.tagged =
    some ⟨.connection, .zombie, ()⟩ := by
  rw [Objects.toStates, Objects.lookup_map, IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).toStates.toKinds.lookup connection.tagged = some .connection := by
  rw [IndexedStore.toObjects_toStates_toKinds, IndexedStore.lookup_erasePayloads]
  rfl

example : (structs.toObjects state).toStates.toKinds = structs.erasePayloads :=
  structs.toObjects_toStates_toKinds state

#print axioms IndexedStore.lookup_toObjects
#print axioms IndexedStore.toObjects_toKinds
#print axioms IndexedStore.toObjects_toStates_toKinds

end Silmaril.Machine.SQLite.GlobalState.StatePayloadChecks
