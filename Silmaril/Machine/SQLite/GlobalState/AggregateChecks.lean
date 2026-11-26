module

import Silmaril.Machine.SQLite.GlobalState.All

namespace Silmaril.Machine.SQLite.GlobalState.AggregateChecks

private def vfs : LocalId .vfs := ⟨0⟩
private def fields : VfsFields := ⟨"fixture", 120, 512⟩
private def structs := IndexedStore.empty.insert vfs fields
private def objects := structs.toObjects (fun _ => .live)
private def kinds := objects.toStates.toKinds

private theorem hasVfs : kinds.HasKind vfs.tagged .vfs := by
  rw [ObjectStore.HasKind, kinds, objects, IndexedStore.toObjects_toStates_toKinds,
    IndexedStore.lookup_erasePayloads]
  rfl

private def registration : kinds.Ref .vfs := ⟨vfs.tagged, hasVfs⟩
private def roots : VfsRoots kinds := ⟨[registration], by simp⟩

-- The typed payload survives the bridge, and its state and payload erasure
-- supports the same VFS root at the original tag.
example : objects.lookup vfs.tagged = some ⟨.vfs, .live, fields⟩ := by
  rw [objects, IndexedStore.lookup_toObjects]
  rfl

example : roots.defaultVfs.map Subtype.val = some vfs.tagged := rfl

private def emptyHistory : History TaggedId ObjectFields := History.empty
private theorem freshVfs : emptyHistory.Fresh vfs.tagged := History.lookup_empty vfs.tagged

private def history := emptyHistory.allocate vfs.tagged .vfs fields freshVfs
private def raw : AllocationHistory TaggedId Nat Unit :=
  (∅ : AllocationHistory TaggedId Nat Unit).insert vfs.tagged (.live 128)
private def combined : AllocatorStore TaggedId TaggedId ObjectFields Nat Unit := ⟨history, raw⟩

private theorem present : combined.objectHistory.lookup vfs.tagged =
    some (.present ⟨.vfs, .live, fields⟩) :=
  emptyHistory.lookup_allocate_self vfs.tagged .vfs fields freshVfs

-- A raw token and the VFS can have the same underlying tagged value.
example : combined.lookup (.allocation vfs.tagged) = some (.allocation (.live 128)) := by
  simp [combined, AllocatorStore.lookup, raw]

example : combined.toObjects.lookupTagged (.object vfs.tagged : StoreId TaggedId TaggedId) =
    some ⟨.vfs, .live, fields⟩ := by
  simp [AllocatorStore.toObjects, Objects.lookupTagged, present, HistoryEntry.toObject]

example : (combined.lookup (.allocation vfs.tagged)).bind StoreEntry.toObject = none :=
  (combined.lookup_toObjects (.allocation vfs.tagged)).symm

example : combined.checkObjectId .vfs (.allocation vfs.tagged) = none :=
  combined.checkObjectId_allocation .vfs vfs.tagged

example (main : NamedMainFile) (number : Nat) {files : VFS.FileMap} {grant : Pager.LockGrant}
    {file : SqliteVfs.FileState} (live : main.opened.Live files file main.mode)
    (allowed : grant.Allows main.opened .readOnly) :
    Pager.ReadAccess files main.opened grant file (main.page number) :=
  main.readAccess number live allowed

end Silmaril.Machine.SQLite.GlobalState.AggregateChecks
