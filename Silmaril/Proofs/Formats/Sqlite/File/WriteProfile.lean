module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs

public section
namespace Silmaril.Proofs.Formats.Sqlite.Image

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

private theorem offsets_length (start : Nat) (cells : List (List UInt8)) :
    (BTree.LeafWrite.offsets start cells).length = cells.length := by
  induction cells generalizing start with
  | nil => rfl
  | cons cell tail ih => simp [BTree.LeafWrite.offsets, ih]

private theorem pointers_length (positions : List Nat) :
    (positions.flatMap (File.Write.be 2)).length = 2 * positions.length := by
  induction positions with
  | nil => rfl
  | cons position tail ih =>
    simp only [List.flatMap_cons, List.length_append, File.Write.be_length, ih, List.length_cons]
    omega

theorem layout_length {leading bytes : List UInt8} {cells : List (List UInt8)}
    (accepted : BTree.LeafWrite.layout leading cells = .ok bytes) : bytes.length = 512 := by
  simp only [BTree.LeafWrite.layout] at accepted
  split at accepted
  next fits =>
    cases accepted
    simp only [List.length_append, List.length_cons, List.length_nil, File.Write.be_length,
      pointers_length, offsets_length, List.length_replicate, File.Write.pageSize] at *
    omega
  next => cases accepted

theorem leaf_length {leading bytes : List UInt8} {cells : List BTree.LeafWrite.Cell}
    (accepted : BTree.LeafWrite.encode leading cells = .ok bytes) : bytes.length = 512 := by
  unfold BTree.LeafWrite.encode at accepted
  split at accepted
  · exact layout_length accepted
  · contradiction

theorem image_length {snapshot : Snapshot} {bytes : Silmaril.Formats.Bytes}
    (accepted : Image.encode snapshot = .ok bytes) : bytes.length = 1024 := by
  unfold Image.encode at accepted
  split at accepted
  next => cases accepted
  next => cases accepted
  next catalogue table hc ht =>
    cases accepted
    simp [leaf_length hc, leaf_length ht]

theorem checked_spec {snapshot : Snapshot} {bytes : Silmaril.Formats.Bytes}
    (accepted : Image.Checked.encode snapshot = .ok bytes) :
    bytes.length = 1024 ∧ ∃ table, TableLeaf.open? bytes = some table ∧
      table.entries = snapshot.readTable.entries := by
  unfold Image.Checked.encode at accepted
  split at accepted
  next => cases accepted
  next raw encoded =>
    split at accepted
    next => cases accepted
    next table read =>
      split at accepted
      next equal =>
        cases accepted
        exact ⟨image_length encoded, table, read, equal⟩
      next => cases accepted

end Silmaril.Proofs.Formats.Sqlite.Image
