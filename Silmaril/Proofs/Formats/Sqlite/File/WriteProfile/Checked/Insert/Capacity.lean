module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Spec.Thms
import Silmaril.Formats.Sqlite.WriteProfile.Thms

public section

open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Insert

open WriteProfile

private def cellBytes (row : Row) : List UInt8 :=
  (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes

private def tableBytes (snapshot : Snapshot) : Nat :=
  8 + 2 * snapshot.orderedRows.length + (snapshot.orderedRows.flatMap cellBytes).length

private theorem tableBytes_eq (snapshot : Snapshot) :
    tableBytes snapshot = 8 + 2 * snapshot.rows.length + (snapshot.rows.flatMap cellBytes).length := by
  have sorted : snapshot.orderedRows.Perm snapshot.rows := List.mergeSort_perm _ _
  unfold tableBytes
  rw [sorted.length_eq, (sorted.flatMap_right cellBytes).length_eq]

private theorem tableBytes_insert {snapshot : Snapshot} {id amount : Int64}
    {edited : Edited} (inserted : snapshot.insert id amount = .ok edited) :
    tableBytes edited.snapshot = tableBytes snapshot + 2 + (cellBytes ⟨id, amount⟩).length := by
  have applied : snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited := by
    change snapshot.insert id amount = .ok edited
    exact inserted
  have rows := (insert_rows snapshot applied).1
  rw [tableBytes_eq edited.snapshot, tableBytes_eq snapshot, rows]
  simp only [List.length_cons, List.flatMap_cons, List.length_append]
  omega

theorem insert_image_capacity {snapshot : Snapshot} {id amount : Int64}
    {edited : Edited} (inserted : snapshot.insert id amount = .ok edited) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    let insertedCell := (⟨id, Record.Write.amount amount⟩ : BTree.LeafWrite.Cell).bytes
    let used := 8 + 2 * snapshot.orderedRows.length + cells.flatten.length + 2 + insertedCell.length
    ((∃ bytes, Image.Checked.encode edited.snapshot = .ok bytes ∧ bytes.length = 1024 ∧
      TableLeaf.open? bytes = some edited.snapshot.readTable) ↔ used ≤ File.Write.pageSize) ∧
    (Image.Checked.encode edited.snapshot = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < used) := by
  have fits :
      (∃ bytes, Image.Checked.encode edited.snapshot = .ok bytes ∧ bytes.length = 1024 ∧
        TableLeaf.open? bytes = some edited.snapshot.readTable) ↔
        tableBytes edited.snapshot ≤ File.Write.pageSize :=
    Image.Checked.open_iff_fits edited.snapshot
  have full :
      Image.Checked.encode edited.snapshot = .error (.encode (.tablePage .pageFull)) ↔
        File.Write.pageSize < tableBytes edited.snapshot :=
    Image.Checked.encode_pageFull_iff edited.snapshot
  rw [tableBytes_insert inserted] at fits full
  exact ⟨fits, full⟩

end Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Insert
