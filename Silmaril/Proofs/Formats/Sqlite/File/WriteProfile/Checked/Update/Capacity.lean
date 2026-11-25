module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Spec.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Update

open WriteProfile

private def cellBytes (row : Row) : List UInt8 :=
  (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes

private def cellWidth (key : Int64) : Nat :=
  (cellBytes ⟨key, 0⟩).length

private theorem width_eq (row : Row) : (cellBytes row).length = cellWidth row.id := by
  simp [cellBytes, cellWidth, BTree.LeafWrite.Cell.bytes]

private def tableBytes (snapshot : Snapshot) : Nat :=
  8 + 2 * snapshot.orderedRows.length + (snapshot.orderedRows.map cellBytes).flatten.length

private theorem tableBytes_eq (snapshot : Snapshot) :
    tableBytes snapshot = 8 + 2 * snapshot.rows.length +
      ((snapshot.rows.map Row.id).map cellWidth).sum := by
  have sort : snapshot.orderedRows.Perm snapshot.rows := List.mergeSort_perm _ _
  have lengths (rows : List Row) :
      (rows.map cellBytes).flatten.length = (rows.map (cellWidth ∘ Row.id)).sum := by
    simp [List.map_map, Function.comp_def, width_eq]
  unfold tableBytes
  rw [sort.length_eq, lengths, List.map_map]
  exact congrArg (8 + 2 * snapshot.rows.length + ·)
    (sort.map (cellWidth ∘ Row.id)).sum_nat

private theorem update_ids {snapshot : Snapshot} {id : Int64} {amount : Option Int64}
    {edited : Edited} (updated : snapshot.update id amount = .ok edited) :
    edited.snapshot.rows.map Row.id = snapshot.rows.map Row.id := by
  simp only [Snapshot.update] at updated
  split at updated
  · cases amount with
    | none => cases updated
    | some amount =>
      cases updated
      simp [List.map_map, Function.comp_def]
  · cases updated
    rfl

theorem update_preserves_image_capacity {snapshot : Snapshot} {id : Int64}
    {amount : Option Int64} {edited : Edited} (updated : snapshot.update id amount = .ok edited) :
    ((∃ bytes, Image.Checked.encode snapshot = .ok bytes ∧ bytes.length = 1024 ∧
       TableLeaf.open? bytes = some snapshot.readTable) ↔
     (∃ bytes, Image.Checked.encode edited.snapshot = .ok bytes ∧ bytes.length = 1024 ∧
       TableLeaf.open? bytes = some edited.snapshot.readTable)) ∧
    (Image.Checked.encode snapshot = .error (.encode (.tablePage .pageFull)) ↔
     Image.Checked.encode edited.snapshot = .error (.encode (.tablePage .pageFull))) := by
  have ids := update_ids updated
  have count : edited.snapshot.rows.length = snapshot.rows.length := by
    simpa only [List.length_map] using congrArg List.length ids
  have same : tableBytes edited.snapshot = tableBytes snapshot := by
    rw [tableBytes_eq, tableBytes_eq, ids, count]
  have fits (state : Snapshot) :
      (∃ bytes, Image.Checked.encode state = .ok bytes ∧ bytes.length = 1024 ∧
        TableLeaf.open? bytes = some state.readTable) ↔ tableBytes state ≤ File.Write.pageSize :=
    Image.Checked.open_iff_fits state
  have full (state : Snapshot) :
      Image.Checked.encode state = .error (.encode (.tablePage .pageFull)) ↔
        File.Write.pageSize < tableBytes state :=
    Image.Checked.encode_pageFull_iff state
  rw [fits, fits, full, full, same]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Update
