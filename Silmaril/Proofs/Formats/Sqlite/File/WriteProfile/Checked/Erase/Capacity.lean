module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Spec.Thms

public section

open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Erase

open WriteProfile

private def cellBytes (row : Row) : List UInt8 :=
  (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes

private def rowBytes (rows : List Row) : Nat :=
  8 + 2 * rows.length + (rows.flatMap cellBytes).length

private theorem rowBytes_perm {left right : List Row} (perm : left.Perm right) :
    rowBytes left = rowBytes right := by
  unfold rowBytes
  rw [perm.length_eq, (perm.flatMap_right cellBytes).length_eq]

private theorem rowBytes_erase {snapshot : Snapshot} {row : Row}
    (member : row ∈ snapshot.rows) :
    rowBytes (snapshot.erase row.id).snapshot.orderedRows + (2 + (cellBytes row).length) =
      rowBytes snapshot.orderedRows := by
  obtain ⟨earlier, later, rows⟩ := List.append_of_mem member
  have move : snapshot.rows.Perm (row :: (earlier ++ later)) := by
    rw [rows]
    exact List.perm_middle
  have keys := (move.map Row.id).nodup_iff.mp snapshot.unique
  have distinct : row.id ∉ (earlier ++ later).map Row.id := (List.nodup_cons.mp keys).1
  have rest : (earlier ++ later).filter (fun other => other.id != row.id) = earlier ++ later := by
    apply List.filter_eq_self.mpr
    intro other member
    apply bne_iff_ne.mpr
    intro same
    exact distinct (same ▸ List.mem_map_of_mem member)
  have erased := move.filter (fun other => other.id != row.id)
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, rest] at erased
  change (snapshot.erase row.id).snapshot.rows.Perm (earlier ++ later) at erased
  have oldSort : snapshot.orderedRows.Perm snapshot.rows := List.mergeSort_perm _ _
  have newSort : (snapshot.erase row.id).snapshot.orderedRows.Perm
      (snapshot.erase row.id).snapshot.rows := List.mergeSort_perm _ _
  rw [rowBytes_perm (newSort.trans erased), rowBytes_perm (oldSort.trans move)]
  simp only [rowBytes, List.length_cons, List.flatMap_cons, List.length_append]
  omega

theorem erase_image_capacity {snapshot : Snapshot} {row : Row}
    (member : row ∈ snapshot.rows) :
    let cells := snapshot.orderedRows.map fun item =>
      (⟨item.id, Record.Write.amount item.amount⟩ : BTree.LeafWrite.Cell).bytes
    let erasedCell := (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    let used := 8 + 2 * snapshot.orderedRows.length + cells.flatten.length - (2 + erasedCell.length)
    let after := (snapshot.erase row.id).snapshot
    ((∃ bytes, Image.Checked.encode after = .ok bytes ∧ bytes.length = 1024 ∧
      TableLeaf.open? bytes = some after.readTable) ↔ used ≤ File.Write.pageSize) ∧
    (Image.Checked.encode after = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < used) := by
  let after := (snapshot.erase row.id).snapshot
  have used := rowBytes_erase member
  have budget : rowBytes after.orderedRows =
      rowBytes snapshot.orderedRows - (2 + (cellBytes row).length) := by
    change rowBytes after.orderedRows + (2 + (cellBytes row).length) = _ at used
    omega
  have fits :
      (∃ bytes, Image.Checked.encode after = .ok bytes ∧ bytes.length = 1024 ∧
        TableLeaf.open? bytes = some after.readTable) ↔
        rowBytes after.orderedRows ≤ File.Write.pageSize :=
    Image.Checked.open_iff_fits after
  have full :
      Image.Checked.encode after = .error (.encode (.tablePage .pageFull)) ↔
        File.Write.pageSize < rowBytes after.orderedRows :=
    Image.Checked.encode_pageFull_iff after
  rw [budget] at fits full
  exact ⟨fits, full⟩

theorem erase_missing_image_eq (snapshot : Snapshot) (id : Int64) (missing : ¬ snapshot.has id) :
    Image.Checked.encode (snapshot.erase id).snapshot = Image.Checked.encode snapshot := by
  have rows : (snapshot.erase id).snapshot.rows = snapshot.rows := by
    apply List.filter_eq_self.mpr
    intro row member
    apply bne_iff_ne.mpr
    intro same
    exact missing (same ▸ List.mem_map_of_mem member)
  have same : (snapshot.erase id).snapshot = snapshot := by
    generalize (snapshot.erase id).snapshot = after at rows ⊢
    cases after
    cases snapshot
    cases rows
    rfl
  rw [same]

end Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Erase
