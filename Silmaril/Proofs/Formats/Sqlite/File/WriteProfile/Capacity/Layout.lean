module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Capacity

private def rowCell (row : Row) : BTree.LeafWrite.Cell :=
  ⟨row.id, Record.Write.amount row.amount⟩

private def serialized (snapshot : Snapshot) : List (List UInt8) :=
  snapshot.orderedRows.map fun row => (rowCell row).bytes

private theorem tablePage_layout (snapshot : Snapshot) :
    tablePage snapshot = BTree.LeafWrite.layout [] (serialized snapshot) := by
  simp [tablePage, BTree.LeafWrite.encode, serialized, rowCell, List.all_eq_true, File.Write.pageSize, Function.comp_def]

private def schemaCell : BTree.LeafWrite.Cell := ⟨1, Record.Write.schema⟩

set_option maxRecDepth 4096 in
private theorem catalogue_ok : ∃ page, cataloguePage = .ok page := by
  have schemaLength : Record.Write.schema.length = 100 := rfl
  have cellLength : schemaCell.bytes.length = 102 := rfl
  have page : BTree.LeafWrite.encode File.Write.header [schemaCell] =
      BTree.LeafWrite.layout File.Write.header [schemaCell.bytes] := by
    simp [BTree.LeafWrite.encode, schemaCell, schemaLength, File.Write.pageSize]
  change ∃ bytes, BTree.LeafWrite.encode File.Write.header [schemaCell] = .ok bytes
  rw [page]
  simp [BTree.LeafWrite.layout, cellLength, File.Write.header_length, File.Write.pageSize]

/-- The writer accepts exactly the snapshots whose physical cells and pointer
array fit in its single table page. -/
theorem encode_accepts_iff (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    (∃ bytes, encode snapshot = .ok bytes) ↔
      8 + 2 * snapshot.orderedRows.length + cells.flatten.length ≤ File.Write.pageSize := by
  change (∃ bytes, encode snapshot = .ok bytes) ↔
      8 + 2 * snapshot.orderedRows.length + (serialized snapshot).flatten.length ≤ File.Write.pageSize
  obtain ⟨_, schemaOk⟩ := catalogue_ok
  have cellCount : (serialized snapshot).length = snapshot.orderedRows.length := by simp [serialized]
  simp only [Image.encode, schemaOk, tablePage_layout, BTree.LeafWrite.layout, List.length_nil, Nat.zero_add, cellCount]
  by_cases fits : 8 + 2 * snapshot.orderedRows.length + (serialized snapshot).flatten.length ≤
      File.Write.pageSize
  · rw [ite_eq_left fits]
    simpa using fits
  · rw [ite_eq_right fits]
    simpa using Nat.lt_of_not_ge fits

/-- A table that exceeds the available bytes returns the precise pageFull error. -/
theorem encode_pageFull_iff (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    encode snapshot = .error (.tablePage .pageFull) ↔
      File.Write.pageSize < 8 + 2 * snapshot.orderedRows.length + cells.flatten.length := by
  change encode snapshot = .error (.tablePage .pageFull) ↔
      File.Write.pageSize < 8 + 2 * snapshot.orderedRows.length + (serialized snapshot).flatten.length
  obtain ⟨_, schemaOk⟩ := catalogue_ok
  have cellCount : (serialized snapshot).length = snapshot.orderedRows.length := by simp [serialized]
  simp only [Image.encode, schemaOk, tablePage_layout, BTree.LeafWrite.layout, List.length_nil, Nat.zero_add, cellCount]
  by_cases fits : 8 + 2 * snapshot.orderedRows.length + (serialized snapshot).flatten.length ≤
      File.Write.pageSize
  · rw [ite_eq_left fits]
    simpa using Nat.not_lt.mpr fits
  · rw [ite_eq_right fits]
    simpa using Nat.lt_of_not_ge fits

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Capacity
