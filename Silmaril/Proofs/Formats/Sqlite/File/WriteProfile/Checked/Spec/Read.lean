module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Capacity.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Spec

/-- The physical bound characterizes when the checked writer emits a complete
1024-byte image that the ordinary reader opens as the exact input table. -/
theorem checked_open_iff_fits (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    (∃ bytes, Checked.encode snapshot = .ok bytes ∧ bytes.length = 1024 ∧
      TableLeaf.open? bytes = some snapshot.readTable) ↔
      8 + 2 * snapshot.orderedRows.length + cells.flatten.length ≤ File.Write.pageSize := by
  simp only
  constructor
  · rintro ⟨bytes, checked, _, _⟩
    apply (encode_accepts_iff snapshot).mp
    rw [Checked.encode_eq_mapError] at checked
    cases raw : Image.encode snapshot with
    | error error => simp [raw, Except.mapError] at checked
    | ok result => exact ⟨result, rfl⟩
  · intro fits
    obtain ⟨bytes, raw⟩ := (encode_accepts_iff snapshot).mpr fits
    refine ⟨bytes, ?_, encode_length raw, encode_open_table raw⟩
    rw [Checked.encode_eq_mapError, raw]
    rfl

/-- Exceeding that same bound is exactly the checked writer's typed error. -/
theorem checked_pageFull_iff (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    Checked.encode snapshot = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < 8 + 2 * snapshot.orderedRows.length + cells.flatten.length := by
  simp only
  have capacity := encode_pageFull_iff snapshot
  dsimp only at capacity
  rw [← capacity, Checked.encode_eq_mapError]
  cases Image.encode snapshot <;> simp [Except.mapError]

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Spec
