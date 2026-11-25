module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Spec.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- A checked image of exactly 1024 bytes reopens to the input table exactly
when the table-leaf header, pointer slots and serialized cells fit. -/
theorem open_iff_fits (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    (∃ bytes, encode snapshot = .ok bytes ∧ bytes.length = 1024 ∧
      TableLeaf.open? bytes = some snapshot.readTable) ↔
      8 + 2 * snapshot.orderedRows.length + cells.flatten.length ≤ File.Write.pageSize :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Spec.checked_open_iff_fits snapshot

/-- The checked writer returns its typed capacity error exactly when the
serialized table page would exceed its byte budget. -/
theorem encode_pageFull_iff (snapshot : Snapshot) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    encode snapshot = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < 8 + 2 * snapshot.orderedRows.length + cells.flatten.length :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Spec.checked_pageFull_iff snapshot

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
