module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Insert.Capacity

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- After a successful logical insert, the old table's usage increases by the
actual serialized cell length and its two-byte pointer. This determines exact
checked reopen and typed capacity failure for the resulting snapshot. -/
theorem insert_image_capacity {snapshot : Snapshot} {id amount : Int64}
    {edited : Edited} (inserted : snapshot.insert id amount = .ok edited) :
    let cells := snapshot.orderedRows.map fun row =>
      (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    let insertedCell := (⟨id, Record.Write.amount amount⟩ : BTree.LeafWrite.Cell).bytes
    let used := 8 + 2 * snapshot.orderedRows.length + cells.flatten.length + 2 + insertedCell.length
    ((∃ bytes, encode edited.snapshot = .ok bytes ∧ bytes.length = 1024 ∧
      TableLeaf.open? bytes = some edited.snapshot.readTable) ↔ used ≤ File.Write.pageSize) ∧
    (encode edited.snapshot = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < used) :=
  Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Insert.insert_image_capacity inserted

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
