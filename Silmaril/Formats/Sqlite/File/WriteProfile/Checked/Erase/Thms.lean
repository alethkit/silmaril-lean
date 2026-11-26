module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Erase.Capacity

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- Erasing a present row frees its serialized cell and its two-byte pointer.
The new budget determines exact checked reopen and typed capacity failure. -/
theorem erase_image_capacity {snapshot : Snapshot} {row : Row}
    (member : row ∈ snapshot.rows) :
    let cells := snapshot.orderedRows.map fun item =>
      (⟨item.id, Record.Write.amount item.amount⟩ : BTree.LeafWrite.Cell).bytes
    let erasedCell := (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell).bytes
    let used := 8 + 2 * snapshot.orderedRows.length + cells.flatten.length - (2 + erasedCell.length)
    let after := (snapshot.erase row.id).snapshot
    ((∃ bytes, encode after = .ok bytes ∧ bytes.length = 1024 ∧
      TableLeaf.open? bytes = some after.readTable) ↔ used ≤ File.Write.pageSize) ∧
    (encode after = .error (.encode (.tablePage .pageFull)) ↔
      File.Write.pageSize < used) :=
  Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Erase.erase_image_capacity member

/-- Erasing an absent rowid preserves the entire checked encoder result. -/
theorem erase_missing_image_eq (snapshot : Snapshot) (id : Int64) (missing : ¬ snapshot.has id) :
    encode (snapshot.erase id).snapshot = encode snapshot :=
  Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Erase.erase_missing_image_eq
    snapshot id missing

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
