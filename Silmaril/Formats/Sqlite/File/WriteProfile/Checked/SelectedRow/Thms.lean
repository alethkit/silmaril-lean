module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.SelectedRow.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- In a successful checked image, the parsed second page preserves the table
writer's bytes and selected pointer. Reading the original image at the resulting
absolute offset recovers the exact one-byte rowid, amount payload and typed row. -/
theorem Checked.encode_selected_row_physical {snapshot : Snapshot} {bytes : Bytes}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : Checked.encode snapshot = .ok bytes)
    (selected : snapshot.orderedRows[slot]? = some ⟨Int64.ofNat rowid, amount⟩) :
    let cells := snapshot.orderedRows.map
      (fun row => (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell))
    let serialized := cells.map BTree.LeafWrite.Cell.bytes
    let view := File.View.ofBytes bytes
    let offset := File.Write.pageSize - serialized.flatten.length + (serialized.take slot).flatten.length
    ∃ page, tablePage snapshot = .ok page ∧
      ∃ image, File.parse? bytes = some image ∧
      ∃ tableView, image.page? 2 = some tableView ∧
        tableView.materialize = Bytes.ofList page ∧
        tableView.be? (8 + 2 * slot) 2 = some offset ∧
        TableLeaf.cell? view (512 + offset) =
          some ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount),
            512 + offset, 512 + offset + 13⟩ ∧
        (TableLeaf.cell? view (512 + offset)).bind TableLeaf.row? =
          some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.checked_encode_selected_row_physical
    slot rowid small amount accepted selected

end Silmaril.Formats.Sqlite.WriteProfile.Image
