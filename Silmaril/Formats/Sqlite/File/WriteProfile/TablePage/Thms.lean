module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.TablePage.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- A successful table-page write stores the selected ordered row at its
pointer. Direct parsing recovers the exact cell and typed row for rowids
0–127 and every signed amount. -/
theorem tablePage_selected_row {snapshot : Snapshot} {page : List UInt8}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : tablePage snapshot = .ok page)
    (selected : snapshot.orderedRows[slot]? = some ⟨Int64.ofNat rowid, amount⟩) :
    let cells := snapshot.orderedRows.map
      (fun row => (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell))
    let serialized := cells.map BTree.LeafWrite.Cell.bytes
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - serialized.flatten.length + (serialized.take slot).flatten.length
    view.be? (8 + 2 * slot) 2 = some offset ∧
      TableLeaf.cell? view offset =
        some ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount), offset, offset + 13⟩ ∧
      (TableLeaf.cell? view offset).bind TableLeaf.row? =
        some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.tablePage_selected_row
    slot rowid small amount accepted selected

end Silmaril.Formats.Sqlite.WriteProfile.Image
