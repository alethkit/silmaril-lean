module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.TablePage.Amount.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- In an accepted table page, the selected amount row's pointer locates its
exact cell and typed row for any signed key and amount. -/
theorem tablePage_selected_amount {snapshot : Snapshot} {page : List UInt8}
    (slot : Nat) (key amount : Int64)
    (accepted : tablePage snapshot = .ok page)
    (selected : snapshot.orderedRows[slot]? = some ⟨key, amount⟩) :
    let cells := snapshot.orderedRows.map
      (fun row => (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell))
    let serialized := cells.map BTree.LeafWrite.Cell.bytes
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - serialized.flatten.length + (serialized.take slot).flatten.length
    let extent := 1 + (Varint.encode key.toUInt64).toList.length + 11
    view.be? (8 + 2 * slot) 2 = some offset ∧
      TableLeaf.cell? view offset =
        some ⟨key, Bytes.ofList (Record.Write.amount amount), offset, offset + extent⟩ ∧
      (TableLeaf.cell? view offset).bind TableLeaf.row? =
        some (key.toInt, [.integer key, .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.Amount.tablePage_selected_amount
    slot key amount accepted selected

end Silmaril.Formats.Sqlite.WriteProfile.Image
