module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.ParentRow.Read

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite

/-- The pointer of a selected amount cell in a successful layout gives the
exact cell and typed row when read directly in the serialized page.
The rowid is in 0–127 and the amount can be any signed integer. -/
theorem layout_selected_row_in_parent {leading page : List UInt8} {cells : List (List UInt8)}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : layout leading cells = .ok page)
    (found : cells[slot]? = some (Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩)) :
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      TableLeaf.cell? view offset =
        some ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount), offset, offset + 13⟩ ∧
      (TableLeaf.cell? view offset).bind TableLeaf.row? =
        some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.ParentRow.layout_selected_row_in_parent
    slot rowid small amount accepted found

end Silmaril.Formats.Sqlite.BTree.LeafWrite
