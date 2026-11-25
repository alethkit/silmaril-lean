module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.SelectedRow.Read

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite

/-- The pointer in a successful layout selects the exact serialized cell.
The cell and row readers recover the typed row from its detached byte copy
at offset zero, for rowids from zero to 127 and every signed amount. -/
theorem layout_selected_row {leading page : List UInt8} {cells : List (List UInt8)}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : layout leading cells = .ok page)
    (found : cells[slot]? = some (Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩)) :
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    let body := Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      ∃ part, view.sub? offset body.length = some part ∧
        part.materialize = Bytes.ofList body ∧
        (TableLeaf.cell? (File.View.ofBytes part.materialize) 0).bind TableLeaf.row? =
          some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.SelectedRow.layout_selected_row
    slot rowid small amount accepted found

end Silmaril.Formats.Sqlite.BTree.LeafWrite
