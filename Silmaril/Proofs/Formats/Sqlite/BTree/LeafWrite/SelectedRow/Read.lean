module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Materialize.Thms
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.SelectedRow

open Silmaril.Formats Silmaril.Formats.Sqlite

theorem layout_selected_row {leading page : List UInt8} {cells : List (List UInt8)}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : BTree.LeafWrite.layout leading cells = .ok page)
    (found : cells[slot]? = some (BTree.LeafWrite.Cell.bytes
      ⟨Int64.ofNat rowid, Record.Write.amount amount⟩)) :
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    let body := BTree.LeafWrite.Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      ∃ part, view.sub? offset body.length = some part ∧
        part.materialize = Bytes.ofList body ∧
        (TableLeaf.cell? (File.View.ofBytes part.materialize) 0).bind TableLeaf.row? =
          some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) := by
  obtain ⟨pointer, part, sliced, _, _, _, exactBytes⟩ :=
    BTree.LeafWrite.layout_pointer_materialize slot accepted found
  refine ⟨pointer, part, sliced, exactBytes, ?_⟩
  rw [exactBytes]
  exact BTree.LeafWrite.Cell.row_roundtrip_small rowid small amount

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.SelectedRow
