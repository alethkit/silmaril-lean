module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Materialize.Thms
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell.Thms
import Silmaril.Formats.Sqlite.TableLeaf.Subview.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.ParentRow

open Silmaril.Formats Silmaril.Formats.Sqlite

theorem layout_selected_row_in_parent {leading page : List UInt8} {cells : List (List UInt8)}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : BTree.LeafWrite.layout leading cells = .ok page)
    (found : cells[slot]? = some (BTree.LeafWrite.Cell.bytes
      ⟨Int64.ofNat rowid, Record.Write.amount amount⟩)) :
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      TableLeaf.cell? view offset =
        some ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount), offset, offset + 13⟩ ∧
      (TableLeaf.cell? view offset).bind TableLeaf.row? =
        some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) := by
  let view := File.View.ofBytes (Bytes.ofList page)
  let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
  let body := BTree.LeafWrite.Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩
  let localCell : TableLeaf.Cell := ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount), 0, 13⟩
  obtain ⟨pointer, part, sliced, _, _, _, exactBytes⟩ :=
    BTree.LeafWrite.layout_pointer_materialize slot accepted found
  have isolated : TableLeaf.cell? (File.View.ofBytes (Bytes.ofList body)) 0 = some localCell :=
    BTree.LeafWrite.Cell.cell_roundtrip_small rowid small amount
  have copied : TableLeaf.cell? (File.View.ofBytes part.materialize) 0 = some localCell := by
    rw [exactBytes]
    exact isolated
  have direct := TableLeaf.cell?_materialized_shift view part offset body.length 0 sliced localCell copied
  rw [Nat.add_zero] at direct
  refine ⟨pointer, direct, ?_⟩
  have row := BTree.LeafWrite.Cell.row_roundtrip_small rowid small amount
  change (TableLeaf.cell? (File.View.ofBytes (Bytes.ofList body)) 0).bind TableLeaf.row? = _ at row
  rw [isolated] at row
  change (TableLeaf.cell? view offset).bind TableLeaf.row? = _
  rw [direct]
  exact row

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.ParentRow
