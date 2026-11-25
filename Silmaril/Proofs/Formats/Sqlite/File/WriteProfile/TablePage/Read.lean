module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.ParentRow.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

private theorem encode_selected_row {leading page : List UInt8} {cells : List BTree.LeafWrite.Cell}
    (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (encoded : BTree.LeafWrite.encode leading cells = .ok page)
    (selected : cells[slot]? = some ⟨Int64.ofNat rowid, Record.Write.amount amount⟩) :
    let serialized := cells.map BTree.LeafWrite.Cell.bytes
    let view := File.View.ofBytes (Bytes.ofList page)
    let offset := File.Write.pageSize - serialized.flatten.length + (serialized.take slot).flatten.length
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      TableLeaf.cell? view offset =
        some ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount), offset, offset + 13⟩ ∧
      (TableLeaf.cell? view offset).bind TableLeaf.row? =
        some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) := by
  unfold BTree.LeafWrite.encode at encoded
  split at encoded
  · apply BTree.LeafWrite.layout_selected_row_in_parent slot rowid small amount encoded
    simp [selected]
  · cases encoded

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
        some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) := by
  change BTree.LeafWrite.encode [] _ = .ok page at accepted
  simpa using encode_selected_row slot rowid small amount accepted (by simp [selected])

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage
