module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Materialize.Thms
import Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell.Amount.Thms
import Silmaril.Formats.Sqlite.TableLeaf.Subview.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.Amount

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
        some (key.toInt, [.integer key, .integer amount]) := by
  let cells := snapshot.orderedRows.map
    (fun row => (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell))
  let serialized := cells.map BTree.LeafWrite.Cell.bytes
  let view := File.View.ofBytes (Bytes.ofList page)
  let offset := File.Write.pageSize - serialized.flatten.length + (serialized.take slot).flatten.length
  let extent := 1 + (Varint.encode key.toUInt64).toList.length + 11
  let body := BTree.LeafWrite.Cell.bytes ⟨key, Record.Write.amount amount⟩
  let localCell : TableLeaf.Cell := ⟨key, Bytes.ofList (Record.Write.amount amount), 0, extent⟩
  have laidOut : BTree.LeafWrite.layout [] serialized = .ok page := by
    change BTree.LeafWrite.encode [] cells = .ok page at accepted
    unfold BTree.LeafWrite.encode at accepted
    split at accepted
    · exact accepted
    · cases accepted
  have found : serialized[slot]? = some body := by
    simp [serialized, cells, body, selected]
  obtain ⟨pointer, part, sliced, _, _, _, exactBytes⟩ :=
    BTree.LeafWrite.layout_pointer_materialize slot laidOut found
  obtain ⟨isolated, row⟩ := BTree.LeafWrite.Cell.amount_roundtrip key amount
  change TableLeaf.cell? (File.View.ofBytes (Bytes.ofList body)) 0 = some localCell at isolated
  have copied : TableLeaf.cell? (File.View.ofBytes part.materialize) 0 = some localCell := by
    rw [exactBytes]
    exact isolated
  have direct := TableLeaf.cell?_materialized_shift view part offset body.length 0 sliced localCell copied
  rw [Nat.add_zero] at direct
  refine ⟨pointer, direct, ?_⟩
  change (TableLeaf.cell? (File.View.ofBytes (Bytes.ofList body)) 0).bind TableLeaf.row? = _ at row
  rw [isolated] at row
  change (TableLeaf.cell? view offset).bind TableLeaf.row? = _
  rw [direct]
  exact row

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.Amount
