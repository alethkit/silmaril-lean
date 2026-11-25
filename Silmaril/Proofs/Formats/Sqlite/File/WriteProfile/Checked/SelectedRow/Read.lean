module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.TablePage.Thms
import Silmaril.Formats.Sqlite.TableLeaf.Subview.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image

private theorem encode_table_view {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    ∃ page, tablePage snapshot = .ok page ∧ ∃ view,
      (File.View.ofBytes bytes).sub? 512 512 = some view ∧
      view.materialize = Bytes.ofList page := by
  cases catalogueRead : cataloguePage with
  | error reason => simp [encode, catalogueRead] at accepted
  | ok catalogue =>
    cases rowsRead : tablePage snapshot with
    | error reason => simp [encode, catalogueRead, rowsRead] at accepted
    | ok rows =>
      have catalogueSize : catalogue.length = 512 := leaf_length catalogueRead
      have rowSize : rows.length = 512 := leaf_length rowsRead
      simp [encode, catalogueRead, rowsRead] at accepted
      subst bytes
      let source := Bytes.ofList (catalogue ++ rows)
      have full : source.length = 1024 := by simp [source, catalogueSize, rowSize]
      let view : File.View := ⟨source, 512, 512, by omega⟩
      refine ⟨rows, rfl, view, ?_, ?_⟩
      · change (File.View.ofBytes source).sub? 512 512 = some view
        simp [File.View.sub?, File.View.ofBytes, full, view]
      · apply congrArg Bytes.mk
        change (catalogue ++ rows).toByteArray.extract 512 (512 + 512) = rows.toByteArray
        rw [List.toByteArray_append]
        apply ByteArray.extract_append_eq_right
        · simp [catalogueSize]
        · simp [catalogueSize, rowSize]

private theorem materialize_length (view : File.View) : view.materialize.length = view.length := by
  have bounded : view.start + view.length ≤ view.source.data.size := view.bounded
  change (view.source.data.extract view.start (view.start + view.length)).size = view.length
  rw [ByteArray.size_extract, Nat.min_eq_left bounded, Nat.add_sub_cancel_left]

private theorem get?_materialize (view : File.View) (offset : Nat) :
    (File.View.ofBytes view.materialize).get? offset = view.get? offset := by
  by_cases inside : offset < view.length
  · have bounded : view.start + view.length ≤ view.source.data.size := view.bounded
    have backing : view.start + offset < view.source.data.size := by omega
    have extracted : offset < view.materialize.data.size := by
      change offset < view.materialize.length
      rwa [materialize_length]
    unfold File.View.get? File.View.ofBytes
    simp only [materialize_length, inside, ite_true, Nat.zero_add]
    rw [getElem?_pos view.materialize.data offset extracted,
        getElem?_pos view.source.data (view.start + offset) backing]
    exact congrArg some (ByteArray.getElem_extract extracted)
  · unfold File.View.get? File.View.ofBytes
    simp [materialize_length, inside]

private theorem be?_materialize (view : File.View) (offset width : Nat) :
    (File.View.ofBytes view.materialize).be? offset width = view.be? offset width := by
  simp only [File.View.be?, get?_materialize]

private theorem parsed_source {bytes : Bytes} {image : File.Image}
    (parsed : File.parse? bytes = some image) : image.source = bytes := by
  cases header : File.parseHeader? bytes with
  | none => simp [File.parse?, header] at parsed
  | some h =>
    simp [File.parse?, header] at parsed
    exact congrArg File.Image.source parsed.2.2.symm

private theorem open_root {bytes : Bytes} {table : BTree.Query.ReadModel Int (List Value)}
    (opened : TableLeaf.open? bytes = some table) :
    ∃ image, File.parse? bytes = some image ∧ image.pageCount = 2 ∧
      image.header.pageSize = 512 ∧ image.source = bytes := by
  cases parsed : File.parse? bytes with
  | none => simp [TableLeaf.open?, parsed] at opened
  | some image =>
    have shape : image.pageCount = 2 ∧ image.physicalPageCount = 2 ∧
        image.header.pageSize = 512 := by
      by_contra invalid
      have bad : ¬((image.pageCount = 2 ∧ image.physicalPageCount = 2) ∧
          image.header.pageSize = 512) := fun h => invalid ⟨h.1.1, h.1.2, h.2⟩
      simp [TableLeaf.open?, parsed, guard, bad] at opened
      contradiction
    exact ⟨image, rfl, shape.1, shape.2.2, parsed_source parsed⟩

private theorem checked_root_page {snapshot : Snapshot} {bytes : Bytes}
    (accepted : Checked.encode snapshot = .ok bytes) :
    ∃ image, File.parse? bytes = some image ∧
      image.page? 2 = (File.View.ofBytes bytes).sub? 512 512 := by
  obtain ⟨_, table, opened, _⟩ := Checked.encode_spec accepted
  obtain ⟨image, parsed, count, size, source⟩ := open_root opened
  exact ⟨image, parsed, by simp [File.Image.page?, count, size, source]⟩

/-- The native shell's checked encoder returns the same bytes as the raw writer. -/
private theorem checked_encode_raw {snapshot : Snapshot} {bytes : Bytes}
    (accepted : Checked.encode snapshot = .ok bytes) : encode snapshot = .ok bytes := by
  unfold Checked.encode at accepted
  split at accepted
  next => cases accepted
  next raw encoded =>
    split at accepted
    next => cases accepted
    next table read =>
      split at accepted
      next =>
        cases accepted
        exact encoded
      next => cases accepted

theorem checked_encode_selected_row_physical {snapshot : Snapshot} {bytes : Bytes}
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
          some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) := by
  let cells := snapshot.orderedRows.map
    (fun row => (⟨row.id, Record.Write.amount row.amount⟩ : BTree.LeafWrite.Cell))
  let serialized := cells.map BTree.LeafWrite.Cell.bytes
  let view := File.View.ofBytes bytes
  let offset := File.Write.pageSize - serialized.flatten.length + (serialized.take slot).flatten.length
  obtain ⟨page, pageRead, tableView, slice, exactPage⟩ :=
    encode_table_view (checked_encode_raw accepted)
  obtain ⟨pointer, cellRead, rowRead⟩ := tablePage_selected_row slot rowid small amount pageRead selected
  have tablePtr : tableView.be? (8 + 2 * slot) 2 = some offset := by
    rw [← be?_materialize, exactPage]
    exact pointer
  let cell : TableLeaf.Cell :=
    ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount), offset, offset + 13⟩
  have copied : TableLeaf.cell? (File.View.ofBytes tableView.materialize) offset = some cell := by
    rw [exactPage]
    exact cellRead
  have direct := TableLeaf.cell?_materialized_shift view tableView 512 512 offset slice cell copied
  have directResult : TableLeaf.cell? view (512 + offset) =
      some ⟨Int64.ofNat rowid, Bytes.ofList (Record.Write.amount amount),
        512 + offset, 512 + offset + 13⟩ := by
    simpa [cell, Nat.add_assoc] using direct
  obtain ⟨image, parsed, pageEq⟩ := checked_root_page accepted
  refine ⟨page, pageRead, image, parsed, tableView, pageEq.trans slice, exactPage,
    tablePtr, directResult, ?_⟩
  change (TableLeaf.cell? view (512 + offset)).bind TableLeaf.row? = _
  rw [directResult]
  rw [cellRead] at rowRead
  exact rowRead

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image
