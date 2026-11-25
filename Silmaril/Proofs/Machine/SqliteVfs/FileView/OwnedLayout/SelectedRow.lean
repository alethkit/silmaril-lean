module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Formats.Sqlite.BTree.LeafWrite.SelectedRow.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.OwnedLayout

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.BTree
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private theorem read_placed (beforePage bytes afterPage : Silmaril.Machine.SqliteVfs.Bytes) :
    readBytes (beforePage ++ bytes ++ afterPage) beforePage.length bytes.length = bytes := by
  calc
    _ = List.ofFn (fun i : Fin bytes.length => bytes[i.val]) := by
      unfold readBytes
      congr 1
      funext index
      have inside : beforePage.length + index.val < (beforePage ++ bytes).length := by
        simp only [List.length_append]
        exact Nat.add_lt_add_left index.isLt _
      rw [List.getElem?_append_left inside,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        getElem?_pos bytes index.val index.isLt]
      rfl
    _ = bytes := List.ofFn_getElem

/-- Read one placed serialized leaf into an owned slot and recover the
selected typed row from the copied bytes. -/
theorem filled_layout_selected_row (capacity : Nat) (file : FileState) (cache : Cache)
    (target : SlotId) (page : Page) {leading serialized beforePage afterPage : List UInt8}
    {cells : List (List UInt8)} (slot rowid : Nat) (small : rowid < 128) (amount : Int64)
    (accepted : LeafWrite.layout leading cells = .ok serialized)
    (found : cells[slot]? = some (LeafWrite.Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩))
    (snapshot : file.bytes = beforePage ++ serialized ++ afterPage)
    (offset : page.offset = beforePage.length) (size : page.size = serialized.length)
    (admitted : page.Admitted) (live : (file.mode page.handle).isNone = false)
    (owned : cache target = some .vacant) :
    let outcome := fill (readOnly capacity) file cache target page
    let copy := File.View.ofBytes (Silmaril.Formats.Bytes.ofList serialized)
    let location := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    let body := LeafWrite.Cell.bytes ⟨Int64.ofNat rowid, Record.Write.amount amount⟩
    outcome = ⟨.ok serialized, file, cache.install target page serialized, [⟨page.request, .ok serialized⟩]⟩ ∧
      copy.be? (leading.length + 8 + 2 * slot) 2 = some location ∧
      ∃ selected, copy.sub? location body.length = some selected ∧
        selected.materialize = Silmaril.Formats.Bytes.ofList body ∧
        (TableLeaf.cell? (File.View.ofBytes selected.materialize) 0).bind TableLeaf.row? =
          some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) := by
  have complete : page.offset + page.size ≤ file.bytes.length := by
    simp [offset, size, snapshot]
  have filled := (ite_eq_left complete).mp
    (readOnly_fill capacity file cache target page owned admitted live)
  have exactBytes : readBytes file.bytes page.offset page.size = serialized := by
    rw [snapshot, offset, size]
    exact read_placed beforePage serialized afterPage
  rw [exactBytes] at filled
  exact ⟨filled, LeafWrite.layout_selected_row slot rowid small amount accepted found⟩

end Silmaril.Proofs.Machine.SqliteVfs.FileView.OwnedLayout
