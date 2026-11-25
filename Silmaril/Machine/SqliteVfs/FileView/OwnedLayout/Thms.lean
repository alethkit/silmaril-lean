module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.OwnedLayout.SelectedRow

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.OwnedLayout

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.BTree
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

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
          some ((rowid : Int), [.integer (Int64.ofNat rowid), .integer amount]) :=
  Proofs.Machine.SqliteVfs.FileView.OwnedLayout.filled_layout_selected_row capacity file cache
    target page slot rowid small amount accepted found snapshot offset size admitted live owned

end Silmaril.Machine.SqliteVfs.FileView.OwnedLayout
