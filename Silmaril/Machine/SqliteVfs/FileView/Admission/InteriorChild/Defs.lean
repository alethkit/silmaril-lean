module

public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Select one child from a 512-byte packed table-interior page with one
cell and no reserved, freeblock or fragmented bytes. The chosen pointer
must name a present and admitted page on the supplied handle.
See <https://sqlite.org/fileformat2.html#b_tree_pages>. -/
def selectChild? (image : File.Image) (handle : Handle) (root : Nat) (key : Int64)
    (bytes : Bytes) : Option Page :=
  match childNumber? with
  | none => none
  | some number =>
    if number == root || number == image.header.lockPage || image.header.isPointerMapPage number then
      none
    else
      match image.page? number with
      | none => none
      | some _ =>
        let page : Page := ⟨handle, number, image.header.pageSize⟩
        if page.Admitted then some page else none

where
  childNumber? : Option Nat := do
    let header := image.header
    let page := File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)
    let base := FileView.Admission.VdbeLeaf.btreeHeaderOffset root
    guard (page.length == 512 && header.pageSize == 512 && header.reserved == 0)
    guard (page.get? base == some 5 && page.be? (base + 3) 2 == some 1)
    guard (page.be? (base + 1) 2 == some 0 && page.get? (base + 7) == some 0)
    let content ← page.be? (base + 5) 2
    let cell ← page.be? (base + 12) 2
    guard (base + 14 ≤ content && cell == content)
    let left ← page.be? cell 4
    let right ← page.be? (base + 8) 4
    let (divider, stop) ← Varint.read? page (cell + 4)
    guard (stop == page.length && left != right)
    pure (if key.toInt ≤ File.signed 8 divider.toNat then left else right)

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild
