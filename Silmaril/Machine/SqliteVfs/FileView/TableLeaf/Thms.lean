module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.TableLeaf.Decode

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.TableLeaf

open Silmaril.Formats.Sqlite.File (Image View)
open Silmaril.Formats.Sqlite

/-- A whole-view copy preserves the packed leaf parser, including rejection,
at every unchanged page-relative base. -/
theorem read_materialized (view : View) (base : Nat) :
    TableLeaf.read? (View.ofBytes view.materialize) base = TableLeaf.read? view base :=
  Proofs.Machine.SqliteVfs.FileView.TableLeaf.read_materialized view base

/-- Under the same-snapshot fill premises, the landed table-leaf reader sees
the same result from the installed bytes and the original shared page view. -/
theorem image_page_fill_decode (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (cache : PageRead.Cache) (target base : Nat)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, PageRead.fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      TableLeaf.read? (View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)) base =
        TableLeaf.read? view base :=
  Proofs.Machine.SqliteVfs.FileView.TableLeaf.image_page_fill_decode capacity file image number
    view handle cache target base snapshot found live range owned

end Silmaril.Machine.SqliteVfs.FileView.TableLeaf
