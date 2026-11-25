module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Machine.SqliteVfs.FileView.Thms
import Silmaril.Formats.Sqlite.File.View.Materialize.Thms
import Silmaril.Formats.Sqlite.TableLeaf.Materialize.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.TableLeaf

open Silmaril.Formats.Sqlite.File (View Image)
open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs

theorem read_materialized (view : View) (base : Nat) :
    TableLeaf.read? (View.ofBytes view.materialize) base = TableLeaf.read? view base :=
  Silmaril.Formats.Sqlite.TableLeaf.read_materialized view base

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
        TableLeaf.read? view base := by
  obtain ⟨bytes, fill, length, read⟩ :=
    FileView.image_page_fill capacity file image number view handle cache target snapshot found
      live range owned
  refine ⟨bytes, fill, ?_⟩
  rw [View.ofList_eq_materialize view bytes length read]
  exact read_materialized view base

end Silmaril.Proofs.Machine.SqliteVfs.FileView.TableLeaf
