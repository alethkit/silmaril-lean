module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
import Silmaril.Machine.SqliteVfs.FileView.Admission.Thms
import Silmaril.Machine.SqliteVfs.FileView.TableLeaf.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.Frontend

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open _root_.Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Silmaril.Machine.SqliteVfs.FileView.Admission.Frontend (query)

/-- The restricted frontend depends on the result of decoding the supplied leaf. -/
theorem query_eq_of_leaf_decode {left right : File.View} (base : Nat) (sql : String)
    (same : TableLeaf.read? left base = TableLeaf.read? right base) :
    query left base sql = query right base sql := by
  unfold query FileView.VdbeLeaf.table?
  rw [same]

/-- An owned fill of a page from a parsed image transports the complete
restricted frontend result at the page-relative b-tree header offset. -/
theorem parsed_image_page_fill_query (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : PageRead.Cache)
    (target : PageRead.SlotId)
    {source : Silmaril.Formats.Bytes} (parsed : File.parse? source = some image)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false) (owned : cache target = some .vacant) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    let base := btreeHeaderOffset number
    page.Admitted ∧
      ∃ bytes, PageRead.fill (readOnly capacity) file cache target page =
        ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
        ∀ sql, query (File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)) base sql =
          query view base sql := by
  have admitted := FileView.Admission.parsed_image_page_admitted handle parsed found
  obtain ⟨bytes, outcome, same⟩ :=
    FileView.TableLeaf.image_page_fill_decode capacity file image number view handle cache
      target (btreeHeaderOffset number) snapshot found live admitted.2 owned
  exact ⟨admitted, bytes, outcome, fun sql => query_eq_of_leaf_decode _ sql same⟩

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.Frontend
