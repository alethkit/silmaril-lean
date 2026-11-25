module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Machine.SqliteVfs.FileView.Admission.Thms
import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Thms

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs.PageRead

/-- The parsed geometry admits the read. The copied page and original view
give the same optional leaf decode and VDBE result at the file's header base. -/
theorem parsed_image_page_fill_run (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : Cache) (target : SlotId)
    {source : Silmaril.Formats.Bytes} (parsed : File.parse? source = some image)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false) (owned : cache target = some .vacant) :
    let page : Page := ⟨handle, number, image.header.pageSize⟩
    let base := btreeHeaderOffset number
    page.Admitted ∧
      ∃ bytes, fill (readOnly capacity) file cache target page =
        ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
        ∀ (db root : Nat) (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State),
          FileView.VdbeLeaf.run? (File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes))
              base db root program fuel initial =
            FileView.VdbeLeaf.run? view base db root program fuel initial := by
  have admitted := Admission.parsed_image_page_admitted handle parsed found
  exact ⟨admitted, FileView.VdbeLeaf.image_page_fill_run capacity file image number view handle
    cache target _ snapshot found live admitted.2 owned⟩

end Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf
