module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Thms
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf.Reject

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Full page installation preserves the leaf-only rejection caused by a
missing or unsupported header tag in the selected view. -/
theorem parsed_nonleaf_full_fill_rejects (capacity : Nat) (file : FileState)
    (image : File.Image) (number : Nat) (view : File.View) (handle : Handle)
    (cache : Cache) (target : SlotId) {source : Silmaril.Formats.Bytes}
    (parsed : File.parse? source = some image)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false) (owned : cache target = some .vacant)
    (tag : view.get? (FileView.Admission.VdbeLeaf.btreeHeaderOffset number) ≠ some 13) :
    let page : Page := ⟨handle, number, image.header.pageSize⟩
    let base := FileView.Admission.VdbeLeaf.btreeHeaderOffset number
    ∃ bytes, fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      ∀ (db root : Nat) (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State),
        FileView.VdbeLeaf.run? (File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes))
            base db root program fuel initial = none ∧
          FileView.VdbeLeaf.run? view base db root program fuel initial = none :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf.parsed_nonleaf_full_fill_rejects capacity file image number view
    handle cache target parsed snapshot found live owned tag

end Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf
