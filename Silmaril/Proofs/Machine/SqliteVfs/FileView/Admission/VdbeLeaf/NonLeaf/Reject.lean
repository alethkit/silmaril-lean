module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private theorem nonleaf_vdbe_rejects (view : File.View) (base db root : Nat)
    (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State)
    (tag : view.get? base ≠ some 13) :
    FileView.VdbeLeaf.run? view base db root program fuel initial = none := by
  have rejects : (view.get? base == some 13) = false := by
    simpa using tag
  have leaf : TableLeaf.read? view base = none := by
    simp [TableLeaf.read?, rejects, guard]
    rfl
  simp [FileView.VdbeLeaf.run?, FileView.VdbeLeaf.table?, leaf]

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
          FileView.VdbeLeaf.run? view base db root program fuel initial = none := by
  obtain ⟨_, bytes, installed, same⟩ :=
    FileView.Admission.VdbeLeaf.parsed_image_page_fill_run capacity file image number view handle
      cache target parsed snapshot found live owned
  refine ⟨bytes, installed, ?_⟩
  intro db root program fuel initial
  have rejected := nonleaf_vdbe_rejects view _ db root program fuel initial tag
  exact ⟨(same db root program fuel initial).trans rejected, rejected⟩

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.NonLeaf
