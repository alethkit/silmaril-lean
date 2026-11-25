module

public import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Machine.SqliteVfs.FileView.TableLeaf.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.VdbeLeaf

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf

theorem run_congr {a b : File.View} (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) (equal : TableLeaf.read? a base = TableLeaf.read? b base) :
    run? a base db root program fuel initial = run? b base db root program fuel initial := by
  unfold run? table?
  rw [equal]

theorem run_rejected_leaf (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) (reject : TableLeaf.read? view base = none) :
    run? view base db root program fuel initial = none := by
  unfold run? table?
  rw [reject]
  rfl

theorem run_rejected_rows (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) (cells : List TableLeaf.Cell)
    (parsed : TableLeaf.read? view base = some cells) (reject : cells.mapM TableLeaf.row? = none) :
    run? view base db root program fuel initial = none := by
  have noTable : table? view base = none := by
    unfold table?
    rw [parsed]
    change (cells.mapM TableLeaf.row?).bind (fun rows => some (BTree.Query.ReadModel.ofList rows)) = none
    rw [reject]
    rfl
  unfold run?
  rw [noTable]
  rfl

theorem run_materialized (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) :
    run? (File.View.ofBytes view.materialize) base db root program fuel initial =
      run? view base db root program fuel initial :=
  run_congr base db root program fuel initial (FileView.TableLeaf.read_materialized view base)

theorem image_page_fill_run (capacity : Nat) (file : FileState) (image : File.Image) (number : Nat)
    (view : File.View) (handle : Handle) (cache : PageRead.Cache) (target base : Nat)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, PageRead.fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      ∀ (db root : Nat) (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State),
        run? (File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)) base db root program fuel initial =
          run? view base db root program fuel initial := by
  obtain ⟨bytes, fill, decode⟩ :=
    FileView.TableLeaf.image_page_fill_decode capacity file image number view handle cache
      target base snapshot found live range owned
  exact ⟨bytes, fill, fun db root program fuel initial => run_congr base db root program fuel initial decode⟩

end Silmaril.Proofs.Machine.SqliteVfs.FileView.VdbeLeaf
