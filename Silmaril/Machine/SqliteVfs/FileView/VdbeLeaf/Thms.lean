module

public import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.VdbeLeaf.Run

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf

open Silmaril.Formats.Sqlite

theorem run_rejected_leaf (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) (reject : TableLeaf.read? view base = none) :
    run? view base db root program fuel initial = none :=
  Proofs.Machine.SqliteVfs.FileView.VdbeLeaf.run_rejected_leaf view base db root program fuel initial reject

theorem run_rejected_rows (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) (cells : List TableLeaf.Cell)
    (parsed : TableLeaf.read? view base = some cells) (reject : cells.mapM TableLeaf.row? = none) :
    run? view base db root program fuel initial = none :=
  Proofs.Machine.SqliteVfs.FileView.VdbeLeaf.run_rejected_rows view base db root program fuel initial
    cells parsed reject

/-- The same program and initial state have the same decode and run outcome
on the shared view and its whole-page copy. -/
theorem run_materialized (view : File.View) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) :
    run? (File.View.ofBytes view.materialize) base db root program fuel initial =
      run? view base db root program fuel initial :=
  Proofs.Machine.SqliteVfs.FileView.VdbeLeaf.run_materialized view base db root program fuel initial

/-- The bytes installed by one exact owned fill supply the same database and
hence the same VDBE result as the shared page for every program and fuel. -/
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
          run? view base db root program fuel initial :=
  Proofs.Machine.SqliteVfs.FileView.VdbeLeaf.image_page_fill_run capacity file image number
    view handle cache target base snapshot found live range owned

end Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf
