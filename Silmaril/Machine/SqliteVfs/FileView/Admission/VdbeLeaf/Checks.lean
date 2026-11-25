module

import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Thms
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs
meta import Silmaril.Formats.Sqlite.TableLeaf.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf

open Silmaril.Formats.Sqlite

example : btreeHeaderOffset 1 = 100 := rfl
example : btreeHeaderOffset 2 = 0 := rfl

-- Place the same small table leaf at two independently supplied offsets.
private def leaf (offset : Nat) : File.View :=
  File.View.ofBytes ⟨⟨Array.replicate offset 0 ++ #[13, 0, 0, 0, 1, 1, 250, 0, 1, 250] ++
    Array.replicate (496 - offset) 0 ++ #[4, 7, 3, 0, 1, 5]⟩⟩

#guard (FileView.VdbeLeaf.table? (leaf 100) (btreeHeaderOffset 1)).isSome
#guard (FileView.VdbeLeaf.table? (leaf 0) (btreeHeaderOffset 2)).isSome

#print axioms parsed_image_page_fill_run

end Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf
