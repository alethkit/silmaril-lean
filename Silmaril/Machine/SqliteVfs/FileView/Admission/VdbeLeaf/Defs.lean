module

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf

/-- The database header occupies the first 100 bytes of page one. -/
def btreeHeaderOffset (number : Nat) : Nat :=
  if number = 1 then 100 else 0

end Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf
