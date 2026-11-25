module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Identifies.Compose

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- A successful checked image identifies the original typed snapshot rows
up to their source order. -/
theorem encode_eq_ok_iff_perm {left right : Snapshot} {bytes : Bytes}
    (encoded : encode left = .ok bytes) :
    encode right = .ok bytes ↔ left.rows.Perm right.rows :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Checked.Identifies.encode_eq_ok_iff_perm encoded

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
