module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Reopen.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- The ordinary reader opens a successful raw image as exactly the snapshot's
ordered table. -/
theorem encode_open_table {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    TableLeaf.open? bytes = some snapshot.readTable :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Reopen.encode_open_table accepted

/-- The checked encoder preserves the emitted bytes and maps raw encoder
failures to their typed checked errors. -/
theorem Checked.encode_eq_mapError (snapshot : Snapshot) :
    Checked.encode snapshot = (Image.encode snapshot).mapError Checked.Error.encode :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Reopen.checked_encode_eq_mapError snapshot

end Silmaril.Formats.Sqlite.WriteProfile.Image
