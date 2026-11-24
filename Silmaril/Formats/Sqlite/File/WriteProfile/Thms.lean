module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

theorem leaf_length {leading bytes : List UInt8} {cells : List BTree.LeafWrite.Cell}
    (accepted : BTree.LeafWrite.encode leading cells = .ok bytes) : bytes.length = 512 :=
  Silmaril.Proofs.Formats.Sqlite.Image.leaf_length accepted

theorem encode_length {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) : bytes.length = 1024 :=
  Silmaril.Proofs.Formats.Sqlite.Image.image_length accepted

/-- A successful checked image has two pages and reopens with precisely the
ordered rows supplied to the read-only VM by the logical snapshot. -/
theorem Checked.encode_spec {snapshot : Snapshot} {bytes : Bytes}
    (accepted : Checked.encode snapshot = .ok bytes) :
    bytes.length = 1024 ∧ ∃ table, TableLeaf.open? bytes = some table ∧
      table.entries = snapshot.readTable.entries :=
  Silmaril.Proofs.Formats.Sqlite.Image.checked_spec accepted

end Silmaril.Formats.Sqlite.WriteProfile.Image
