module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.TablePage.Scan.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- The ordinary packed-leaf and row readers accept the successfully emitted
512-byte table page and recover the exact typed entries in signed rowid order. -/
theorem tablePage_read_rows {snapshot : Snapshot} {page : List UInt8}
    (accepted : tablePage snapshot = .ok page) :
    (TableLeaf.read? (File.View.ofBytes (Bytes.ofList page)) 0).bind (List.mapM TableLeaf.row?) =
      some (snapshot.orderedRows.map Row.entry) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.TablePage.Scan.tablePage_read_rows accepted

end Silmaril.Formats.Sqlite.WriteProfile.Image
