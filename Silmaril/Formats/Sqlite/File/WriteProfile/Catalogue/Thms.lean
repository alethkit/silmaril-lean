module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.Record.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Catalogue.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- The ordinary leaf reader recovers the sole catalogue cell from a successful
catalogue page. The UTF-8 record decoder recovers all five exact fields. -/
theorem cataloguePage_read_schema {page : List UInt8} (accepted : cataloguePage = .ok page) :
    TableLeaf.read? (File.View.ofBytes (Bytes.ofList page)) 100 =
      some [⟨1, Bytes.ofList Record.Write.schema, 410, 512⟩] ∧
    Record.decode? .utf8 (Bytes.ofList Record.Write.schema) =
      some #[.text "table", .text "sample", .text "sample", .integer 2, .text IntTable.schemaSql] :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Catalogue.cataloguePage_read_schema accepted

end Silmaril.Formats.Sqlite.WriteProfile.Image
