module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Parse.Read

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

/-- Successfully encoded raw bytes give the exact two-page, UTF-8 format-4
header to the ordinary file parser. -/
theorem encode_parse_image {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    File.parse? bytes = some ⟨bytes,
      { pageSize := 512, writeVersion := 1, readVersion := 1, reserved := 0,
        changeCounter := 1, rawPageCount := 2, freelistTrunk := 0, freelistCount := 0,
        schemaCookie := 1, schemaFormat := 4, cacheSize := 0, largestRoot := 0,
        encoding := .utf8, userVersion := 0, incrementalVacuum := false, applicationId := 0,
        versionValidFor := 1, sqliteVersion := 0 }, 2, 2⟩ :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse.encode_parse_image accepted

end Silmaril.Formats.Sqlite.WriteProfile.Image
