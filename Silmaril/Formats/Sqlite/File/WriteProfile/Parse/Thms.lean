module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Parse.Read
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Parse.Pages

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

/-- The ordinary catalogue and table page lookups recover views of the exact
page bytes on successful raw encoding. Both views retain the original image. -/
theorem encode_pages {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    ∃ image, File.parse? bytes = some image ∧
      ∃ catalogue table, cataloguePage = .ok catalogue ∧ tablePage snapshot = .ok table ∧
        ∃ first second,
          image.page? 1 = some first ∧ first.source = bytes ∧ first.start = 0 ∧
          first.length = 512 ∧ first.materialize = Bytes.ofList catalogue ∧
          image.page? 2 = some second ∧ second.source = bytes ∧ second.start = 512 ∧
          second.length = 512 ∧ second.materialize = Bytes.ofList table :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Parse.encode_pages accepted

end Silmaril.Formats.Sqlite.WriteProfile.Image
