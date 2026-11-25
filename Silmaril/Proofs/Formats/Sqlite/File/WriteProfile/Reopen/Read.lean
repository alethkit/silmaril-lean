module

import Silmaril.Formats.Sqlite.File.WriteProfile.Catalogue.Thms
public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.File.WriteProfile.Parse.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.TablePage.Scan.Thms
import Silmaril.Formats.Sqlite.TableLeaf.Materialize.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile Silmaril.Formats.Sqlite.WriteProfile.Image

namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Reopen

/-- Successful raw encoding reopens with exactly the snapshot's ordered VM rows. -/
theorem encode_open_table {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    TableLeaf.open? bytes = some snapshot.readTable := by
  obtain ⟨image, parsed, catalogue, table, catalogueOk, tableOk, first, second,
    pageOne, _, _, _, firstBytes, pageTwo, _, _, _, secondBytes⟩ := encode_pages accepted
  obtain ⟨catalogueRead, schemaRecord⟩ := cataloguePage_read_schema catalogueOk
  have firstRead : TableLeaf.read? first 100 = some [⟨1, Bytes.ofList Record.Write.schema, 410, 512⟩] := by
    rw [← TableLeaf.read_materialized first 100, firstBytes]
    exact catalogueRead
  have secondRead : (TableLeaf.read? second 0).bind (List.mapM TableLeaf.row?) =
      some (snapshot.orderedRows.map Row.entry) := by
    rw [← TableLeaf.read_materialized second 0, secondBytes]
    exact tablePage_read_rows tableOk
  have imageEq := encode_parse_image accepted
  rw [parsed] at imageEq
  cases imageEq
  simp [TableLeaf.open?, parsed, pageOne, pageTwo, firstRead, schemaRecord,
    File.Header.autoVacuum, Snapshot.readTable, guard]
  rw [← Option.bind_assoc, secondRead]
  rfl

/-- The checked writer accepts those same emitted bytes. -/
private theorem checked_encode_of_encode {snapshot : Snapshot} {bytes : Bytes}
    (accepted : encode snapshot = .ok bytes) :
    Checked.encode snapshot = .ok bytes := by
  simp [Checked.encode, accepted, encode_open_table accepted]

/-- The checked encoder preserves every successful raw image and reports the
raw encoder's typed error when encoding fails. -/
theorem checked_encode_eq_mapError (snapshot : Snapshot) :
    Checked.encode snapshot = (encode snapshot).mapError Checked.Error.encode := by
  cases result : encode snapshot with
  | error error => simp [Checked.encode, result, Except.mapError]
  | ok bytes => rw [checked_encode_of_encode result]; rfl

end Silmaril.Proofs.Formats.Sqlite.WriteProfile.Image.Reopen
