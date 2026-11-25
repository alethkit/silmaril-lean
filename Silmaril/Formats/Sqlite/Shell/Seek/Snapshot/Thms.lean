module

public import Silmaril.Formats.Sqlite.Shell.Defs
public import Silmaril.Formats.Sqlite.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Seek.Snapshot.Read

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- The executor's point-query result is the unique lookup in the snapshot's
source rows, followed by the requested projection, offset and limit. -/
theorem execute_seek_snapshot (snapshot : WriteProfile.Snapshot) (key : Int64) (query : Query)
    (selected : query.key = some key) :
    let projected := ((snapshot.rows.find? fun row => row.id == key).toList).map fun row =>
      query.columns.map fun column => match column with
        | .id => key.toInt
        | .amount => row.amount.toInt
    execute snapshot.readTable query =
      .ok ⟨query.columns.map Column.name, (projected.drop query.offset).take (query.limit.getD 1)⟩ :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Seek.Snapshot.execute_seek_snapshot snapshot key query selected

end Silmaril.Formats.Sqlite.Shell
