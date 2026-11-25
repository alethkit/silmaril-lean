module

public import Silmaril.Formats.Sqlite.Shell.Defs
public import Silmaril.Formats.Sqlite.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Scan.Read

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- An unfiltered scan returns the selected columns in signed rowid order
(or its reverse), with the offset and limit applied in that order. -/
theorem execute_scan_query (snapshot : WriteProfile.Snapshot) (query : Query)
    (unfiltered : query.key = none) :
    let ordered := if query.descending then snapshot.orderedRows.reverse else snapshot.orderedRows
    let selected := (ordered.drop query.offset).take (query.limit.getD ordered.length)
    execute snapshot.readTable query =
      .ok ⟨query.columns.map Column.name, selected.map fun row =>
        query.columns.map fun column => match column with
          | .id => row.id.toInt
          | .amount => row.amount.toInt⟩ :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Scan.execute_scan_query snapshot query unfiltered

/-- The ordinary two-column scan returns exactly the snapshot rows in their
signed rowid order. -/
theorem execute_scan (snapshot : WriteProfile.Snapshot) :
    execute snapshot.readTable { columns := [.id, .amount] } =
      .ok ⟨["id", "amount"], snapshot.orderedRows.map fun row => [row.id.toInt, row.amount.toInt]⟩ :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Scan.execute_scan snapshot

end Silmaril.Formats.Sqlite.Shell
