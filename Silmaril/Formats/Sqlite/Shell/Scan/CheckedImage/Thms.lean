module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.Scan.CheckedImage.Compose

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- Opening a successfully encoded checked image and running an unfiltered
scan returns the selected ordered rows of the encoding input. -/
theorem execute_checked_scan {snapshot : WriteProfile.Snapshot} {bytes : Bytes}
    (encoded : WriteProfile.Image.Checked.encode snapshot = .ok bytes)
    (query : Query) (unfiltered : query.key = none) :
    let ordered := if query.descending then snapshot.orderedRows.reverse else snapshot.orderedRows
    let selected := (ordered.drop query.offset).take (query.limit.getD ordered.length)
    (TableLeaf.open? bytes).map (fun table => execute table query) =
      some (.ok ⟨query.columns.map Column.name, selected.map fun row =>
        query.columns.map fun column => match column with
          | .id => row.id.toInt
          | .amount => row.amount.toInt⟩) :=
  Silmaril.Proofs.Formats.Sqlite.Shell.Scan.CheckedImage.execute_checked_scan encoded query unfiltered

end Silmaril.Formats.Sqlite.Shell
