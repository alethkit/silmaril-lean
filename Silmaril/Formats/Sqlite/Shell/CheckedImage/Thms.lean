module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
public import Silmaril.Formats.Sqlite.Shell.Defs
import Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage.Read

public section
namespace Silmaril.Formats.Sqlite.Shell

/-- The ordinary reader and executor give the specified scan or point result
on the unchanged bytes of a successful checked encoding. -/
theorem execute_checked_query {snapshot : WriteProfile.Snapshot} {bytes : Bytes}
    (encoded : WriteProfile.Image.Checked.encode snapshot = .ok bytes) (query : Query) :
    let projected := match query.key with
      | none =>
        let ordered := if query.descending then snapshot.orderedRows.reverse else snapshot.orderedRows
        let selected := (ordered.drop query.offset).take (query.limit.getD ordered.length)
        selected.map fun row => query.columns.map fun column => match column with
          | .id => row.id.toInt
          | .amount => row.amount.toInt
      | some key =>
        let found := ((snapshot.rows.find? fun row => row.id == key).toList).map fun row =>
          query.columns.map fun column => match column with
            | .id => key.toInt
            | .amount => row.amount.toInt
        (found.drop query.offset).take (query.limit.getD 1)
    (TableLeaf.open? bytes).map (fun table => execute table query) =
      some (.ok ⟨query.columns.map Column.name, projected⟩) :=
  Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage.execute_checked_query encoded query

end Silmaril.Formats.Sqlite.Shell
