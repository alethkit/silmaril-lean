module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms
public import Silmaril.Formats.Sqlite.Shell.Scan.Thms

public section

open Silmaril.Formats
open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Scan.CheckedImage

theorem execute_checked_scan {snapshot : WriteProfile.Snapshot} {bytes : Bytes}
    (encoded : WriteProfile.Image.Checked.encode snapshot = .ok bytes)
    (query : Shell.Query) (unfiltered : query.key = none) :
    let ordered := if query.descending then snapshot.orderedRows.reverse else snapshot.orderedRows
    let selected := (ordered.drop query.offset).take (query.limit.getD ordered.length)
    (TableLeaf.open? bytes).map (fun table => Shell.execute table query) =
      some (.ok ⟨query.columns.map Shell.Column.name, selected.map fun row =>
        query.columns.map fun column => match column with
          | .id => row.id.toInt
          | .amount => row.amount.toInt⟩) := by
  rw [WriteProfile.Image.Checked.encode_eq_mapError] at encoded
  have raw : WriteProfile.Image.encode snapshot = .ok bytes := by
    cases h : WriteProfile.Image.encode snapshot <;> simp_all [Except.mapError]
  rw [WriteProfile.Image.encode_open_table raw]
  exact congrArg some (Shell.execute_scan_query snapshot query unfiltered)

end Silmaril.Proofs.Formats.Sqlite.Shell.Scan.CheckedImage
