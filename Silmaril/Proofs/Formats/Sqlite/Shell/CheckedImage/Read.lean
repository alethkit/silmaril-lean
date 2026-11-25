module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms
public import Silmaril.Formats.Sqlite.Shell.Scan.CheckedImage.Thms
public import Silmaril.Formats.Sqlite.Shell.Seek.Snapshot.Thms

public section

open Silmaril.Formats
open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage

theorem execute_checked_query {snapshot : WriteProfile.Snapshot} {bytes : Bytes}
    (encoded : WriteProfile.Image.Checked.encode snapshot = .ok bytes) (query : Shell.Query) :
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
    (TableLeaf.open? bytes).map (fun table => Shell.execute table query) =
      some (.ok ⟨query.columns.map Shell.Column.name, projected⟩) := by
  cases selected : query.key with
  | none =>
    exact Shell.execute_checked_scan encoded query selected
  | some key =>
    rw [WriteProfile.Image.Checked.encode_eq_mapError] at encoded
    have raw : WriteProfile.Image.encode snapshot = .ok bytes := by
      cases h : WriteProfile.Image.encode snapshot <;> simp_all [Except.mapError]
    rw [WriteProfile.Image.encode_open_table raw]
    exact congrArg some (Shell.execute_seek_snapshot snapshot key query selected)

end Silmaril.Proofs.Formats.Sqlite.Shell.CheckedImage
