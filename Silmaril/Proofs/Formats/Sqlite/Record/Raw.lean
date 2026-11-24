module

public import Silmaril.Formats.Sqlite.Record.Raw.Defs
public import Silmaril.Formats.Sqlite.Record.Thms

public section

namespace Silmaril.Proofs.Formats.Sqlite.Record.Raw

open Silmaril.Formats Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Record

theorem Column.raw_blob (column : Column) (length : Nat)
    (code : column.code = 12 + 2*length) :
    column.rawValue? = some (.blob column.payload.materialize) := by
  simp only [Column.rawValue?, code, serialType_blob]

theorem Column.raw_integer (column : Column) (width : Nat)
    (kind : serialType column.code = .integer width) :
    column.rawValue? = (column.payload.be? 0 width).map
      (fun n => .integer (Int64.ofInt (File.signed width n))) := by
  simp only [Column.rawValue?, kind]
  cases column.payload.be? 0 width <;> rfl

theorem Column.raw_real (column : Column)
    (kind : serialType column.code = .real) :
    column.rawValue? = (column.payload.be? 0 8).map
      (fun n => .real (UInt64.ofNat n)) := by
  simp only [Column.rawValue?, kind]
  cases column.payload.be? 0 8 <;> rfl

end Silmaril.Proofs.Formats.Sqlite.Record.Raw
