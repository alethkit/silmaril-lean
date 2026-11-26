module

public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Proofs.Formats.Sqlite.Record.Layout.Columns

public section
namespace Silmaril.Formats.Sqlite.Record

/-- A successful column read keeps the input code order, uses contiguous
shared payload views, and ends at the exact sum of the serial widths. -/
theorem columnsAux?_layout (source : File.View) (codes : List Nat) (offset : Nat)
    (inside : offset ≤ source.length) {columns : List Column} {next : Nat}
    (read : columnsAux? source codes offset = some (columns, next)) :
    columns.map Column.code = codes ∧
    next = offset + (codes.map fun code => (serialType code).width).sum ∧
    next ≤ source.length ∧
    ∀ slot column, columns[slot]? = some column →
      column.payload.source = source.source ∧
      column.payload.start = source.start + offset +
        ((codes.take slot).map fun code => (serialType code).width).sum ∧
      column.payload.length = (serialType column.code).width :=
  Silmaril.Proofs.Formats.Sqlite.Record.Layout.columnsAux?_layout source codes offset inside read

/-- When the serial widths overrun the admitted view, column reading fails
even if the shared backing bytes extend farther. -/
theorem columnsAux?_truncated (source : File.View) (codes : List Nat) (offset : Nat)
    (inside : offset ≤ source.length)
    (overrun : source.length < offset + (codes.map fun code => (serialType code).width).sum) :
    columnsAux? source codes offset = none :=
  Silmaril.Proofs.Formats.Sqlite.Record.Layout.columnsAux?_truncated source codes offset inside overrun

/-- A successfully parsed record uses the original shared source. Its header
and all column widths consume exactly the admitted view. -/
theorem parse?_layout {source : File.View} {record : Parsed}
    (parsed : parse? source = some record) :
    record.source = source ∧
    record.headerSize +
      (record.columns.toList.map fun column => (serialType column.code).width).sum = source.length ∧
    ∀ slot column, record.columns.toList[slot]? = some column →
      column.payload.source = source.source ∧
      column.payload.start = source.start + record.headerSize +
        ((record.columns.toList.take slot).map fun column => (serialType column.code).width).sum ∧
      column.payload.length = (serialType column.code).width :=
  Silmaril.Proofs.Formats.Sqlite.Record.Layout.parse?_layout parsed

end Silmaril.Formats.Sqlite.Record
