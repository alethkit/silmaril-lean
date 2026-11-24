module
public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Proofs.Formats.Sqlite.Record

public section
namespace Silmaril.Formats.Sqlite.Record

@[simp] theorem serialType_blob (length : Nat) : serialType (12 + 2*length) = .blob length := by
  unfold serialType
  split <;> simp_all <;> omega

@[simp] theorem serialType_text (length : Nat) : serialType (13 + 2*length) = .text length :=
  Silmaril.Proofs.Formats.Sqlite.Record.serialType_text length

/-- A raw record column's view never changes its storage-class code; decoding
does not reinterpret BLOB octets as text. -/
theorem Column.blob_value (column : Column) (encoding : File.TextEncoding) (length : Nat)
    (code : column.code = 12 + 2*length) :
    column.value? encoding = some (.blob column.payload.materialize) := by
  simp only [Column.value?, code, serialType_blob]

end Silmaril.Formats.Sqlite.Record
