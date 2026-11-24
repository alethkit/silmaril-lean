module
public import Silmaril.Formats.Sqlite.Record.Raw.Defs
public import Silmaril.Formats.Sqlite.Record.Thms
import Silmaril.Proofs.Formats.Sqlite.Record.Raw

public section
namespace Silmaril.Formats.Sqlite.Record

theorem Column.raw_text (column : Column) (length : Nat)
    (code : column.code = 13 + 2*length) :
    column.rawValue? = some (.text column.payload.materialize) := by
  simp only [Column.rawValue?, code, serialType_text]

theorem Column.raw_blob (column : Column) (length : Nat)
    (code : column.code = 12 + 2*length) :
    column.rawValue? = some (.blob column.payload.materialize) :=
  Silmaril.Proofs.Formats.Sqlite.Record.Raw.Column.raw_blob column length code

/-- Raw INTEGER decoding preserves the exact signed value used by the
existing semantic projection; it has no encoding-dependent branch. -/
theorem Column.raw_integer (column : Column) (width : Nat)
    (kind : serialType column.code = .integer width) :
    column.rawValue? = (column.payload.be? 0 width).map
      (fun n => .integer (Int64.ofInt (File.signed width n))) :=
  Silmaril.Proofs.Formats.Sqlite.Record.Raw.Column.raw_integer column width kind

/-- All 64 REAL bits, including signed zeros and NaN payloads, survive. -/
theorem Column.raw_real (column : Column)
    (kind : serialType column.code = .real) :
    column.rawValue? = (column.payload.be? 0 8).map
      (fun n => .real (UInt64.ofNat n)) :=
  Silmaril.Proofs.Formats.Sqlite.Record.Raw.Column.raw_real column kind

/-- Projecting a raw INTEGER agrees with the existing exact decoder for
every encoding, without interpreting its payload as text. -/
theorem Column.raw_integer_projection (column : Column) (width : Nat)
    (encoding : File.TextEncoding) (kind : serialType column.code = .integer width) :
    column.rawValue?.bind (RawValue.toValue? encoding) = column.value? encoding := by
  simp only [Column.rawValue?, Column.value?, kind]
  cases column.payload.be? 0 width <;> rfl

theorem Column.raw_real_projection (column : Column)
    (encoding : File.TextEncoding) (kind : serialType column.code = .real) :
    column.rawValue?.bind (RawValue.toValue? encoding) = column.value? encoding := by
  simp only [Column.rawValue?, Column.value?, kind]
  cases column.payload.be? 0 8 <;> rfl

@[simp] theorem RawValue.integer_toValue? (encoding : File.TextEncoding) (value : Int64) :
    (RawValue.integer value).toValue? encoding = some (.integer value) := rfl

@[simp] theorem RawValue.real_toValue? (encoding : File.TextEncoding) (bits : UInt64) :
    (RawValue.real bits).toValue? encoding = some (.real bits) := rfl

@[simp] theorem RawValue.blob_toValue? (encoding : File.TextEncoding) (bytes : Bytes) :
    (RawValue.blob bytes).toValue? encoding = some (.blob bytes) := rfl

/-- Identical bytes in TEXT and BLOB remain different storage values. -/
theorem RawValue.text_ne_blob (text blob : Bytes) : RawValue.text text ≠ .blob blob := by
  intro same
  cases same

end Silmaril.Formats.Sqlite.Record
