module
public import Silmaril.Formats.Sqlite.Record.Defs

/-! SQLite storage values before Unicode validation. TEXT and BLOB both carry
their exact serialized bytes and retain distinct storage classes. SQLite can
store non-Unicode text, so structural record validity must not require a
successful projection to the String-based `Sqlite.Value` carrier. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.Record

inductive RawValue where
  | null
  | integer (value : Int64)
  | real (bits : UInt64)
  | text (bytes : Bytes)
  | blob (bytes : Bytes)
  deriving DecidableEq

/-- Optional semantic projection. TEXT is decoded strictly in the declared
database encoding; the other four storage classes require no Unicode check. -/
def RawValue.toValue? (encoding : File.TextEncoding) : RawValue → Option Value
  | .null => some .null
  | .integer value => some (.integer value)
  | .real bits => some (.real bits)
  | .text bytes => Value.text <$> decodeText? encoding (File.View.ofBytes bytes)
  | .blob bytes => some (.blob bytes)

/-- Lossless storage-class projection of one structurally parsed column.
INTEGER sign extension and REAL payload bits use the same decoding rules as
the existing Unicode projection. TEXT never performs character decoding. -/
def Column.rawValue? (column : Column) : Option RawValue :=
  match serialType column.code with
  | .null => some .null
  | .zero => some (.integer 0)
  | .one => some (.integer 1)
  | .integer width => do
    let n ← column.payload.be? 0 width
    pure (.integer (Int64.ofInt (File.signed width n)))
  | .real => do
    pure (.real (UInt64.ofNat (← column.payload.be? 0 8)))
  | .text _ => some (.text column.payload.materialize)
  | .blob _ => some (.blob column.payload.materialize)
  | .reserved _ => none

def Parsed.rawValues? (record : Parsed) : Option (Array RawValue) :=
  (record.columns.toList.mapM Column.rawValue?).map List.toArray

/-- Structural record decoding is independent of text encoding. Reserved
serial types, malformed headers and truncated payloads still fail. -/
def decodeRaw? (bytes : Bytes) : Option (Array RawValue) :=
  (parse? (File.View.ofBytes bytes)).bind Parsed.rawValues?

end Silmaril.Formats.Sqlite.Record
