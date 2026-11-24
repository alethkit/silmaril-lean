module

public import Silmaril.Formats.Sqlite.File.Write.Defs
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Formats.Sqlite.IntTable.Defs

/-! Record encodings for one fixed schema and its integer data rows. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.Record.Write

/-- The INTEGER PRIMARY KEY alias is serialized as NULL. The amount always
uses serial type 6, an eight-byte signed big-endian integer. -/
def amount (value : Int64) : List UInt8 :=
  [3, 0, 6] ++ File.Write.be 8 value.toUInt64.toNat

@[simp] theorem amount_length (value : Int64) : (amount value).length = 11 := by
  simp [amount]

/-- The sole sqlite_schema record, with root page 2. The record-header length
includes its own one-byte varint. Each serial type uses SQLite's varint codec. -/
def schema : List UInt8 :=
  let kind := "table".toUTF8.data.toList
  let name := "sample".toUTF8.data.toList
  let sql := IntTable.schemaSql.toUTF8.data.toList
  let textCode := fun (length : Nat) => 13 + 2 * length
  let codes := [textCode kind.length, textCode name.length, textCode name.length, 1,
    textCode sql.length]
  let serials := codes.flatMap (fun code => (Varint.encode (UInt64.ofNat code)).toList)
  [UInt8.ofNat (serials.length + 1)] ++ serials ++ kind ++ name ++ name ++ [2] ++ sql

end Silmaril.Formats.Sqlite.Record.Write
