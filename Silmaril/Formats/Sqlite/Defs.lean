module
public import Silmaril.Formats.Bytes

/-! SQLite storage-class values, a starting point for a future formalization.
This declares a carrier, not a database engine, record decoder, SQL semantics,
affinity/conversion rules, schema validation, or import/export behavior. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite

/-- SQLite's five storage classes. REAL is represented by its binary64 bits,
so this carrier does not silently identify signed zeros or interpret NaNs.
SQLite's conversion of NaN to NULL is an engine behavior to model separately. -/
inductive Value where
  | null
  | integer (value : Int64)
  | real (bits : UInt64)
  | text (value : String)
  | blob (value : Bytes)
  deriving DecidableEq
end Silmaril.Formats.Sqlite
