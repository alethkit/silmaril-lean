module

public import SqliteWasm.BodyComposition
public import SqliteWasm.Original
public import SqliteWasm.Object
import SqliteWasm.LargeBody99
import SqliteWasm.LargeBody260
import SqliteWasm.LargeBody719
import SqliteWasm.LargeBody767

public section

namespace SqliteWasm

open SqliteWasmArtifact

/-- The Core decoder reads the complete original Code record at defined ordinal 99. -/
theorem originalCode99 : ReadsCodeAt original 99 (sqlite.funcs.map functionCode)[99]! :=
  LargeBody99.originalCode

/-- The Core decoder reads the complete original Code record at defined ordinal 260. -/
theorem originalCode260 : ReadsCodeAt original 260 (sqlite.funcs.map functionCode)[260]! :=
  LargeBody260.originalCode

/-- The Core decoder reads the complete original Code record at defined ordinal 719. -/
theorem originalCode719 : ReadsCodeAt original 719 (sqlite.funcs.map functionCode)[719]! :=
  LargeBody719.originalCode

/-- The Core decoder reads the complete original Code record at defined ordinal 767. -/
theorem originalCode767 : ReadsCodeAt original 767 (sqlite.funcs.map functionCode)[767]! :=
  LargeBody767.originalCode

end SqliteWasm
