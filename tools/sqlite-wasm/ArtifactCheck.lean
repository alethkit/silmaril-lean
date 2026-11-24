module

public import SqliteWasm.Object
public import SqliteWasm.Original
public import SqliteWasmArtifactEntries

public section

namespace SqliteWasm

open Silmaril.Wasm SqliteWasmArtifact

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

sqlite_check_eq originalVersionExport :
    sourceExport? original "sqlite3_libversion_number" = some versionIndex

theorem quotedVersionExport :
    (sqlite.exports.find? (·.name == "sqlite3_libversion_number")).map Export.index =
      some (.func ⟨289⟩) := rfl

sqlite_check_eq originalVersionFunction :
    sourceFunction? original 289 = definedFunction? sqlite 289

sqlite_check_eq originalGetVarintFunction :
    sourceFunction? original 434 = definedFunction? sqlite 434

sqlite_check_eq originalPutVarintFunction :
    sourceFunction? original 530 = definedFunction? sqlite 530

theorem quotedFunctionsPresent :
    (definedFunction? sqlite 289).isSome ∧
    (definedFunction? sqlite 434).isSome ∧
    (definedFunction? sqlite 530).isSome :=
  ⟨rfl, rfl, rfl⟩

#print axioms quotedFunctionsPresent
#print axioms originalVersionExport
#print axioms quotedVersionExport
#print axioms originalVersionFunction
#print axioms originalGetVarintFunction
#print axioms originalPutVarintFunction

end SqliteWasm
