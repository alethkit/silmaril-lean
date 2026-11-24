module

public import SqliteWebWasm.Object
public import SqliteWebWasm.Original
public import SqliteWasmArtifactEntries

public section

namespace SqliteWebWasm

open Silmaril.Wasm SqliteWasmArtifact

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

sqlite_check_eq originalVersionExport :
    sourceExport? original "sqlite3_libversion_number" = some 483

theorem quotedVersionExport :
    (sqlite.exports.find? (·.name == "sqlite3_libversion_number")).map Export.index =
      some (.func ⟨483⟩) := rfl

sqlite_check_eq originalVersionFunction :
    sourceFunction? original 483 = definedFunction? sqlite 483

sqlite_check_eq originalStartIndex :
    sourceStart? original = some ⟨36⟩

theorem quotedStartIndex : sqlite.start = some ⟨36⟩ := rfl

sqlite_check_eq originalStartFunction :
    sourceFunction? original 36 = definedFunction? sqlite 36

theorem quotedFunctionsPresent :
    (definedFunction? sqlite 483).isSome ∧
    (definedFunction? sqlite 36).isSome :=
  ⟨rfl, rfl⟩

#print axioms quotedFunctionsPresent
#print axioms originalVersionExport
#print axioms quotedVersionExport
#print axioms originalVersionFunction
#print axioms originalStartIndex
#print axioms quotedStartIndex
#print axioms originalStartFunction

end SqliteWebWasm
