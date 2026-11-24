module

public import SqliteWasm.SectionRuns
public import SqliteWasm.Original
public import SqliteWasm.Object
import SqliteWasm.DataSectionEvidence

public section

namespace SqliteWasm

open SqliteWasmArtifact

/-- The original Data section reads both quoted segments and advances to byte 741717. -/
theorem originalDataSection :
    SectionRun original 11 683402 683406 58311 (fun s => { s with data := sqlite.data }) :=
  DataSectionEvidence.dataSection

end SqliteWasm
