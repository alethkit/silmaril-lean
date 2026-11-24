module

public import SqliteWasm.SectionRuns
public import SqliteWasm.Original
public import SqliteWasm.Object
import SqliteWasm.VectorEvidence

public section

namespace SqliteWasm

open SqliteWasmArtifact

/-- The original Type vector is the quotation's type list. -/
theorem originalTypeSection : SectionRun original 1 8 11 518 (fun s => { s with types := sqlite.types }) :=
  MetadataEvidence.typeSection

/-- The original Import vector is the quotation's import list. -/
theorem originalImportSection : SectionRun original 2 529 532 918 (fun s => { s with imports := sqlite.imports }) :=
  MetadataEvidence.importSection

/-- The original Export vector is the quotation's export list. -/
theorem originalExportSection : SectionRun original 7 3017 3020 180 (fun s => { s with exports := sqlite.exports }) :=
  MetadataEvidence.exportSection

end SqliteWasm
